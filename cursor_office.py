#!/usr/bin/env python3
"""
cursor_office.py - A tiny Game Boy-style "office" that visualizes your AI agents.

Each little person in the office is a chat/agent that was active in the last 24 hours,
read from the local transcript files on this machine. BOTH tools are shown together:

  * Cursor agents      (~/.cursor/projects/*/agent-transcripts/)
  * Claude Code agents (~/.claude/projects/*/)

Hover any worker to see which tool it belongs to (teal = Cursor, coral = Claude Code),
along with its live token/spend/model, its task, and the last instruction you sent it.

  * WORKING agents sit at a desk and type on their computer.
  * WAITING agents (finished a turn and waiting for your reply) hang out in the
    kitchen, make coffee and grab a snack.

Click a person to open an overlay with their task, latest thinking/response and the
last tool they used. From there you can open that chat's transcript file in Cursor or
copy the session id (to find it under "Previous Chats" in Cursor).

------------------------------------------------------------------------------------
HOW TO RUN  (no dependencies, just Python 3.8+)

    python3 cursor_office.py

Then open the URL it prints (default http://127.0.0.1:8787). It auto-opens a browser.

By default it shows agents from ALL your Cursor + Claude Code projects/roots on this
machine (each worker is tagged with its project). You can scope it to a single root, or
hide a whole source, if you prefer.

Useful flags:
    python3 cursor_office.py --hours 48        # widen the activity window
    python3 cursor_office.py --port 9000       # change port
    python3 cursor_office.py --project my-app  # only this root/project (substring match)
    python3 cursor_office.py --list-projects   # list roots with active sessions, then exit
    python3 cursor_office.py --no-cursor       # hide Cursor agents (Claude Code only)
    python3 cursor_office.py --no-claude       # hide Claude Code agents (Cursor only)
    python3 cursor_office.py --demo            # add fake workers so the office is lively
    python3 cursor_office.py --no-open         # don't auto-open the browser

------------------------------------------------------------------------------------
SHARING WITH YOUR TEAM

This is a single self-contained file. Drop it in a GitHub gist (or send the file) and
your teammates just run `python3 cursor_office.py`. It reads *their own* local Cursor
data from ~/.cursor/projects/*/agent-transcripts/ and Claude Code data from
~/.claude/projects/* -- nothing is uploaded anywhere and the server only listens on
localhost.
"""

import argparse
import json
import os
import re
import sys
import threading
import time
import webbrowser
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import quote, unquote, urlparse

# --------------------------------------------------------------------------------------
# Transcript discovery + parsing
# --------------------------------------------------------------------------------------

CURSOR_PROJECTS_DIR = os.path.expanduser("~/.cursor/projects")
# Claude Code stores one .jsonl per chat under ~/.claude/projects/<encoded-cwd>/,
# with any Task subagents in a sibling <session-uuid>/subagents/*.jsonl -- the same
# shape as Cursor, so both sources feed the SAME office (each worker is tagged with
# its `source` so the UI can tell a Cursor agent from a Claude Code agent).
CLAUDE_PROJECTS_DIR = os.path.expanduser("~/.claude/projects")

# Office (working/desk) vs kitchen (waiting) is decided by TURN STATE, not raw
# write-recency: a session is "working" while its latest turn is still IN PROGRESS
# (a user/assistant message after the last `turn_ended`). This keeps a genuinely
# busy chat at its desk even through long quiet stretches mid-turn -- a slow tool
# call, a long generation, or simply while you read -- which a write-recency window
# got wrong (it kept dropping active chats to "idle" during those gaps). A chat
# whose latest turn has ENDED is waiting on you, so it walks to the kitchen, picked
# up on the next poll. Two refinements layer on top:
#   * Multitask rollup: if the parent's turn has ended but a background SUBAGENT was
#     written within SUBAGENT_ACTIVE_SECONDS, the chat still counts as working
#     (the Multitask Mode case, where the parent is idle while a worker runs).
#   * Staleness cap: a turn that has been completely silent (chat AND subagents)
#     for longer than WORKING_STALE_CAP_SECONDS is treated as abandoned/crashed and
#     sent to the kitchen, so a half-finished turn can't sit at a desk forever.
SUBAGENT_ACTIVE_SECONDS = 120    # multitask subagent freshness window; --active-secs
# Backstop only: a turn still "in progress" but completely silent this long is
# treated as abandoned/crashed -> kitchen. Kept FAR out (2h) on purpose: the
# transcript .jsonl records only user/assistant messages, NOT tool calls, so a
# busy tool-heavy turn can legitimately write nothing for many minutes. A short
# cap (e.g. 15m) wrongly evicted those active turns to the kitchen, so turn state
# -- not mtime -- is the primary signal and this only catches genuinely dead ones.
WORKING_STALE_CAP_SECONDS = 7200
# A turn that owes the user a PLAIN reply (last event is a real user message, no tool pending)
# but has produced nothing for this long is stuck/abandoned -- e.g. an interrupted request the
# user never continued. A real agent starts replying within seconds, so this is safe to keep
# short WITHOUT evicting long single-tool turns (those are "mid-tool", not "reply", so exempt).
REPLY_STALE_SECONDS = 600

# --watch (dev hot-reload). START_TOKEN changes every time the process (re-)starts;
# the page polls /api/version and reloads itself when it sees a new token. Set from
# the pid + import time so a re-exec after a file change produces a fresh value.
START_TOKEN = str(os.getpid()) + "-" + str(int(os.stat(__file__).st_mtime))
WATCH_MODE = False

# Dynamic Workflow (the Workflow tool) tents. A workflow run's tent is shown while it
# is running, and lingers this long after its last write before it closes (a finished
# workflow's full summary always stays in the chat's detail panel).
SHOW_WORKFLOWS = True
WORKFLOW_FRESH_SECONDS = 300
_WORKFLOW_SCRIPT_CACHE = {}     # script_path -> (mtime, meta_dict)
_WORKFLOW_IDENTITY_CACHE = {}   # uuid -> (parent_mtime, {runId: {name,summary,scriptPath}})
_WORKFLOW_JOURNAL_CACHE = {}    # run_dir -> ((mtime,size), {total,done,running_ids})

# rough per-1M-token pricing (USD) by model family, for a best-effort $ spend estimate.
_MODEL_PRICING = {  # (input, output); cache-read ~= 0.1x input, cache-write ~= 1.25x input
    "opus": (15.0, 75.0),
    "sonnet": (3.0, 15.0),
    "haiku": (0.80, 4.0),
}

TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"[ \t]+")
# leading "Thursday, Jun 25, 2026, 1:26 PM (UTC+3)" style timestamp lines
TS_LINE_RE = re.compile(
    r"^(mon|tue|wed|thu|fri|sat|sun)[a-z]*,.*\(utc.*\)\s*$", re.IGNORECASE
)

# Deterministic fun names so each agent feels like an office worker.
FIRST_NAMES = [
    "Pip", "Willow", "Clover", "Bun", "Maple", "Sprout", "Waffle", "Biscuit",
    "Poppy", "Mochi", "Pebble", "Fern", "Cricket", "Marshmallow", "Pumpkin",
    "Honey", "Acorn", "Noodle", "Pickle", "Sunny", "Berry", "Tofu", "Dandelion",
    "Bramble", "Hazel", "Olive", "Tansy", "Muffin", "Peaches", "Juniper",
]
LAST_NAMES = [
    "Sunbeam", "Marshmallow", "Buttercup", "Honeydew", "Pumpkinpatch",
    "Snugglebee", "Cloudberry", "Dewdrop", "Meadowlight", "Gigglesworth",
    "Cottontail", "Brightbloom", "Mossypaws", "Tinkerwhisk", "Sugarplum",
    "Pebblebrook", "Willowwisp", "Honeycomb", "Berrybramble", "Twinkletoes",
    "Mapleshade", "Cuddleburrow", "Dapplewood", "Snickerdoodle", "Fernwhistle",
]


def _clean_text(s):
    if not s:
        return ""
    s = TAG_RE.sub(" ", s)
    s = s.replace("\\n", "\n")
    # collapse runs of spaces/tabs but keep newlines
    lines = [WS_RE.sub(" ", ln).strip() for ln in s.split("\n")]
    out = "\n".join(ln for ln in lines)
    out = re.sub(r"\n{3,}", "\n\n", out).strip()
    return out


def _strip_leading_timestamp(s):
    """Drop leading blank/timestamp lines so the real query shows up first."""
    lines = (s or "").split("\n")
    while lines and (not lines[0].strip() or TS_LINE_RE.match(lines[0].strip())):
        lines.pop(0)
    return "\n".join(lines).strip()


def _name_for(uuid):
    h = 0
    for ch in uuid:
        h = (h * 131 + ord(ch)) & 0xFFFFFFFF
    first = FIRST_NAMES[h % len(FIRST_NAMES)]
    last = LAST_NAMES[(h // len(FIRST_NAMES)) % len(LAST_NAMES)]
    return f"{first} {last}"


def _variant_for(uuid):
    h = 0
    for ch in uuid:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return h % 6


def _pretty_project(folder):
    name = folder
    if name.startswith("Users-"):
        parts = name.split("-")
        # keep the last 2 meaningful segments, e.g. ...-my-app -> "my-app"
        if len(parts) >= 2:
            name = "-".join(parts[-2:])
    return name


def _tool_detail(name, inp):
    # Tolerant of both Cursor and Claude Code tool schemas (e.g. Cursor's Shell /
    # StrReplace / `path` vs Claude's Bash / Edit / `file_path`).
    if not isinstance(inp, dict):
        return name
    def first_line(v):
        return _clean_text(str(v)).split("\n")[0][:80]
    def basename_of(*keys):
        for k in keys:
            v = inp.get(k)
            if v:
                return os.path.basename(v) or v
        return ""
    if name in ("Shell", "Bash"):
        return first_line(inp.get("description") or inp.get("command") or "")
    if name in ("Read", "Write", "Delete", "StrReplace", "Edit", "MultiEdit", "NotebookEdit"):
        return basename_of("path", "file_path", "notebook_path")
    if name in ("Grep", "SemanticSearch"):
        return first_line(inp.get("pattern") or inp.get("query") or "")
    if name in ("Task",):
        return first_line(inp.get("description") or inp.get("prompt") or "")
    if name == "Glob":
        return first_line(inp.get("glob_pattern") or inp.get("pattern") or "")
    if name in ("TodoWrite",):
        return "updating task list"
    if name in ("WebSearch", "WebFetch"):
        return first_line(inp.get("search_term") or inp.get("query") or inp.get("url") or "")
    # fall back to first value
    for k in ("description", "explanation", "title"):
        if inp.get(k):
            return first_line(inp[k])
    return name


def _normalize_events(path):
    """Return a list of normalized events from a .jsonl transcript."""
    events = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("type") == "turn_ended":
                    events.append({
                        "kind": "turn_ended",
                        "status": obj.get("status"),
                        "text": "",
                        "tools": [],
                    })
                    continue
                role = obj.get("role")
                if role not in ("user", "assistant"):
                    continue
                content = ((obj.get("message") or {}).get("content")) or []
                texts = []
                tools = []
                if isinstance(content, str):
                    texts.append(content)
                else:
                    for block in content:
                        if not isinstance(block, dict):
                            continue
                        btype = block.get("type")
                        if btype == "text" and block.get("text"):
                            texts.append(block["text"])
                        elif btype == "tool_use":
                            tools.append({
                                "name": block.get("name", "tool"),
                                "detail": _tool_detail(block.get("name", ""), block.get("input")),
                            })
                events.append({
                    "kind": role,
                    "text": _clean_text("\n\n".join(texts)),
                    "tools": tools,
                })
    except Exception:
        pass
    return events


def _turn_in_progress(events):
    """True if the session's latest turn has NOT ended yet.

    A Cursor turn is delimited by an explicit ``turn_ended`` marker. The agent is
    actively working when there is conversational activity (a user prompt, or the
    agent mid-response / mid-tool-use) AFTER the last ``turn_ended``. Once the agent
    finishes and ``turn_ended`` is written, the session is waiting on the user.

    This is far more reliable than guessing from file timestamps, because
    ``turn_ended`` is a definitive boundary rather than a recency heuristic.
    """
    last_end = -1
    last_msg = -1
    for i, e in enumerate(events):
        if e["kind"] == "turn_ended":
            last_end = i
        elif e["kind"] in ("user", "assistant"):
            last_msg = i
    return last_msg > last_end


def _latest_sub_mtime(sub_files):
    """Most recent write across a session's background subagent transcripts (0 if none)."""
    if not sub_files:
        return 0.0
    return max((m for _, m in sub_files), default=0.0)


def _active_sub_count(sub_files):
    """How many background subagents are *currently running* -- i.e. their transcript
    was written within the freshness window. The subagents/ dir also holds finished
    ones, so we count only recently-touched files (the UI shows a little helper per
    active subagent next to the working agent)."""
    if not sub_files:
        return 0
    now = time.time()
    return sum(1 for _, m in sub_files if (now - m) <= SUBAGENT_ACTIVE_SECONDS)


def _first_user_text(path):
    """First user-message text from a transcript (works for either Cursor or Claude
    line format). Used to label a subagent when it has no metadata file."""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                role = o.get("role") or ((o.get("message") or {}).get("role"))
                if role != "user":
                    continue
                c = (o.get("message") or {}).get("content")
                if c is None:
                    c = o.get("content")
                if isinstance(c, str):
                    return _clean_text(c)
                if isinstance(c, list):
                    for b in c:
                        if isinstance(b, dict) and b.get("type") == "text" and b.get("text"):
                            return _clean_text(b["text"])
    except Exception:
        pass
    return ""


def _sub_activity(path):
    """Read a subagent transcript ONCE (scanned from the end) and return four fields --
    (bubble_text, bubble_kind, last_tool, last_message):
      - bubble_text/bubble_kind drive the ephemeral dwarf bubble/chip: the newest assistant
        message's headline, tool winning within that message (kind 'tool'|'assistant'|'').
      - last_tool = "Name: detail" of the most-recent tool_use (may be an earlier message).
      - last_message = the most-recent assistant TEXT ([:360], + " ..." when longer).
    The last two mirror the desk hover-card's independent last_tool / last_message so a
    helper dwarf's tooltip can show BOTH what it last ran and what it last wrote. All ""
    when nothing is found."""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except Exception:
        return ("", "", "", "")
    bub_txt, bub_kind, last_tool, last_message = "", "", "", ""
    for line in reversed(lines):
        line = line.strip()
        if not line or '"assistant"' not in line:   # cheap pre-filter
            continue
        try:
            o = json.loads(line)
        except Exception:
            continue
        role = o.get("role") or ((o.get("message") or {}).get("role"))
        if role != "assistant":
            continue
        c = (o.get("message") or {}).get("content")
        if c is None:
            c = o.get("content")
        m_tool_first, m_tool_last, m_text = "", "", ""
        if isinstance(c, str):
            m_text = _clean_text(c)
        elif isinstance(c, list):
            tools, parts = [], []
            for b in c:
                if not isinstance(b, dict):
                    continue
                bt = b.get("type")
                if bt == "tool_use":
                    tools.append(("%s: %s" % (b.get("name", "tool"),
                                  _tool_detail(b.get("name", ""), b.get("input")))).strip().rstrip(":"))
                elif bt == "text" and b.get("text"):
                    parts.append(b["text"])
            if tools:
                m_tool_first, m_tool_last = tools[0], tools[-1]
            m_text = _clean_text("\n".join(parts))
        # ephemeral bubble: newest content-bearing message, tool wins (first tool in the msg)
        if not bub_kind:
            if m_tool_first:
                bub_txt, bub_kind = m_tool_first, "tool"
            elif m_text:
                bub_txt, bub_kind = m_text, "assistant"
        # hover fields: most-recent tool and most-recent text, found INDEPENDENTLY
        if not last_tool and m_tool_last:
            last_tool = m_tool_last
        if not last_message and m_text:
            last_message = m_text[:360].rstrip() + (" ..." if len(m_text) > 360 else "")
        if bub_kind and last_tool and last_message:
            break
    return (bub_txt, bub_kind, last_tool, last_message)


def _subagent_infos(sub_files):
    """For the *currently running* subagents, return [{type, detail}] describing what
    each is doing. Claude subagents carry a sibling ``<name>.meta.json`` with an
    ``agentType`` + ``description``; otherwise we fall back to the subagent's opening
    prompt. Sorted by path so a given subagent keeps the same helper slot."""
    if not sub_files:
        return []
    now = time.time()
    infos = []
    for path, m in sorted(sub_files, key=lambda pm: pm[0]):
        if (now - m) > SUBAGENT_ACTIVE_SECONDS:
            continue
        typ, detail = "", ""
        meta = (path[:-len(".jsonl")] + ".meta.json") if path.endswith(".jsonl") else path + ".meta.json"
        try:
            if os.path.isfile(meta):
                with open(meta, "r", encoding="utf-8", errors="replace") as fh:
                    md = json.load(fh)
                typ = (md.get("agentType") or "").strip()
                detail = (md.get("description") or "").strip()
        except Exception:
            pass
        if not detail:
            detail = _first_user_text(path)
        sub_id = os.path.splitext(os.path.basename(path))[0]
        bub_txt, bub_kind, last_tool, last_message = _sub_activity(path)
        infos.append({"type": typ, "detail": detail[:140], "id": sub_id,
                      "last_msg": bub_txt[:160], "last_kind": bub_kind,
                      "last_tool": last_tool, "last_message": last_message, "ts": m})
    return infos


_BG_CONTENT_RE = re.compile(
    r"background with ID:\s*(\w+)\.\s*Output is being written to:\s*(\S+?\.output)")


def _open_shells_claude(path, cap=6):
    """Background shells a Claude session started that are (as far as disk can tell) still
    running -- shown as little terminal windows by the desk.

    A background shell is a ``Bash`` tool_use with ``run_in_background: true``; its result
    line reports a task id + an output-file path. A shell is considered FINISHED once a
    terminal ``<task-notification>`` (status completed/failed) references its id -- in EITHER
    of the two on-disk forms (a consumed user-message line, or a queued ``attachment``).
    Absence of that notification = still running (this mirrors Claude's own "N shells"
    counter, and shares its one blind spot: a shell killed out-of-band via ``kill``/``pkill``
    leaves no transcript trace, so it can be over-reported). Returns up to ``cap`` shells
    newest-first: ``[{id, command, running, output_tail}]``."""
    cmd_by_tuid, shells, order, finished = {}, {}, [], set()
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                m = o.get("message")
                if isinstance(m, dict) and isinstance(m.get("content"), list):
                    for b in m["content"]:
                        if not isinstance(b, dict):
                            continue
                        if (b.get("type") == "tool_use" and b.get("name") == "Bash"
                                and isinstance(b.get("input"), dict)
                                and b["input"].get("run_in_background")):
                            cmd_by_tuid[b.get("id")] = b["input"].get("command", "")
                        elif b.get("type") == "tool_result" and isinstance(b.get("content"), str):
                            tur = o.get("toolUseResult")
                            tid = tur.get("backgroundTaskId") if isinstance(tur, dict) else None
                            mt = _BG_CONTENT_RE.search(b["content"])
                            if tid and mt:
                                shells[tid] = {"command": cmd_by_tuid.get(b.get("tool_use_id"), ""),
                                               "output_file": mt.group(2)}
                                if tid not in order:
                                    order.append(tid)
                # terminal task-notifications mark a shell finished -- both on-disk forms
                txt = None
                if isinstance(m, dict) and isinstance(m.get("content"), str) and "<task-notification>" in m["content"]:
                    txt = m["content"]
                att = o.get("attachment")
                if isinstance(att, dict) and att.get("commandMode") == "task-notification":
                    txt = att.get("prompt", "")
                if txt:
                    ti = re.search(r"<task-id>(\w+)</task-id>", txt)
                    st = re.search(r"<status>(\w+)</status>", txt)
                    if ti and st and st.group(1) in ("completed", "failed"):
                        finished.add(ti.group(1))
    except Exception:
        return []
    # PRIORITISE running shells (newest-first), then fill with the most-recent finished ones,
    # THEN cap. Otherwise a long-lived shell (e.g. a --watch dev server) gets capped out by a
    # burst of newer, already-finished commands and never shows -- even while still running.
    newest = list(reversed(order))
    ordered = [t for t in newest if t not in finished] + [t for t in newest if t in finished]
    out = []
    for tid in ordered[:cap]:
        s = shells[tid]
        tail = ""
        try:
            f = s["output_file"]
            if os.path.exists(f) and not os.path.islink(f):
                nz = [ln for ln in open(f, "r", encoding="utf-8", errors="replace").read().splitlines() if ln.strip()]
                tail = " / ".join(nz[-2:])[:150]
        except Exception:
            pass
        out.append({"id": tid,
                    "command": _clean_text(s["command"])[:200],
                    "running": tid not in finished,
                    "output_tail": tail})
    return out


def _is_working(turn_in_progress, eff_mtime, sub_files, wf_latest=0.0):
    """Office (working) vs kitchen (waiting), decided by TURN STATE + rollups.

    Working when the latest turn is still in progress, OR a background subagent
    was written very recently (multitask: parent idle, worker running), OR a dynamic
    Workflow's files were written very recently (the Workflow tool returns immediately
    after launch, so the parent's own turn ends while its subagents are still running).
    Either way a turn completely silent past the staleness cap is considered abandoned
    and sent to the kitchen so it can't occupy a desk indefinitely.

    Computed fresh per request (depends on wall-clock vs the rolled-up mtimes).
    """
    now = time.time()
    eff = max(eff_mtime, wf_latest or 0.0)
    if (now - eff) > WORKING_STALE_CAP_SECONDS:
        return False
    if turn_in_progress:
        # a turn that owes a PLAIN reply (Claude turn-kind "reply") but has been silent a long
        # time is stuck/abandoned mid-turn -> idle. Mid-tool turns ("tool"/generic truthy) can
        # legitimately be silent for one long tool call, so they keep the far-out stale cap.
        if turn_in_progress == "reply" and (now - eff) > REPLY_STALE_SECONDS:
            return False
        return True
    latest_sub = _latest_sub_mtime(sub_files)
    if latest_sub and (now - latest_sub) <= SUBAGENT_ACTIVE_SECONDS:
        return True
    # a dynamic Workflow whose journal / agent transcripts were touched within the
    # freshness window keeps the parent "working" even though its own turn has ended.
    return bool(wf_latest) and (now - wf_latest) <= SUBAGENT_ACTIVE_SECONDS


def _rel_time(seconds_ago):
    s = int(seconds_ago)
    if s < 60:
        return f"{s}s ago"
    m = s // 60
    if m < 60:
        return f"{m}m ago"
    h = m // 60
    if h < 24:
        return f"{h}h ago"
    d = h // 24
    return f"{d}d ago"


_KNOWN_SUBAGENT_IDS = set()  # subagent uuids ever seen, remembered across scans
_KNOWN_SUBAGENT_LOCK = threading.Lock()


def discover_transcripts():
    """Yield (uuid, project_folder, abspath, eff_mtime, sub_files) for top-level
    agent transcripts, de-duplicated across ALL Cursor project roots.

    Two correctness measures prevent the "appears after refresh then vanishes"
    flicker:

    * GLOBAL subagent exclusion. A subagent transcript is recorded inside its
      parent's ``<parent>/subagents/<uuid>.jsonl`` AND (sometimes) as its own
      top-level ``<uuid>/<uuid>.jsonl`` dir. We gather subagent uuids across EVERY
      project (not just the current one) and never list them as their own agent.
      Known subagent ids are also remembered across scans, so a transient gap in
      the filesystem registration can't momentarily promote a subagent to a
      top-level agent.
    * CROSS-PROJECT de-dup. The same chat uuid can have a top-level transcript dir
      in more than one project root (e.g. ``my-app`` and ``empty-window``). Yielding
      both hands the frontend two agents with the same id -- one computed "working"
      and one "waiting" -- which fight over the same slot and flicker. We keep a
      single representative per uuid. When a uuid is duplicated we PREFER the copy
      that currently computes to 'working' (e.g. the live ``my-app`` copy with a
      fresh mid-turn subagent) over a stale copy (e.g. an ``empty-window`` copy with
      a finished turn and no subagents), so the stale one can never shadow the
      working one. Ties fall back to freshest eff_mtime, then most subagents.

    ``eff_mtime`` is the most recent of the chat itself or any of its subagents, so
    a session whose work runs in a background subagent still shows as working.
    """
    if not os.path.isdir(CURSOR_PROJECTS_DIR):
        return
    try:
        projects = os.listdir(CURSOR_PROJECTS_DIR)
    except OSError:
        return

    # ---- pass 1: gather subagent ids + files across ALL projects ----
    subagent_ids = set()
    sub_mtime = {}        # (project, entry) -> latest subagent transcript mtime
    sub_files = {}        # (project, entry) -> [(subpath, submtime), ...]
    project_entries = {}  # project -> entries list (cached so we don't relist)
    for project in projects:
        at_dir = os.path.join(CURSOR_PROJECTS_DIR, project, "agent-transcripts")
        if not os.path.isdir(at_dir):
            continue
        try:
            entries = os.listdir(at_dir)
        except OSError:
            continue
        project_entries[project] = entries
        for entry in entries:
            sub_dir = os.path.join(at_dir, entry, "subagents")
            if not os.path.isdir(sub_dir):
                continue
            try:
                subs = os.listdir(sub_dir)
            except OSError:
                continue
            for f in subs:
                if not f.endswith(".jsonl"):
                    continue
                subagent_ids.add(f[: -len(".jsonl")])
                try:
                    subpath = os.path.join(sub_dir, f)
                    m = os.path.getmtime(subpath)
                    sub_files.setdefault((project, entry), []).append((subpath, m))
                    if m > sub_mtime.get((project, entry), 0):
                        sub_mtime[(project, entry)] = m
                except OSError:
                    pass

    # remember subagent ids across scans (robust against transient registration gaps)
    with _KNOWN_SUBAGENT_LOCK:
        _KNOWN_SUBAGENT_IDS.update(subagent_ids)
        known = set(_KNOWN_SUBAGENT_IDS)

    # ---- pass 2: collect ALL candidate copies per uuid ----
    cands = {}  # uuid -> [(eff_mtime, n_sub, project, jsonl, sub_files_list), ...]
    for project, entries in project_entries.items():
        at_dir = os.path.join(CURSOR_PROJECTS_DIR, project, "agent-transcripts")
        for entry in entries:
            if entry == "subagents" or entry in known:
                continue
            sess_dir = os.path.join(at_dir, entry)
            if not os.path.isdir(sess_dir):
                continue
            jsonl = os.path.join(sess_dir, entry + ".jsonl")
            if not os.path.isfile(jsonl):
                continue
            try:
                mtime = os.path.getmtime(jsonl)
            except OSError:
                continue
            sf = sub_files.get((project, entry), [])
            eff_mtime = max(mtime, sub_mtime.get((project, entry), 0))
            cands.setdefault(entry, []).append((eff_mtime, len(sf), project, jsonl, sf))

    # ---- resolve duplicates: keep the live/freshest copy ----
    # The same chat uuid can have a top-level dir in more than one project root. We
    # keep a single representative: freshest rolled-up eff_mtime first (the copy
    # being actively written), then the one with the most subagents -- so a stale
    # duplicate can never shadow the live copy and steal its desk/kitchen slot.
    for uuid, lst in cands.items():
        if len(lst) == 1:
            eff_mtime, _n, project, jsonl, sf = lst[0]
        else:
            def _score(c):
                eff, n, _proj, _jl, _sfl = c
                return (eff, n)
            eff_mtime, _n, project, jsonl, sf = max(lst, key=_score)
        yield uuid, project, jsonl, eff_mtime, sf


_CACHE = {}  # uuid -> (mtime, parsed_dict)
_CACHE_LOCK = threading.Lock()


def parse_agent(uuid, project, path, mtime, sub_files=None, full=False):
    with _CACHE_LOCK:
        cached = _CACHE.get(uuid)
        if cached and cached[0] == mtime and (full <= cached[1].get("_full", False)):
            return cached[1]

    events = _normalize_events(path)

    task_full = ""
    for ev in events:
        if ev["kind"] == "user" and ev["text"]:
            task_full = _strip_leading_timestamp(ev["text"]) or ev["text"]
            break
    title = task_full.split("\n")[0].strip()
    if len(title) > 70:
        title = title[:67].rstrip() + "..."
    if not title:
        title = "(untitled session)"

    latest_response = ""
    for ev in reversed(events):
        if ev["kind"] == "assistant" and ev["text"]:
            latest_response = ev["text"]
            break

    latest_tool = None
    for ev in reversed(events):
        if ev["tools"]:
            latest_tool = ev["tools"][-1]
            break

    turn_in_progress = _turn_in_progress(events)
    status = "working" if _is_working(turn_in_progress, mtime, sub_files) else "waiting"
    msg_count = sum(1 for e in events if e["kind"] in ("user", "assistant"))

    # what the agent is doing *right now*: most recent assistant text, else the
    # most recent tool action, else fall back to the opening task.
    latest_activity = latest_response
    latest_kind = "assistant"
    if not latest_activity and latest_tool:
        latest_activity = f"{latest_tool['name']}: {latest_tool.get('detail', '')}".strip().rstrip(":")
        latest_kind = "tool"
    if not latest_activity:
        latest_activity = task_full
        latest_kind = "task"
    latest_short = latest_activity[:360].rstrip() + (" ..." if len(latest_activity) > 360 else "")

    result = {
        "id": uuid,
        "source": "cursor",
        "scheduled": False,
        "name": _name_for(uuid),
        "variant": _variant_for(uuid),
        "project": _pretty_project(project),
        "status": status,
        "turn_in_progress": turn_in_progress,
        "title": title,
        "preview": (task_full[:360].rstrip() + (" ..." if len(task_full) > 360 else "")) or title,
        "latest": latest_short or title,
        "latest_kind": latest_kind,
        # for the hover card: the last tool used (with detail) and the last text message,
        # kept SEPARATE (the ephemeral chip only shows the short tool name).
        "last_tool": (("%s: %s" % (latest_tool["name"], latest_tool.get("detail", ""))).strip().rstrip(":") if latest_tool else ""),
        "last_message": ((latest_response[:360].rstrip() + (" ..." if len(latest_response) > 360 else "")) if latest_response else ""),
        "message_count": msg_count,
        "mtime": mtime,
        "last_activity_rel": _rel_time(time.time() - mtime),
        "_full": False,
    }

    if full:
        timeline = []
        for ev in events[-14:]:
            if ev["kind"] == "turn_ended":
                timeline.append({"role": "system", "text": f"-- turn ended ({ev.get('status')}) --", "tools": []})
                continue
            text = ev["text"]
            if len(text) > 1600:
                text = text[:1600].rstrip() + " ..."
            timeline.append({
                "role": ev["kind"],
                "text": text,
                "tools": ev["tools"][:6],
            })
        result.update({
            "task_full": task_full,
            "latest_response": latest_response[:6000],
            "latest_tool": latest_tool,
            "timeline": timeline,
            "transcript_path": path,
            "_full": True,
        })

    with _CACHE_LOCK:
        _CACHE[uuid] = (mtime, result)
    return result


# --------------------------------------------------------------------------------------
# Claude Code transcripts (~/.claude/projects) -- same office, tagged source="claude"
# --------------------------------------------------------------------------------------

def _claude_pretty_project(dirname):
    """Best-effort label from a Claude project dir.

    Claude encodes the launch cwd as the dir name ('/' -> '-', leading '-'). Real
    dashes make it impossible to reverse perfectly, so we show the last couple of
    path-ish segments -- matching the cursor pretty style (e.g. '...-my-app' ->
    'my-app').
    """
    name = (dirname or "").lstrip("-")
    if name.lower().startswith("users-"):
        parts = name.split("-")
        if len(parts) >= 2:
            name = "-".join(parts[-2:])
    return name


def _normalize_events_claude(path):
    """Normalize a Claude Code .jsonl into the shared event shape.

    Returns ``(events, title, scheduled, scheduled_name)`` where ``title`` is the
    session name: a user-set ``custom-title`` if present, else the auto ``ai-title``.
    Claude Code has no ``turn_ended`` marker, so we only emit user/assistant events;
    tool-result user messages are flagged so the first *real* user prompt (not a tool
    result) can be used as the task. Inline sidechain (subagent) records are skipped so
    the office worker reflects the main thread -- a running Task subagent still surfaces
    as the parent's pending tool_use.

    A session started by a scheduled task / cron opens with a
    ``<scheduled-task name="..." file="...">`` marker in its first user message; we
    detect that (before the tag is stripped) so those agents can be shown as couriers.
    """
    events = []
    ai_title = ""
    custom_title = ""
    scheduled = False
    scheduled_name = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("type") == "ai-title" and obj.get("aiTitle"):
                    ai_title = obj["aiTitle"]
                    continue
                if obj.get("type") == "custom-title" and obj.get("customTitle"):
                    custom_title = obj["customTitle"]   # a name the user gave the session
                    continue
                if obj.get("isSidechain"):
                    continue
                msg = obj.get("message") or {}
                role = msg.get("role")
                if role not in ("user", "assistant"):
                    continue
                content = msg.get("content") or []
                texts = []
                tools = []
                is_tool_result = False
                if isinstance(content, str):
                    texts.append(content)
                else:
                    for block in content:
                        if not isinstance(block, dict):
                            continue
                        btype = block.get("type")
                        if btype == "text" and block.get("text"):
                            texts.append(block["text"])
                        elif btype == "tool_use":
                            tools.append({
                                "name": block.get("name", "tool"),
                                "detail": _tool_detail(block.get("name", ""), block.get("input")),
                            })
                        elif btype == "tool_result":
                            is_tool_result = True
                injected = False
                if role == "user":
                    joined = "\n".join(texts)  # raw, before tags are stripped
                    # slash-command echoes, local-command output, task notifications,
                    # system reminders and caveats are appended as user-role lines but
                    # are NOT a real user turn -- flag them so turn-detection can skip them.
                    injected = _is_injected_user_text(joined)
                    if not scheduled and "<scheduled-task" in joined:
                        scheduled = True
                        m = re.search(r'name="([^"]+)"', joined)
                        if m:
                            scheduled_name = m.group(1)
                events.append({
                    "kind": role,
                    "text": _clean_text("\n\n".join(texts)),
                    "tools": tools,
                    "is_tool_result": is_tool_result,
                    "injected": injected,
                })
    except Exception:
        pass
    # a name the user gave the session wins over the auto-generated one
    return events, (custom_title or ai_title), scheduled, scheduled_name


def _turn_in_progress_claude(events):
    """Claude has no ``turn_ended`` marker: a turn is done once the latest message is
    a final assistant answer (text with no pending tool call). Anything else -- a
    fresh user prompt, a tool result awaiting the model, or an in-flight tool_use --
    means the agent is still working (at a desk)."""
    for e in reversed(events):
        if e["kind"] not in ("user", "assistant"):
            continue
        # injected/automated user-role lines (system reminders, task notifications,
        # slash-command echoes, local-command output, caveats) are appended AFTER the
        # final answer -- they are not a real user turn. Skip them, or a finished
        # session would look mid-turn (stuck working at a desk) forever.
        if e["kind"] == "user" and e.get("injected"):
            continue
        # a user interrupt (Ctrl-C / Esc) aborts the turn: the transcript records
        # "[Request interrupted by user...]" and nothing runs after it until the user
        # speaks again. Treat it as a turn boundary -> waiting, not stuck-working forever.
        if e["kind"] == "user" and (e["text"] or "").lstrip().startswith("[Request interrupted by user"):
            return ""
        if e["kind"] == "assistant":
            if e["text"] and not e["tools"]:
                return ""      # delivered a final response -> done, waiting on the user
            return "tool"      # a pending tool_use (may run a long time) -> mid-tool
        # a user event that is a tool result awaits the model -> also mid-tool
        if e.get("is_tool_result"):
            return "tool"
        return "reply"         # a plain user message with no reply yet -> agent owes a reply
    return ""                  # no conversation yet


# user-role transcript lines that aren't something the user actually typed: slash commands,
# local command output, task notifications, system reminders, and the local-command caveat.
_INJECTED_USER_PREFIXES = (
    "<command-name>", "<command-message>", "<command-args>", "<command-contents>",
    "<local-command-stdout>", "<local-command-stderr>",
    "<task-notification>", "<system-reminder>", "<user-prompt-submit-hook>",
    "<bash-input>", "<bash-stdout>", "<bash-stderr>",
    "[system notification",
    "caveat: the messages below were generated by the user while running",
)
_TRAILING_INJECT_RE = re.compile(
    r"\n\s*<(?:system-reminder|command-|local-command|task-notification|bash-)", re.IGNORECASE)


def _is_injected_user_text(text):
    return (text or "").lstrip().lower().startswith(_INJECTED_USER_PREFIXES)


def _last_user_instruction(path):
    """Most recent genuine user instruction from a Claude transcript: the last user-role
    text block that is NOT a tool result and NOT injected/automated content (slash commands,
    command output, task notifications, system reminders, caveats). Any injected block the
    harness appended after a real message is trimmed off the end."""
    result = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if '"user"' not in line:            # cheap pre-filter (user lines only)
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                m = o.get("message") or {}
                if (o.get("role") or m.get("role")) != "user":
                    continue
                c = m.get("content")
                if c is None:
                    c = o.get("content")
                if isinstance(c, list) and any(
                        isinstance(b, dict) and b.get("type") == "tool_result" for b in c):
                    continue                        # tool output, not a typed message
                txt = ""
                if isinstance(c, str):
                    txt = c
                elif isinstance(c, list):
                    for b in c:
                        if isinstance(b, dict) and b.get("type") == "text":
                            txt += b.get("text", "")
                txt = txt.strip()
                if not txt or _is_injected_user_text(txt):
                    continue
                txt = _TRAILING_INJECT_RE.split(txt, 1)[0].strip()   # drop appended reminders
                if txt:
                    result = txt
    except OSError:
        pass
    return result


def parse_claude_agent(uuid, project, path, mtime, sub_files=None, full=False):
    with _CACHE_LOCK:
        cached = _CACHE.get(uuid)
        if cached and cached[0] == mtime and (full <= cached[1].get("_full", False)):
            return cached[1]

    events, ai_title, scheduled, scheduled_name = _normalize_events_claude(path)

    task_full = ""
    for ev in events:
        if ev["kind"] == "user" and ev["text"] and not ev.get("is_tool_result"):
            task_full = _strip_leading_timestamp(ev["text"]) or ev["text"]
            break

    title = (ai_title or scheduled_name or task_full.split("\n")[0]).strip()
    if len(title) > 70:
        title = title[:67].rstrip() + "..."
    if not title:
        title = "(untitled session)"

    latest_response = ""
    for ev in reversed(events):
        if ev["kind"] == "assistant" and ev["text"]:
            latest_response = ev["text"]
            break

    latest_tool = None
    for ev in reversed(events):
        if ev["tools"]:
            latest_tool = ev["tools"][-1]
            break

    turn_in_progress = _turn_in_progress_claude(events)
    status = "working" if _is_working(turn_in_progress, mtime, sub_files) else "waiting"
    msg_count = sum(1 for e in events if e["kind"] in ("user", "assistant"))

    latest_activity = latest_response
    latest_kind = "assistant"
    if not latest_activity and latest_tool:
        latest_activity = f"{latest_tool['name']}: {latest_tool.get('detail', '')}".strip().rstrip(":")
        latest_kind = "tool"
    if not latest_activity:
        latest_activity = task_full
        latest_kind = "task"
    latest_short = latest_activity[:360].rstrip() + (" ..." if len(latest_activity) > 360 else "")

    # the most recent real thing the user typed (skip tool-result / system turns) --
    # shown as "Last instruction" alongside the agent's own latest activity.
    last_instruction = _last_user_instruction(path)
    last_instruction = _strip_leading_timestamp(last_instruction) or last_instruction
    if len(last_instruction) > 200:
        last_instruction = last_instruction[:200].rstrip() + " ..."

    usage = _claude_usage(path)

    result = {
        "id": uuid,
        "source": "claude",
        "scheduled": scheduled,
        "name": _name_for(uuid),
        "variant": _variant_for(uuid),
        "project": _claude_pretty_project(project),
        "status": status,
        "turn_in_progress": turn_in_progress,
        "title": title,
        "preview": (task_full[:360].rstrip() + (" ..." if len(task_full) > 360 else "")) or title,
        "latest": latest_short or title,
        "latest_kind": latest_kind,
        # hover card: last tool used (with detail) + last text message, kept SEPARATE
        # (the ephemeral chip only shows the short tool name).
        "last_tool": (("%s: %s" % (latest_tool["name"], latest_tool.get("detail", ""))).strip().rstrip(":") if latest_tool else ""),
        "last_message": ((latest_response[:360].rstrip() + (" ..." if len(latest_response) > 360 else "")) if latest_response else ""),
        "last_instruction": last_instruction,
        "message_count": msg_count,
        "model": usage["model"],
        "tokens": usage["tokens"],
        "spend": usage["spend"],
        "mtime": mtime,
        "last_activity_rel": _rel_time(time.time() - mtime),
        "_full": False,
    }

    if full:
        timeline = []
        for ev in events[-14:]:
            text = ev["text"]
            if len(text) > 1600:
                text = text[:1600].rstrip() + " ..."
            timeline.append({
                "role": ev["kind"],
                "text": text,
                "tools": ev["tools"][:6],
            })
        result.update({
            "task_full": task_full,
            "latest_response": latest_response[:6000],
            "latest_tool": latest_tool,
            "timeline": timeline,
            "transcript_path": path,
            "_full": True,
        })

    with _CACHE_LOCK:
        _CACHE[uuid] = (mtime, result)
    return result


def discover_claude_transcripts():
    """Yield (uuid, project_dir, abspath, eff_mtime, sub_files) for Claude Code chats.

    Each chat is ``~/.claude/projects/<encoded-cwd>/<uuid>.jsonl`` with Task
    subagents in a sibling ``<uuid>/subagents/*.jsonl``. ``eff_mtime`` rolls up the
    freshest write across the chat and its subagents (so a session whose work runs in
    a background subagent still reads as working). Duplicate uuids across roots keep
    the freshest copy, mirroring the cursor discovery.
    """
    if not os.path.isdir(CLAUDE_PROJECTS_DIR):
        return
    try:
        projects = os.listdir(CLAUDE_PROJECTS_DIR)
    except OSError:
        return

    cands = {}  # uuid -> [(eff_mtime, n_sub, project_dir, jsonl, sub_files), ...]
    for project in projects:
        pdir = os.path.join(CLAUDE_PROJECTS_DIR, project)
        if not os.path.isdir(pdir):
            continue
        try:
            entries = os.listdir(pdir)
        except OSError:
            continue
        for entry in entries:
            if not entry.endswith(".jsonl"):
                continue
            uuid = entry[: -len(".jsonl")]
            jsonl = os.path.join(pdir, entry)
            if not os.path.isfile(jsonl):
                continue
            try:
                mtime = os.path.getmtime(jsonl)
            except OSError:
                continue
            sf = []
            sub_dir = os.path.join(pdir, uuid, "subagents")
            if os.path.isdir(sub_dir):
                try:
                    for sfn in os.listdir(sub_dir):
                        if not sfn.endswith(".jsonl"):
                            continue
                        sp = os.path.join(sub_dir, sfn)
                        try:
                            sf.append((sp, os.path.getmtime(sp)))
                        except OSError:
                            pass
                except OSError:
                    pass
            sub_m = max((m for _, m in sf), default=0)
            eff_mtime = max(mtime, sub_m)
            cands.setdefault(uuid, []).append((eff_mtime, len(sf), project, jsonl, sf))

    for uuid, lst in cands.items():
        eff_mtime, _n, project, jsonl, sf = max(lst, key=lambda c: (c[0], c[1]))
        yield uuid, project, jsonl, eff_mtime, sf


# --------------------------------------------------------------------------------------
# Per-session usage: model, token throughput, rough $ spend  (Claude transcripts)
# --------------------------------------------------------------------------------------

def _model_family(model_id):
    m = (model_id or "").lower()
    if "opus" in m:
        return "opus"
    if "sonnet" in m:
        return "sonnet"
    if "haiku" in m:
        return "haiku"
    return None


def _pretty_model(model_id):
    """'claude-opus-4-8' -> 'Opus 4.8'; unknown ids returned as-is."""
    fam = _model_family(model_id)
    if not fam:
        return model_id or ""
    label = fam.capitalize()
    ver = re.search(r"(\d+)[-.](\d+)", model_id or "")
    return f"{label} {ver.group(1)}.{ver.group(2)}" if ver else label


def _claude_usage(path):
    """One raw scan of a Claude transcript: latest model, cumulative token throughput
    (input+output+cache) and a best-effort $ spend estimate from _MODEL_PRICING."""
    model_id = ""
    total = 0
    spend = 0.0
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if '"usage"' not in line and '"model"' not in line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                msg = o.get("message") or {}
                if not (o.get("type") == "assistant" or msg.get("role") == "assistant"):
                    continue
                if msg.get("model"):
                    model_id = msg["model"]
                u = msg.get("usage") or {}
                it = u.get("input_tokens") or 0
                ot = u.get("output_tokens") or 0
                cr = u.get("cache_read_input_tokens") or 0
                cw = u.get("cache_creation_input_tokens") or 0
                total += it + ot + cr + cw
                fam = _model_family(msg.get("model") or model_id)
                if fam:
                    pin, pout = _MODEL_PRICING[fam]
                    spend += (it * pin + ot * pout + cr * pin * 0.1 + cw * pin * 1.25) / 1_000_000
    except OSError:
        pass
    return {
        "model": _pretty_model(model_id),
        "tokens": total or None,
        "spend": round(spend, 2) if spend else None,
    }


# --------------------------------------------------------------------------------------
# Dynamic Workflow (the Workflow tool) discovery  (Claude-only, like the transcripts)
# --------------------------------------------------------------------------------------

def _find_workflow_script(session_dir, run_id):
    """The sibling script for a run lives at <session>/workflows/scripts/*-<run_id>.js."""
    sdir = os.path.join(session_dir, "workflows", "scripts")
    try:
        for fn in os.listdir(sdir):
            if fn.endswith(run_id + ".js"):
                return os.path.join(sdir, fn)
    except OSError:
        pass
    return None


def _parse_workflow_script(script_path):
    """Best-effort regex-extract of the script's `export const meta = {...}` literal:
    name, description and phase titles (capped). Never load-bearing -- always a fallback."""
    try:
        st = os.stat(script_path)
    except OSError:
        return {}
    cached = _WORKFLOW_SCRIPT_CACHE.get(script_path)
    if cached and cached[0] == st.st_mtime:
        return cached[1]
    meta = {"name": "", "description": "", "phases": []}
    try:
        with open(script_path, "r", encoding="utf-8", errors="replace") as fh:
            head = fh.read(20000)
        m = re.search(r"name:\s*['\"]([^'\"]+)['\"]", head)
        if m:
            meta["name"] = m.group(1)
        m = re.search(r"description:\s*['\"]([^'\"]+)['\"]", head)
        if m:
            meta["description"] = m.group(1)
        block = re.search(r"phases:\s*\[(.*?)\]", head, re.S)
        if block:
            for pm in re.finditer(r"title:\s*['\"]([^'\"]+)['\"]", block.group(1)):
                meta["phases"].append({"title": pm.group(1)})
                if len(meta["phases"]) >= 12:
                    break
    except OSError:
        pass
    _WORKFLOW_SCRIPT_CACHE[script_path] = (st.st_mtime, meta)
    return meta


def _workflow_identities(uuid, jsonl_path, mtime):
    """Scan the PARENT transcript for `toolUseResult` blobs of launched local workflows,
    returning {runId: {name, summary, scriptPath}}. Cached by parent mtime."""
    cached = _WORKFLOW_IDENTITY_CACHE.get(uuid)
    if cached and cached[0] == mtime:
        return cached[1]
    out = {}
    try:
        with open(jsonl_path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if "local_workflow" not in line:   # cheap pre-filter before json.loads
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                tur = o.get("toolUseResult")
                if isinstance(tur, dict) and tur.get("taskType") == "local_workflow":
                    rid = tur.get("runId")
                    if rid:
                        out[rid] = {
                            "name": tur.get("workflowName") or "",
                            "summary": tur.get("summary") or "",
                            "scriptPath": tur.get("scriptPath") or "",
                        }
    except OSError:
        pass
    _WORKFLOW_IDENTITY_CACHE[uuid] = (mtime, out)
    return out


# STRONG markers are unambiguous per-agent task headings -> jump to them wherever they appear
# (a shared preamble can be arbitrarily long). WEAK ones are common words -> only near the top.
_TASK_MARKERS_STRONG = ("YOUR AREA", "YOUR TASK", "YOUR JOB", "YOUR FOCUS", "YOUR SLICE",
                        "YOUR MISSION", "YOUR GOAL", "YOUR PIECE", "YOUR ROLE")
_TASK_MARKERS_WEAK = ("TASK:", "GOAL:", "OBJECTIVE:", "FOCUS:", "AREA:", "ROLE:")
_MARKER_HEAD_RE = re.compile(r"^(YOUR\s+[A-Za-z]+|TASK|GOAL|OBJECTIVE|FOCUS|AREA|ROLE|MISSION)"
                             r"\s*[:\-–—]+\s*", re.I)


def _distinctive_details(prompts, cap=140):
    """Per-agent SHORT label capturing what *that* subagent does. Sibling workflow agents
    almost always share a large identical preamble (the same context/instructions block) with
    only a small distinctive slice -- e.g. ``YOUR AREA -- ...`` -- differing, so the naive
    first-N-chars makes every helper-dwarf read identically. We strip the prefix common to all
    siblings in the run and/or jump to a task-marker heading, then collapse to one short line.
    Robust across arbitrary scripts (no dependency on the workflow source or agent() labels)."""
    nonempty = [p for p in prompts if p]
    cut = 0
    if len(nonempty) >= 2:                       # longest prefix shared by every sibling prompt
        s0, m = nonempty[0], len(nonempty[0])
        for p in nonempty[1:]:
            i, lim = 0, min(m, len(p))
            while i < lim and s0[i] == p[i]:
                i += 1
            m = i
            if not m:
                break
        if 0 < m < len(s0):                      # back up to a word/newline boundary
            b = max(s0.rfind("\n", 0, m), s0.rfind(" ", 0, m))
            cut = b if b > 0 else m
    out = []
    for p in prompts:
        if not p:
            out.append("")
            continue
        rest = p[cut:] if 0 < cut < len(p) else p
        up = rest.upper()
        hits =  [j for j in (up.find(mk) for mk in _TASK_MARKERS_STRONG) if j >= 0]
        hits += [j for j in (up.find(mk) for mk in _TASK_MARKERS_WEAK) if 0 <= j <= 240]
        if hits:
            rest = rest[min(hits):]              # jump to the per-agent "YOUR AREA / TASK:" heading
        rest = _MARKER_HEAD_RE.sub("", rest)     # drop the heading word itself
        rest = re.sub(r"\s+", " ", rest.lstrip(" \t\n-–—*:>#")).strip()
        out.append(rest[:cap].strip())
    return out


def _workflow_progress(run_dir):
    """Parse a run's journal.jsonl into {total, done, running, active[], latest_mtime,
    had_retries}. Logical tasks are keyed by the journal ``key`` (not agentId) so a retried
    task collapses to one; a task is counted RUNNING only when it has a started event, no
    result, AND its freshest agent-<id>.jsonl was written within SUBAGENT_ACTIVE_SECONDS --
    a started-with-no-result whose transcript went cold long ago died/finished silently and
    must not show as running. Journal parse cached by (mtime, size); freshness refreshed
    cheaply each call. Each active subagent's ``detail`` is de-boilerplated by
    ``_distinctive_details`` so sibling dwarves read distinctly."""
    journal = os.path.join(run_dir, "journal.jsonl")
    try:
        st = os.stat(journal)
    except OSError:
        return {"total": 0, "done": 0, "running": 0, "active": [], "latest_mtime": 0.0, "had_retries": False}
    cache_key = (st.st_mtime, st.st_size)
    cached = _WORKFLOW_JOURNAL_CACHE.get(run_dir)
    if cached and cached[0] == cache_key:
        base = cached[1]
    else:
        started_keys, result_keys, key_agents = set(), set(), {}
        n_started = 0
        try:
            with open(journal, "r", encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        o = json.loads(line)
                    except Exception:
                        continue
                    k = o.get("key"); aid = o.get("agentId"); t = o.get("type")
                    if not k or not aid:
                        continue
                    if t == "started":
                        n_started += 1
                        started_keys.add(k)
                        key_agents.setdefault(k, []).append(aid)
                    elif t == "result":
                        result_keys.add(k)
        except OSError:
            started_keys, result_keys, key_agents, n_started = set(), set(), {}, 0
        base = {
            "total": len(started_keys),
            "done": len(started_keys & result_keys),
            "open_keys": [k for k in started_keys if k not in result_keys],
            "key_agents": key_agents,
            "had_retries": n_started != len(started_keys),
        }
        _WORKFLOW_JOURNAL_CACHE[run_dir] = (cache_key, base)
    now = time.time()
    latest = st.st_mtime
    running_fresh = 0
    pending = []
    for k in base["open_keys"]:
        best_am, best_aid = None, None
        for aid in base["key_agents"].get(k, []):
            ap = os.path.join(run_dir, "agent-%s.jsonl" % aid)
            try:
                am = os.path.getmtime(ap)
            except OSError:
                continue
            if am > latest:
                latest = am
            if best_am is None or am > best_am:
                best_am, best_aid = am, aid
        if best_am is None or (now - best_am) > SUBAGENT_ACTIVE_SECONDS:
            continue   # never written, or went cold -> died/finished without a result
        running_fresh += 1
        if len(pending) < 6:
            ap = os.path.join(run_dir, "agent-%s.jsonl" % best_aid)
            bub_txt, bub_kind, last_tool, last_message = _sub_activity(ap)
            pending.append({"type": "workflow-subagent", "_prompt": _first_user_text(ap),
                            "id": best_aid, "last_msg": bub_txt[:160], "last_kind": bub_kind,
                            "last_tool": last_tool, "last_message": last_message, "ts": best_am})
    # de-boilerplate the sibling prompts together so each dwarf reads distinctly
    details = _distinctive_details([p.pop("_prompt") for p in pending])
    active = []
    for p, d in zip(pending, details):
        p["detail"] = d or "workflow subagent"
        active.append(p)
    return {
        "total": base["total"],
        "done": base["done"],
        "running": running_fresh,
        "active": active,
        "latest_mtime": latest,
        "had_retries": base["had_retries"],
    }


def _phase_states(phases, total, done, running, counts, trustworthy):
    """Colour an ordered phase list done/active/pending. Phases complete strictly in order
    (each phase is fully awaited before the next), so overall progress maps monotonically
    onto the stepper. When `trustworthy` (exact per-phase counts known and consistent) we
    greedily fill done-then-running across the counts for real per-phase (done, running,
    count); otherwise we only highlight the single phase the overall fraction lands in and
    print NO per-phase number (fabricating one would be dishonest -- per-phase counts are
    not recoverable from disk for most runs)."""
    k = len(phases)
    states = ["pending"] * k
    if k == 0:
        return states, None
    if trustworthy and counts and sum(counts) == total:
        rd, rr, per = done, running, []
        for c in counts:
            d = min(c, rd); rd -= d
            r = min(c - d, rr); rr -= r
            per.append((d, r, c))
        for i, (d, r, c) in enumerate(per):
            states[i] = "done" if (c > 0 and d == c) else ("active" if (d > 0 or r > 0) else "pending")
        return states, per
    if total and running == 0 and done >= total:
        return ["done"] * k, None
    idx = 0 if not total else min(k - 1, int((done / max(total, 1)) * k))
    for i in range(k):
        states[i] = "done" if i < idx else ("active" if i == idx else "pending")
    return states, None


def _discover_workflow_runs(uuid, jsonl_path, mtime, session_dir):
    """(display_runs, wf_latest) for a Claude session. display_runs are the runs that are
    currently running or finished within WORKFLOW_FRESH_SECONDS (running first, then by
    size); wf_latest is the freshest write across ALL runs (drives working/kitchen)."""
    wf_root = os.path.join(session_dir, "subagents", "workflows")
    if not os.path.isdir(wf_root):
        return [], 0.0
    try:
        names = os.listdir(wf_root)
    except OSError:
        return [], 0.0
    identities = None
    runs = []
    wf_latest = 0.0
    for name in names:
        if not name.startswith("wf_"):
            continue
        run_dir = os.path.join(wf_root, name)
        if not os.path.isdir(run_dir):
            continue
        prog = _workflow_progress(run_dir)
        wf_latest = max(wf_latest, prog["latest_mtime"])   # must stay BEFORE the gate (feeds _is_working)
        if prog["running"] <= 0:      # only show a run that has a genuinely-live agent right now
            continue
        if identities is None:
            identities = _workflow_identities(uuid, jsonl_path, mtime)
        ident = identities.get(name, {})
        wname = ident.get("name") or ""
        summary = ident.get("summary") or ""
        meta = {}
        script_path = ident.get("scriptPath") or _find_workflow_script(session_dir, name)
        if script_path:
            meta = _parse_workflow_script(script_path)
            wname = wname or meta.get("name") or ""
            summary = summary or meta.get("description") or ""
        phases = meta.get("phases") or []
        # honest phase stepper: colour each phase done/active/pending from overall logical
        # progress. Real per-phase counts are NOT recoverable from disk, so they appear only
        # when a strict trust gate proves them (currently never -- counts stay None). See
        # _phase_states.
        counts = [p.get("count") for p in phases]
        have_counts = len(counts) > 0 and all(c is not None for c in counts)
        trustworthy = (have_counts and not meta.get("dynamic")
                       and not prog["had_retries"]
                       and sum(c for c in counts) == prog["total"] and prog["total"] > 0)
        states, per = _phase_states(phases, prog["total"], prog["done"], prog["running"],
                                    counts if have_counts else None, trustworthy)
        enriched = []
        for i, p in enumerate(phases):
            e = {"title": p.get("title", ""), "detail": p.get("detail", ""), "state": states[i]}
            if per is not None:
                d, r, c = per[i]
                e["done"], e["running"], e["count"] = d, r, c
            enriched.append(e)
        phases = enriched
        if not wname:
            wname = name
        runs.append({
            "runId": name,
            "name": wname,
            "summary": summary,
            "phases": phases,
            "phase_trusted": per is not None,
            "total": prog["total"],
            "done": prog["done"],
            "running": prog["running"],
            "active": prog["active"],
        })
    runs.sort(key=lambda r: (0 if r["running"] > 0 else 1, -r["total"]))
    return runs, wf_latest


def _session_dir_for(path):
    """The session subdir (holding subagents/ and workflows/) for a parent transcript."""
    return path[:-len(".jsonl")] if path.endswith(".jsonl") else path


# Registry so get_agents / list_projects / get_agent_detail can walk every source
# uniformly. Each entry: (source_name, discover_fn, parse_fn).
_SOURCES = [
    ("cursor", discover_transcripts, parse_agent),
    ("claude", discover_claude_transcripts, parse_claude_agent),
]


def _project_matches(needle, *labels):
    """Substring match a --project needle against any of the given labels (raw dir
    and/or pretty label). Empty needle matches everything."""
    if not needle:
        return True
    needle = needle.lower()
    return any(needle in (lbl or "").lower() for lbl in labels)


def _enabled_sources(sources):
    """Filter the source registry by name (None -> all)."""
    if not sources:
        return _SOURCES
    want = set(sources)
    return [s for s in _SOURCES if s[0] in want]


def get_agents(hours, full=False, project_filter=None, sources=None):
    cutoff = time.time() - hours * 3600
    agents = []
    for _src, discover, parse in _enabled_sources(sources):
        for uuid, project, path, mtime, _sub_files in discover():
            if mtime < cutoff:
                continue
            a = parse(uuid, project, path, mtime, sub_files=_sub_files, full=full)
            if not _project_matches(project_filter, project, a["project"]):
                continue
            # dynamic Workflow tents (Claude only) + their freshness (keeps a parent at a
            # desk while its workflow subagents run, even though its own turn has ended).
            if SHOW_WORKFLOWS and _src == "claude":
                wf_runs, wf_latest = _discover_workflow_runs(uuid, path, mtime, _session_dir_for(path))
            else:
                wf_runs, wf_latest = [], 0.0
            a["workflows"] = wf_runs
            a["wf_running_agents"] = sum(r["running"] for r in wf_runs)
            # recompute status fresh each request: parse is cached, but working/
            # kitchen depends on wall-clock (the staleness cap + subagent freshness)
            # vs the turn state, so it can change even when the transcript hasn't.
            a["status"] = "working" if _is_working(a.get("turn_in_progress"), mtime, _sub_files, wf_latest) else "waiting"
            # parent is "self active" only while its OWN turn is in progress; when it's merely
            # working because a subagent/workflow is live, the desk should stop typing (item 8).
            a["self_active"] = bool(a.get("turn_in_progress")) and a["status"] == "working"
            a["last_activity_rel"] = _rel_time(time.time() - mtime)
            a["subagents"] = _subagent_infos(_sub_files)   # running subagents -> little helpers
            a["subs"] = len(a["subagents"])
            # open background shells (Claude only) -> little terminal windows. A background
            # shell survives the turn, so show it whether the chat is at a desk (working) or
            # in the kitchen (waiting) -- but not for archived/beach agents. Only genuinely-
            # running ones become sprites.
            if _src == "claude" and a["status"] in ("working", "waiting"):
                a["shells"] = [s for s in _open_shells_claude(path) if s["running"]][:3]
            else:
                a["shells"] = []
            agents.append(a)
    agents.sort(key=lambda a: a["mtime"], reverse=True)
    return agents


def list_projects(hours, sources=None):
    """Return [(pretty_label, raw_folder, active_count, source)] sorted by activity."""
    cutoff = time.time() - hours * 3600
    counts = {}
    for src, discover, parse in _enabled_sources(sources):
        for uuid, project, path, mtime, _sub_files in discover():
            if mtime < cutoff:
                continue
            a = parse(uuid, project, path, mtime, sub_files=_sub_files, full=False)
            key = (a["project"], project, src)
            counts[key] = counts.get(key, 0) + 1
    rows = [(pretty, raw, n, src) for (pretty, raw, src), n in counts.items()]
    rows.sort(key=lambda r: (-r[2], r[0]))
    return rows


def get_agent_detail(uuid):
    for _src, discover, parse in _SOURCES:
        for u, project, path, mtime, _sub_files in discover():
            if u == uuid:
                d = parse(uuid, project, path, mtime, sub_files=_sub_files, full=True)
                if SHOW_WORKFLOWS and _src == "claude":
                    wf_runs, wf_latest = _discover_workflow_runs(uuid, path, mtime, _session_dir_for(path))
                else:
                    wf_runs, wf_latest = [], 0.0
                d["workflows"] = wf_runs
                d["status"] = "working" if _is_working(d.get("turn_in_progress"), mtime, _sub_files, wf_latest) else "waiting"
                d["last_activity_rel"] = _rel_time(time.time() - mtime)
                d["subagents"] = _subagent_infos(_sub_files)
                d["subs"] = len(d["subagents"])
                d["shells"] = ([s for s in _open_shells_claude(path) if s["running"]][:3]
                               if _src == "claude" else [])
                return d
    return None


def demo_agents():
    now = time.time()
    # working agents / their live helpers occasionally "say" a new thing; each gets its own
    # slow, staggered clock so the office shows the odd bubble popping -- not a wall of them.
    def _blip(off, period=15):
        return int((now + off) // period)
    subs_a = [{"type": "general-purpose", "detail": "Review the working diff for bugs",
               "id": "demoA-0", "last_msg": "Grep: export path (%d)" % _blip(0), "last_kind": "tool",
               "last_tool": "Grep: export path", "last_message": "scanning for the config loader", "ts": now},
              {"type": "test-runner", "detail": "Run the unit test suite",
               "id": "demoA-1", "last_msg": "unit suite green, pass %d" % _blip(5), "last_kind": "assistant",
               "last_tool": "Bash: pytest -q", "last_message": "unit suite green, all 42 pass", "ts": now}]
    subs_e = [{"type": "explorer", "detail": "Map the ORM query paths",
               "id": "demoE-0", "last_msg": "Read: orders.py (%d)" % _blip(2), "last_kind": "tool",
               "last_tool": "Read: orders.py", "last_message": "tracing the pagination query", "ts": now},
              {"type": "db-analyst", "detail": "EXPLAIN the slow orders query",
               "id": "demoE-1", "last_msg": "Bash: EXPLAIN ANALYZE (%d)" % _blip(8), "last_kind": "tool",
               "last_tool": "Bash: EXPLAIN ANALYZE orders", "last_message": "the seq scan is the bottleneck", "ts": now},
              {"type": "doc-writer", "detail": "Draft the fix summary",
               "id": "demoE-2", "last_msg": "drafting summary v%d" % _blip(12), "last_kind": "assistant",
               "last_tool": "Edit: report.md", "last_message": "drafting the fix summary", "ts": now}]
    wf_demo = [{
        "runId": "wf_demo01",
        "name": "exhaustive-security-audit",
        "summary": "Fan out finders across every subsystem, then adversarially verify each finding before reporting",
        "phases": [{"title": "Find", "state": "done"}, {"title": "Verify", "state": "active"},
                   {"title": "Synthesize", "state": "pending"}],
        "phase_trusted": False,
        "total": 21, "done": 14, "running": 3,
        "active": [{"type": "workflow-subagent", "detail": "Verify the auth-bypass finding",
                    "id": "demoW-0", "last_msg": "auth-bypass looks real (%d)" % _blip(3), "last_kind": "assistant",
                    "last_tool": "Read: auth/middleware.py", "last_message": "auth-bypass looks real -- no token check on the admin route", "ts": now},
                   {"type": "workflow-subagent", "detail": "Refute the SSRF candidate",
                    "id": "demoW-1", "last_msg": "Edit: sanitizer.py (%d)" % _blip(9), "last_kind": "tool",
                    "last_tool": "Edit: sanitizer.py", "last_message": "the SSRF filter is actually sound", "ts": now},
                   {"type": "workflow-subagent", "detail": "Check the deserialization sink",
                    "id": "demoW-2", "last_msg": "WebFetch: cve database (%d)" % _blip(14), "last_kind": "tool",
                    "last_tool": "WebFetch: nvd.nist.gov", "last_message": "cross-checking against the CVE list", "ts": now}],
    }]
    samples = [
        ("demo-aaaa-0001", "working", "Refactor the data export pipeline", 120, "cursor", False, subs_a, []),
        ("demo-bbbb-0002", "working", "Add pagination to the users API endpoint", 600, "claude", False, [], []),
        ("demo-cccc-0003", "waiting", "Why is this record showing up as archived?", 1800, "cursor", False, [], []),
        ("demo-dddd-0004", "waiting", "Write tests for the CSV importer", 5400, "claude", False, [], []),
        ("demo-eeee-0005", "working", "Investigate slow query on the orders table", 300, "claude", False, subs_e, []),
        ("demo-hhhh-0008", "working", "Audit the payments service for vulnerabilities", 45, "claude", False, [], wf_demo),
        ("demo-ffff-0006", "waiting", "Daily production error monitor", 9000, "claude", True, [], []),
        ("demo-gggg-0007", "waiting", "Nightly dependency update check", 12000, "claude", True, [], []),
    ]
    # demo open background shells (little terminal windows by the desk): one clean single
    # shell, a 3-shell max case (alongside helper dwarves), and a 2-shell case (alongside a
    # workflow easel) so QA covers coexistence with both neighbours.
    demo_shells = {
        "demo-bbbb-0002": [
            {"id": "sh-b1", "command": "npm run dev -- --port 3000", "running": True,
             "output_tail": "VITE ready in 431 ms / ➜ Local: http://localhost:3000/"}],
        "demo-eeee-0005": [
            {"id": "sh-e1", "command": "python manage.py runserver 0.0.0.0:8000", "running": True,
             "output_tail": "Watching for file changes with StatReloader / System check identified no issues"},
            {"id": "sh-e2", "command": "tail -f logs/orders-slow.log", "running": True,
             "output_tail": "SELECT * FROM orders WHERE status=? (1.83s) / slow query logged"},
            {"id": "sh-e3", "command": "redis-server --port 6380", "running": True,
             "output_tail": "Ready to accept connections tcp"}],
        "demo-hhhh-0008": [
            {"id": "sh-h1", "command": "docker compose up payments", "running": True,
             "output_tail": "payments-1  | Listening on :9099"},
            {"id": "sh-h2", "command": "python3 -m http.server 8080", "running": True,
             "output_tail": "Serving HTTP on 0.0.0.0 port 8080 ..."}],
        # a WAITING (kitchen) agent with a live shell -> exercises kitchen-shell rendering
        "demo-dddd-0004": [
            {"id": "sh-d1", "command": "pytest -q --looponfail tests/importer", "running": True,
             "output_tail": "watching for changes... / 12 passed in 0.42s"}],
    }
    out = []
    for idx, (uuid, status, title, ago, source, scheduled, subagents, workflows) in enumerate(samples):
        # a WORKING agent that is actually typing (no helpers) alternates between writing text
        # (white bubble) and running a tool (dark chip) on its own slow clock; a delegating
        # parent (turn ended, dwarves running) and waiting agents keep a static last line so
        # only their dwarves pop indicators. Nothing syncs up -> the odd bubble/chip, not a wall.
        active_typing = status == "working" and not subagents and not workflows
        if active_typing:
            phase = _blip(idx * 4, 13)
            if phase % 2:
                tool = ["Edit", "Bash", "Grep", "Read"][idx % 4]
                latest = "%s: %s.py [%d]" % (tool, title.split()[0].lower(), phase)
                lkind = "tool"
            else:
                latest = "Reviewing the latest changes about " + title.split()[0].lower() + " [%d]" % phase
                lkind = "assistant"
        else:
            latest = ("Working with helpers on " + title.split()[0].lower()) if status == "working" \
                     else "Wrapped up -- waiting for your next instruction."
            lkind = "assistant"
        # a fresh user instruction lands on a working agent every so often (staggered, slow) ->
        # the boss walks over to a desk to deliver it. Waiting agents keep their original ask.
        last_instr = ((("can you also cover the empty case?", "please add a test for this",
                        "make sure it handles nulls too", "ship it once CI is green",
                        "rename that so it reads clearer")[_blip(idx * 9, 34) % 5])
                      if status == "working" else "Please " + title[0].lower() + title[1:])
        out.append({
            "id": uuid,
            "source": source,
            "scheduled": scheduled,
            "subagents": subagents,
            "subs": len(subagents),
            "shells": demo_shells.get(uuid, []),
            "workflows": workflows,
            "wf_running_agents": sum(w["running"] for w in workflows),
            # a working parent that has helpers/workflows running is NOT typing itself
            # (its own turn ended) -> demonstrates the frozen-desk animation (item 8).
            "self_active": status == "working" and not subagents and not workflows,
            "name": _name_for(uuid),
            "variant": _variant_for(uuid),
            "project": "demo-office",
            "status": status,
            "title": title,
            "preview": title,
            "latest": latest,
            "latest_kind": lkind,
            "last_tool": ["Bash: pytest -q tests/", "Edit: service.py", "Grep: export path", "Read: config.yaml"][idx % 4],
            "last_message": latest if lkind == "assistant" else ("Reviewing the changes about " + title.split()[0].lower()),
            "last_instruction": last_instr,
            "message_count": 12,
            "model": "Opus 4.8" if source == "claude" else None,
            "tokens": (1_240_000 if source == "claude" else None),
            "spend": (3.42 if source == "claude" else None),
            "mtime": now - ago,
            "last_activity_rel": _rel_time(ago),
            "demo": True,
        })
    return out


def demo_detail(uuid):
    for a in demo_agents():
        if a["id"] == uuid:
            a = dict(a)
            a.update({
                "task_full": a["title"],
                "latest_response": "This is a demo worker. Run without --demo to see your real agents.\n\nI'd start by mapping the relevant modules, then make the change incrementally and verify with a quick test.",
                "latest_tool": {"name": "Shell", "detail": "python -m pytest -v"},
                "timeline": [
                    {"role": "user", "text": a["title"], "tools": []},
                    {"role": "assistant", "text": "Let me explore the codebase first.", "tools": [{"name": "Grep", "detail": "export"}]},
                    {"role": "assistant", "text": "Found the relevant module. Making the change now.", "tools": [{"name": "StrReplace", "detail": "service.py"}]},
                ],
                "transcript_path": "(demo - no file)",
            })
            return a
    return None


# --------------------------------------------------------------------------------------
# Frontend (single embedded HTML/JS/CSS page)
# --------------------------------------------------------------------------------------

PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Agent Office</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Press+Start+2P&display=swap" rel="stylesheet">
<style>
  :root{
    --gb-darkest:#0f380f; --gb-dark:#306230; --gb-light:#8bac0f; --gb-lightest:#9bbc0f;
    --shell:#c4bfb4; --shell-dark:#9a958b;
    /* high-contrast greyscale for readable text panels (tooltip + detail) */
    --panel:#1c1e24; --panel2:#26282f; --panel-line:#3a3d46;
    --ink-hi:#f4f5f7; --ink-mid:#c4c7cf; --ink-lo:#8b8f99;
    --card:#f2f2f4; --card-line:#d4d5da; --card-ink:#1c1e24; --card-ink-lo:#5b5e68;
  }
  *{box-sizing:border-box;}
  html,body{margin:0;height:100%;background:#1b1f17;color:var(--gb-darkest);
    font-family:'Press Start 2P',ui-monospace,Menlo,Consolas,monospace;}
  body{display:flex;align-items:center;justify-content:center;padding:18px;}
  #shell{background:var(--shell);border-radius:14px 14px 42px 14px;padding:18px 18px 26px;
    box-shadow:0 14px 40px rgba(0,0,0,.55), inset 0 2px 0 #e8e4da, inset 0 -3px 0 var(--shell-dark);
    width:min(960px,96vw);}
  #brand{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;
    font-size:11px;color:#5a564d;letter-spacing:1px;}
  #brand .dot{display:inline-block;width:9px;height:9px;border-radius:50%;background:#7a1717;
    box-shadow:0 0 6px #d33;margin-right:8px;vertical-align:middle;}
  #brand #celebrate,#brand #whip,#brand #sound,#brand #filter,#brand #names{font-family:inherit;font-size:9px;letter-spacing:1px;color:#e8e8ea;
    background:#3a3a40;border:1px solid #54545c;border-radius:5px;padding:5px 11px;cursor:pointer;}
  #brand #celebrate:hover,#brand #whip:hover,#brand #sound:hover,#brand #filter:hover,#brand #names:hover{background:#4a4a52;color:#fff;}
  #brand #celebrate:active,#brand #whip:active,#brand #sound:active,#brand #filter:active,#brand #names:active{transform:translateY(1px);}
  #brand #sound,#brand #filter,#brand #names,#brand #whip{margin-left:8px;}
  #brand #sound.off,#brand #filter.off{color:#8a8a90;}
  #brand #filter.on{background:#2f5fb0;border-color:#3f6fc0;color:#fff;}
  #screenwrap{background:#22281a;border-radius:10px;padding:12px;
    box-shadow:inset 0 0 0 3px #20240f, inset 0 0 22px rgba(0,0,0,.6);}
  #matrix{display:flex;align-items:center;gap:8px;justify-content:center;margin-bottom:8px;
    font-size:7px;letter-spacing:2px;color:#6f6a78;}
  #matrix .ln{height:3px;flex:1;max-width:120px;border-radius:2px;}
  #matrix .l1{background:linear-gradient(90deg,#7a1f5a,#1f3f7a);}
  #matrix .l2{background:linear-gradient(90deg,#1f3f7a,#7a1f5a);}
  #screen{position:relative;width:100%;aspect-ratio:11/9;background:#65748d;
    border-radius:6px;overflow:hidden;}
  canvas{position:absolute;inset:0;width:100%;height:100%;image-rendering:auto;cursor:pointer;}
  #hud{position:absolute;left:0;top:0;display:flex;flex-direction:column;align-items:flex-start;
    gap:4px;padding:6px 8px;font-size:8px;color:#fff;pointer-events:none;}
  #hud .pill{background:rgba(0,0,0,.42);padding:4px 7px;border-radius:4px;}
  #tip{position:absolute;left:8px;bottom:8px;font-size:7px;color:#fff;
    background:rgba(0,0,0,.32);padding:3px 6px;border-radius:4px;pointer-events:none;}
  #nametag{position:absolute;background:var(--panel);
    color:var(--ink-hi);font-size:11px;line-height:1.55;padding:11px 13px;border-radius:7px;
    width:300px;max-width:78%;white-space:normal;word-break:break-word;
    border:1px solid var(--panel-line);
    box-shadow:0 10px 26px rgba(0,0,0,.55);
    max-height:82vh;overflow-y:auto;
    pointer-events:none;display:none;z-index:15;}
  #nametag .nt-name{font-size:13px;color:var(--ink-hi);font-weight:bold;}
  #nametag .nt-badge{display:inline-block;font-size:9px;padding:2px 7px;border-radius:4px;margin-left:7px;vertical-align:middle;}
  #nametag .nt-badge.working{background:#e8eaee;color:#16181d;}
  #nametag .nt-badge.waiting{background:#4a4d56;color:#f4f5f7;}
  .nt-badge.src-cursor,.badge.src-cursor{background:#2b6d84;color:#eaf6fb;}
  .nt-badge.src-claude,.badge.src-claude{background:#d97757;color:#2a1409;}
  .nt-badge.scheduled,.badge.scheduled{background:#2f5fb0;color:#eaf1ff;}
  .nt-badge.workflow,.badge.workflow{background:#6a4fb0;color:#f1eaff;}
  #nametag .nt-meta{font-size:9px;color:var(--ink-lo);margin:6px 0 8px;}
  #nametag .nt-label{font-size:8px;letter-spacing:1px;color:var(--ink-lo);text-transform:uppercase;margin-top:8px;}
  #nametag .nt-text{font-size:11px;color:var(--ink-mid);margin-top:3px;}
  #nametag .nt-hint{font-size:8px;color:var(--ink-lo);margin-top:9px;text-align:right;opacity:.85;}
  #nametag .wf-phase{display:inline-block;padding:1px 5px;border-radius:3px;margin:2px 2px 0 0;font-size:10px;}
  #nametag .wf-phase.done{background:#2f5d3a;color:#dff5e4;}
  #nametag .wf-phase.active{background:#b7791f;color:#fff4dd;}
  #nametag .wf-phase.pending{background:#33363f;color:#9aa0ab;}
  #nametag .wf-sep{color:var(--ink-lo);margin:0 3px;}
  #legend{display:flex;gap:14px;justify-content:center;margin-top:12px;font-size:8px;color:#5a564d;}
  #legend span{display:inline-flex;align-items:center;gap:6px;}
  #legend i{width:10px;height:10px;border-radius:2px;display:inline-block;}

  /* overlay dialog */
  #overlay{position:absolute;inset:0;display:none;align-items:center;justify-content:center;
    background:rgba(15,24,8,.55);padding:14px;z-index:20;}
  #dialog{width:100%;max-width:680px;max-height:100%;background:var(--card);
    border:3px solid var(--panel);border-radius:8px;display:flex;flex-direction:column;
    box-shadow:0 0 0 3px var(--panel-line), 0 18px 40px rgba(0,0,0,.5);overflow:hidden;}
  #dhead{background:var(--panel);color:var(--ink-hi);padding:12px 14px;
    display:flex;justify-content:space-between;align-items:flex-start;gap:8px;}
  #dhead .who{font-size:13px;color:var(--ink-hi);}
  #dhead .sub{font-size:9px;color:var(--ink-mid);margin-top:6px;line-height:1.7;}
  #dhead button{font-family:inherit;background:var(--panel2);color:var(--ink-hi);
    border:1px solid var(--panel-line);border-radius:4px;font-size:9px;padding:5px 8px;cursor:pointer;}
  #dbody{padding:16px;overflow:auto;font-size:11px;line-height:1.85;color:var(--card-ink);}
  #dbody h4{margin:0 0 8px;font-size:10px;color:var(--card-ink-lo);text-transform:uppercase;letter-spacing:1px;}
  #dbody section{margin-bottom:18px;}
  #dbody .box{background:#ffffff;border:1px solid var(--card-line);border-left:3px solid #8b8f99;
    padding:11px 13px;border-radius:4px;white-space:pre-wrap;word-break:break-word;font-size:11px;line-height:1.75;color:var(--card-ink);}
  #dbody .tool{display:inline-block;background:var(--panel);color:var(--ink-hi);
    padding:3px 7px;border-radius:3px;font-size:8px;margin:2px 4px 2px 0;}
  #dbody .turn{font-size:8px;color:var(--card-ink-lo);text-align:center;margin:6px 0;}
  .role-user .box{border-left-color:#3a3d46;background:#ececed;}
  .badge{display:inline-block;font-size:8px;padding:3px 7px;border-radius:3px;}
  .badge.working{background:#e8eaee;color:#16181d;}
  .badge.waiting{background:#4a4d56;color:#f4f5f7;}
  #dfoot{display:flex;flex-wrap:wrap;gap:8px;padding:10px 12px;border-top:1px solid var(--card-line);
    background:#e7e7ea;}
  #dfoot button{flex:1 1 auto;font-family:inherit;font-size:8px;padding:9px 8px;cursor:pointer;
    border:1px solid var(--panel);border-radius:5px;background:var(--panel);color:var(--ink-hi);}
  #dfoot button.ghost{background:#fff;color:var(--card-ink);border-color:var(--card-line);}
  #toast{position:absolute;left:50%;bottom:16px;transform:translateX(-50%);background:var(--panel);
    color:var(--ink-hi);font-size:8px;padding:7px 12px;border-radius:5px;display:none;z-index:30;}
  #empty{position:absolute;inset:0;display:none;flex-direction:column;align-items:center;
    justify-content:center;text-align:center;font-size:9px;color:#1c1e24;padding:24px;line-height:2;}
</style>
</head>
<body>
  <div id="shell">
    <div id="brand"><span><span class="dot"></span>AGENT OFFICE</span><span id="scope"></span><button id="celebrate" title="confetti + everyone dances">CELEBRATE</button><button id="whip" title="crack the whip &mdash; everyone works harder">WHIP</button><button id="sound" title="chime when an agent finishes">&#9834; ON</button><button id="filter" title="hide scheduled / courier agents">&#9993; HIDE</button><button id="names" title="agent name style">NAMES</button><span id="clock"></span></div>
    <div id="screenwrap">
      <div id="matrix"><span class="ln l1"></span>DOT MATRIX WITH STEREO SOUND<span class="ln l2"></span></div>
      <div id="screen">
        <canvas id="cv" width="704" height="576"></canvas>
        <div id="hud">
          <span class="pill" id="hud-work">working: 0</span>
          <span class="pill" id="hud-wait">in kitchen: 0</span>
          <span class="pill" id="hud-beach" style="display:none">on beach: 0</span>
          <span class="pill" id="hud-subs" style="display:none">subagents: 0</span>
          <span class="pill" id="hud-wf" style="display:none">workflows: 0</span>
        </div>
        <div id="tip">click a worker</div>
        <div id="nametag"></div>
        <div id="empty">No agents active in the last <b id="emh">24</b>h.<br/><br/>
          Start a chat in Cursor or Claude Code, or run with <b>--demo</b> to populate the office.</div>
        <div id="overlay">
          <div id="dialog">
            <div id="dhead">
              <div>
                <div class="who" id="d-name"></div>
                <div class="sub" id="d-sub"></div>
              </div>
              <button id="d-x" title="close">X</button>
            </div>
            <div id="dbody"></div>
            <div id="dfoot">
              <button id="d-finish">&#127958; SEND TO BEACH</button>
              <button id="d-open">OPEN TRANSCRIPT FILE (.jsonl)</button>
              <button id="d-copy" class="ghost">COPY SESSION ID</button>
            </div>
          </div>
        </div>
        <div id="toast"></div>
      </div>
    </div>
    <div id="legend">
      <span><i style="background:#1f5d1f"></i>working (at desk)</span>
      <span><i style="background:#7a4a00"></i>waiting (in kitchen)</span>
      <span><i style="background:#2b6d84"></i>Cursor</span>
      <span><i style="background:#d97757"></i>Claude Code</span>
      <span><i style="background:#2f5fb0"></i>scheduled (courier)</span>
      <span><i style="background:#57c2d8"></i>finished (beach)</span>
    </div>
  </div>

<script>
"use strict";
const cv = document.getElementById('cv');
const ctx = cv.getContext('2d');
// Logical drawing size stays 640x576 (all layout/hit-test math uses these), but we
// super-sample the actual backing store so text + art render at much higher
// resolution and scale down crisply instead of being upscaled/blurred (esp. on
// HiDPI / retina screens). SS is chosen from devicePixelRatio, capped for perf.
const W = 704, H = 576;   // 704 = 576*11/9 -> matches #screen aspect-ratio:11/9 (widened so edge desks' dwarves/easels don't clip)
const SS = Math.min(4, Math.max(2, Math.ceil((window.devicePixelRatio||1)*2)));
cv.width = W*SS; cv.height = H*SS;
ctx.imageSmoothingEnabled = false;
// global art scale: characters + desks are drawn larger (about their anchor) so
// the rooms feel filled. ALL hitbox / hover-ring / pick() math multiplies by SC.
const SC = 1.5;
const BUBBLE_MS = 8200;    // speech-bubble lifetime (ms)
const BUBBLE_FADE = 900;   // fade-out tail (ms)
const BOSS_MS = 7200;      // how long the "boss" lingers by a desk delivering a new instruction
// the bottom band is split: KITCHEN (waiting) on the left, BEACH (finished, resting)
// on the right. BEACH_X is the divider; everything to its right is sand + water.
const BEACH_X = Math.round(W*0.60);

// Game Boy palette
const C = { d0:'#0f380f', d1:'#306230', d2:'#8bac0f', d3:'#9bbc0f', floor:'#94ad42', floor2:'#8aa53b' };
// look variants -- bright, cheerful, diverse shirt colours (no gloomy navy crowd)
const SHIRTS = ['#e0533b','#2f93d8','#37b56c','#e8a72e','#8c5fd6','#22b9b9','#e673a8','#6aa72f',
                '#d83b5b','#3f74d6','#ee8f2c','#16a0c0','#c84fc0','#5bc05b','#f0b429','#ff7a4d'];
const HAIR   = ['#3a2a14','#1a1410','#5a3010','#6a6a6a','#2a1840','#403018','#7a3010','#c89020','#d8d8d8','#1a3a5a'];
const SKIN   = ['#f0d2a8','#e6b98a','#d2a070','#f6dcc0','#c08860','#ecc89c','#b87a52','#fae0c2'];
const ACCCOL = ['#1b1b1b','#d2452f','#2f74d6','#e8a72e','#22b9b9','#8c5fd6'];

// rich, full-colour scene palette (the screen is no longer monochrome green)
const PAL = {
  sky:'#bfe9f5', skyTop:'#9ad8ee', cloud:'#ffffff',
  bldg1:'#7c87b0', bldg2:'#9aa4c6', bldgWin:'#dfeefa',
  nightTop:'#171436', nightBot:'#46315f', star:'#ffffff', moon:'#f3eecf',
  bldgN1:'#211c40', bldgN2:'#2c2752', litWin:'#ffd36b',
  wall:'#efe6d2', trim:'#cdbf9c', base:'#b09a72',
  ofloor:'#6f7f98', ofloor2:'#65748d',
  kfloor:'#ecdcb6', kfloor2:'#e1cfa4',
  wood:'#b27a43', woodHi:'#c68f55', woodDk:'#7d4f2a',
  metal:'#aeb9c2', metalDk:'#7a8893', steel:'#cdd6dd',
  fridge:'#e3eaef', fridgeDk:'#c5cfd6',
  cabinet:'#3f5266', cabinetTop:'#d9c8a6',
  leaf:'#46a04f', leafHi:'#69bf68', leafDk:'#2f7a3c', pot:'#c4693a', potDk:'#9a4f28',
  board:'#2c3b37', chalk:'#ece6d2', chalkY:'#e4c558',
  monitor:'#2b2b34', monitorLip:'#16161c', screen:'#7fd3e0',
  paper:'#ffffff', ink:'#26282e', outline:'#241c2b', chairW:'#6a5240',
  pink:'#dd8aa8', red:'#d2452f', yellow:'#e3b021', orange:'#e07a2f',
  mugA:'#d9534f', mugB:'#4f86d9', mugC:'#e8b84b',
};

// derive a fun, deterministic appearance from the agent id.
// NOTE: hash() is unsigned 32-bit, so we MUST use unsigned shifts (>>>) here -
// a signed >> would go negative for high hashes and yield undefined colours.
function featuresFor(id){
  const h = hash(id);
  return {
    skin: SKIN[(h>>>0) % SKIN.length],
    hair: HAIR[(h>>>3) % HAIR.length],
    shirt: SHIRTS[(h>>>6) % SHIRTS.length],
    hairStyle: (h>>>9) % 8,        // 0 flat 1 spiky 2 bald 3 bun 4 mop 5 mohawk 6 side-part 7 afro
    acc: (h>>>12) % 6,             // 0 none 1 glasses 2 cap 3 headphones 4 beanie 5 antenna
    accCol: ACCCOL[(h>>>15) % ACCCOL.length],
    pants: ['#3a4654','#4a3a2e','#2f4250','#5a4326','#3a3a44','#2f4a38'][(h>>>23) % 6],
    speed: 0.55 + ((h>>>18) % 5) * 0.14,   // per-person walk speed
    big: ((h>>>21) & 1) === 1,             // chunkier body
    female: ((h>>>16) & 1) === 1,          // ~half women, stable by id
    femStyle: (h>>>17) % 4,                // 0 long  1 ponytail  2 bun+bow  3 top-knot
    outfit: (h>>>19) % 5,                  // 0 plain 1 zip 2 stripe 3 v-neck 4 hoodie
    lanyard: ((h>>>25) % 3) === 0,         // ~1/3 wear an office badge on a lanyard
  };
}
// a small outfit detail + soft left-side sheen, shared by every sprite so the crowd
// looks varied. cx = torso centre, topY = torso top, halfW = half the torso width.
function torsoDetail(cx, topY, halfW, h, sh, f){
  if(f.messenger) return;                                        // couriers keep their plain uniform + badge
  px(cx-halfW+1, topY+2, 1, h-4, 'rgba(255,255,255,.10)');       // subtle sheen down the left
  if(f.lanyard){                                                 // office badge on a lanyard (overrides other detail)
    px(cx-3,topY,1,5,'#33343e'); px(cx+3,topY,1,5,'#33343e');    // cords from the shoulders
    px(cx-2,topY+5,5,5,'#eef0f4'); px(cx-2,topY+5,5,1,'#ffffff'); // badge card
    px(cx-1,topY+6,3,1,'#8f98a4'); px(cx-1,topY+8,2,1,'#8f98a4'); // badge text lines
    return;
  }
  const dk=shade(sh,-.26), lt=shade(sh,.26);
  if(f.outfit===1){ px(cx, topY+1, 1, h-2, dk); px(cx-1, topY+3, 3,1, dk); px(cx-1, topY+7, 3,1, dk); }     // zip placket
  else if(f.outfit===2){ px(cx-halfW+2, topY+Math.round(h*0.45), (halfW-2)*2, 2, lt); }                     // chest stripe
  else if(f.outfit===3){ px(cx-2, topY, 4,2, dk); px(cx-1, topY+2, 2,1, dk); }                              // v-neck
  else if(f.outfit===4){ px(cx-4, topY, 8,2, dk); px(cx-2, topY+2, 1,4, PAL.paper); px(cx+1, topY+2, 1,4, PAL.paper); } // hoodie
}

// Scheduled / automated agents (cron, daily monitors, etc.) wear a courier uniform:
// one solid color from shirt to cap, so a whole squad of them reads instantly as
// "not a human-driven chat" instead of blending into the office crowd.
const MESSENGER_COL = '#2f5fb0';
function featuresForAgent(a){
  const f = featuresFor((a && a.id) || 'x');
  if(a && a.scheduled){
    f.messenger = true;
    f.shirt = MESSENGER_COL;    // uniform shirt
    f.acc = 2;                  // cap
    f.accCol = MESSENGER_COL;   // cap matches the uniform
    if(f.hairStyle === 2) f.hairStyle = 0;   // a little hair peeks out under a bald courier's cap
  }
  return f;
}

let agents = [];      // raw from server
let people = [];      // live sprites with positions
let deskSlots = [];   // fixed office desks (always drawn; some hold a worker)
let helperHits = [];  // per-frame hover regions for the subagent dwarves
let workflowHits = []; // per-frame hover regions for the workflow tents
let shellHits = [];    // per-frame hover regions for the open-shell terminal windows
let bubbleAnchors = []; // per-frame: bubbles to draw as a screen-space overlay
let vendSlots = [];   // per-frame click rects for the vending-machine drink slots
let vendDrops = {};   // slot idx -> {start,col,fromX,fromY} while a can is dropping/resting
let deskAssign = {};  // agent id -> stable desk slot index (kept across refreshes)
let seatAssign = {};  // agent id -> stable kitchen seat index
let beachAssign = {}; // agent id -> stable beach spot index (finished agents)
let hover = null;
let detailCache = {};
let WINDOW_HOURS = 24;
let confetti = [];          // celebration particles (capped, auto-expire)
let whipFx = [];            // whip-crack particles: one lash line + shock streaks (capped, auto-expire)
let prevStatus = null;      // id -> last status; null until the first poll (no false fires)
let msgSeen = null;   // id -> last assistant `latest` seen (desk agents); null until first poll
let subMsgSeen = {};  // subId -> last change-token (subagents + workflow subs)
let subBubbles = {};  // subId -> {text,start,until} active dwarf bubbles
let instrSeen = null; // id -> last user instruction seen (working agents); null until first poll
let bossVisits = {};  // id -> {text,start,until} a supervisor delivering a new instruction at a desk
let hideScheduled = (localStorage.getItem('office_hide_scheduled')==='on');  // filter couriers (default off)
// agents the user has marked "finished" -- they go rest on the beach until unmarked.
// User-controlled and sticky (persisted), independent of the working/waiting status.
let finishedIds = new Set(JSON.parse(localStorage.getItem('office_finished')||'[]'));
function saveFinished(){ localStorage.setItem('office_finished', JSON.stringify([...finishedIds])); }

// ---- ambient random events (pure scenery; never clickable / never hit-tested) ----
// One dog OR cat OR agent-relocate fires every 30-60s, scheduled inside tick() off
// the same rAF clock so it can't drift like a stray setInterval. These critters live
// ONLY in the animation layer: pick(), hover, confetti and polling never see them.
let amb = { dog:null, cat:null, plane:null };   // at most one of each on screen
let nextEventAt = 0;                // performance.now() ms of the next event
let lastEventType = null;           // avoid firing the same type twice in a row
let nextPlaneAt = 0;                // performance.now() ms of the next window fly-by

// stable kitchen floor spots (hand-placed, ≥~44px apart, CLEAR of the fridge/counter,
// the lounge table+poufs, the couch, the REFRESH! machine and the wall signs). Used
// for waiter scatter AND as relocate targets so agents never stack.
const KSPOTS = [
  [95,432],[185,428],[280,433],[360,429],           // band in front of the counter (kept left of BEACH_X)
  [60,460],[125,460],[230,470],[315,466],           // mid floor (between fridge and beach)
  [255,548],[320,545],[365,540]                     // front-centre gap (between table and beach)
];

// stable BEACH rest spots for finished agents (all in the right band, x > BEACH_X,
// clear of the water strip on the far-right edge, the umbrella and the napping bear).
const BSPOTS = [
  [438,520],[510,532],[464,478],
  [556,502],[590,458],[534,548]
];

// ---- layout regions (in canvas px) ----
function layout(){
  const kitchenH = Math.round(H*0.40);
  return {
    office: {x:0, y:0, w:W, h:H-kitchenH},
    kitchen:{x:0, y:H-kitchenH, w:W, h:kitchenH},
    kitchenTop: H-kitchenH
  };
}

// assign stable positions: desks for workers (grid), wander targets for waiters
function rebuild(){
  const L = layout();
  // when the "hide scheduled" filter is on, courier (scheduled) agents don't get a
  // desk or kitchen spot -- they walk off-screen instead (handled at the end).
  const active = hideScheduled ? agents.filter(a=>!a.scheduled) : agents;
  // agents marked "finished" go to the beach regardless of working/waiting status;
  // everyone else is placed at desks (working) or the kitchen (waiting) as before.
  const beachers = active.filter(a=>finishedIds.has(a.id));
  const rest = active.filter(a=>!finishedIds.has(a.id));
  const workers = rest.filter(a=>a.status==='working');
  const waiters = rest.filter(a=>a.status!=='working');

  const next = [];
  const prevById = {}; people.forEach(p=>prevById[p.id]=p);

  // --- STABLE position assignment ---------------------------------------
  // Each agent keeps the SAME desk slot / kitchen seat across refreshes, keyed
  // by its id. When an agent changes role (kitchen<->desk) it KEEPS its old x/y
  // and walks/glides to the new target instead of teleporting.
  const workerIds = new Set(workers.map(a=>a.id));
  const waiterIds = new Set(waiters.map(a=>a.id));
  const beacherIds = new Set(beachers.map(a=>a.id));
  // release assignments for agents that left or switched role
  Object.keys(deskAssign).forEach(id=>{ if(!workerIds.has(id)) delete deskAssign[id]; });
  Object.keys(seatAssign).forEach(id=>{ if(!waiterIds.has(id)) delete seatAssign[id]; });
  Object.keys(beachAssign).forEach(id=>{ if(!beacherIds.has(id)) delete beachAssign[id]; });
  // give brand-new workers the lowest free desk index (stable thereafter)
  const usedSlots = new Set(Object.values(deskAssign));
  workers.forEach(a=>{ if(deskAssign[a.id]==null){ let i=0; while(usedSlots.has(i)) i++; deskAssign[a.id]=i; usedSlots.add(i); } });
  const usedSeats = new Set(Object.values(seatAssign));
  waiters.forEach(a=>{ if(seatAssign[a.id]==null){ let i=0; while(usedSeats.has(i)) i++; seatAssign[a.id]=i; usedSeats.add(i); } });
  const usedBeach = new Set(Object.values(beachAssign));
  beachers.forEach(a=>{ if(beachAssign[a.id]==null){ let i=0; while(usedBeach.has(i)) i++; beachAssign[a.id]=i; usedBeach.add(i); } });

  // a fixed office layout of desks that is ALWAYS drawn (so the room looks
  // furnished even when nobody is working). Sized to fit the highest used slot.
  const cols = 3;
  const maxSlot = Object.values(deskAssign).reduce((m,v)=>Math.max(m,v), -1);
  const need = Math.max(6, Math.ceil((maxSlot+1)/cols)*cols);
  // tighter grid sized for the bigger (SC) desks so the office reads as full
  const left = 140, right = W-140, top = WALL_H+48, rowH = 128;   // wider insets (edge desks fit their dwarves/easels) + taller rows (more gap between the 2 rows)
  deskSlots = [];
  for(let i=0;i<need;i++){
    const c=i%cols, r=Math.floor(i/cols);
    const x = left + c*((right-left)/(cols-1));
    const y = top + r*rowH;
    deskSlots.push({x, y, worker:null});
  }
  workers.forEach(a=>{
    const old = prevById[a.id];
    const slot = deskSlots[deskAssign[a.id]];
    // already seated at THIS desk? stay seated. Otherwise walk in and then sit.
    const sameSeat = old && old.kind==='work' && old.seated &&
                     old.deskX===slot.x && old.deskY===slot.y;
    const person = Object.assign(old||{}, {
      id:a.id, agent:a, kind:'work',
      // keep current position so a kitchen->desk move animates as a walk
      x: old? old.x : slot.x, y: old? old.y : slot.y,
      deskX:slot.x, deskY:slot.y, vx:0, vy:0,
      seated: old ? !!sameSeat : true,   // fresh load: just sit; transitions walk
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    });
    slot.worker = person;
    next.push(person);
  });

  // kitchen: scatter waiting agents NATURALLY across the open floor (not a grid).
  // Each agent keeps a stable anchor (by seatAssign index) plus a small deterministic
  // jitter from hash(id). The anchor list is hand-placed (≥~52px apart, with a few
  // loose pairs) and stays CLEAR of the fridge/counter (top-left band), the COFFEE
  // and DO GOOD WORK signs, the REFRESH! machine (right), and the couch + table.
  const k = L.kitchen;
  // hand-placed scatter across the OPEN floor (KSPOTS), clear of the lounge table
  // (left), the couch + side table (right), the counter/fridge (back wall), the
  // REFRESH! machine and the DO GOOD WORK poster. Spaced ≥~44px for hovering.
  waiters.forEach(a=>{
    const old = prevById[a.id];
    const idx = seatAssign[a.id];
    const base = KSPOTS[idx % KSPOTS.length];
    const ring = Math.floor(idx / KSPOTS.length);   // overflow agents nudge outward
    const hsh = hash(a.id);
    const jx = ((hsh>>>3) % 9) - 4;                  // -4..+4 deterministic jitter
    const jy = ((hsh>>>9) % 9) - 4;
    // a relocated agent (ambient event) keeps its event-chosen spot across refreshes
    // instead of snapping back to its stable anchor.
    const home = (old && old.relocHome) ? old.relocHome
               : { x: base[0] + jx + ring*16, y: base[1] + jy + ring*14 };
    // walk in if new or arriving from another zone (desk/beach); otherwise keep mode
    const cameFromElsewhere = !old || old.kind!=='wait';
    next.push(Object.assign(old||{}, {
      id:a.id, agent:a, kind:'wait',
      // brand-new agents enter from the room doorway (top-center) and walk to
      // their spot; agents leaving a desk keep their office position and walk down.
      x: old? old.x : W*0.5, y: old? old.y : k.y+8,
      home, vx:0, vy:0,
      mode: cameFromElsewhere ? 'walk' : old.mode,
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    }));
  });

  // pair each waiting agent with its nearest kitchen neighbour (by anchor) so they can
  // occasionally turn and chat. Recomputed every poll, so it tracks relocations.
  const waitList = next.filter(p=>p.kind==='wait');
  for(const p of waitList){
    let bx=null, bd=80;                       // only pair within ~80px
    for(const q of waitList){ if(q===p) continue;
      const d=Math.hypot(p.home.x-q.home.x, p.home.y-q.home.y);
      if(d<bd){ bd=d; bx=q.home.x; }
    }
    p.talkX = bx;   // x of the neighbour to face while chatting (null = nobody near)
  }

  // beach: finished agents walk over to the sand and chill until you unmark them.
  beachers.forEach(a=>{
    const old = prevById[a.id];
    const idx = beachAssign[a.id];
    const base = BSPOTS[idx % BSPOTS.length];
    const ring = Math.floor(idx / BSPOTS.length);        // overflow nudges outward
    const hsh = hash(a.id);
    const jx = ((hsh>>>4) % 7) - 3;
    const jy = ((hsh>>>10) % 7) - 3;
    const home = { x: base[0] + jx + ring*14, y: base[1] + jy + ring*12 };
    const cameFromElsewhere = !old || old.kind!=='beach';
    next.push(Object.assign(old||{}, {
      id:a.id, agent:a, kind:'beach',
      x: old? old.x : W*0.5, y: old? old.y : k.y+8,
      home, vx:0, vy:0,
      mode: cameFromElsewhere ? 'walk' : old.mode,
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    }));
  });

  // filtered-out scheduled agents: if they were on screen, keep them around just long
  // enough to walk off the bottom edge (a tidy "exit"); ones that were never visible
  // are simply omitted. Turning the filter back off re-adds them via the normal
  // worker/kitchen assignment above, so they walk back in from where they left.
  if(hideScheduled){
    agents.filter(a=>a.scheduled).forEach(a=>{
      const old = prevById[a.id];
      if(!old) return;
      next.push(Object.assign(old, {
        id:a.id, agent:a, kind:'exit', mode:'walk', seated:false,
        // sprites are drawn scaled x SC about their anchor, so the body extends
        // ~50px ABOVE the anchor -- push the target well below H so the WHOLE
        // sprite (cap included) clears the bottom edge, not just the feet.
        exitX: W*0.5, exitY: H + 70*SC,
        vx:0, vy:0,
        seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
      }));
    });
  }

  people = next;
  document.getElementById('hud-work').textContent = 'working: '+workers.length;
  document.getElementById('hud-wait').textContent = 'in kitchen: '+waiters.length;
  const hb=document.getElementById('hud-beach');
  hb.textContent = 'on beach: '+beachers.length;
  hb.style.display = beachers.length ? '' : 'none';   // only show the pill when in use
  // running subagents + active workflow runs across all agents (only shown when in use)
  const subCount = agents.reduce((n,a)=>n+(a.subs||0)+(a.wf_running_agents||0),0);
  const wfCount  = agents.reduce((n,a)=>n+((a.workflows||[]).length),0);
  const hs=document.getElementById('hud-subs');
  hs.textContent='subagents: '+subCount; hs.style.display = subCount ? '' : 'none';
  const hw=document.getElementById('hud-wf');
  hw.textContent='workflows: '+wfCount; hw.style.display = wfCount ? '' : 'none';
  document.getElementById('empty').style.display = agents.length? 'none':'flex';
}

function hash(s){let h=0;for(let i=0;i<s.length;i++)h=(h*31+s.charCodeAt(i))&0xffffffff;return h>>>0;}

// ---- agent name styles (chosen in the header; names are stable per agent id) ----
const NAME_SETS = {
  magical: { label:'MAGICAL', first:["Pip","Willow","Clover","Bun","Maple","Sprout","Waffle","Biscuit","Poppy","Mochi","Pebble","Fern","Cricket","Marshmallow","Pumpkin","Honey","Acorn","Noodle","Pickle","Sunny","Berry","Tofu","Dandelion","Bramble","Hazel","Olive","Tansy","Muffin","Peaches","Juniper"],
    last:["Sunbeam","Marshmallow","Buttercup","Honeydew","Pumpkinpatch","Snugglebee","Cloudberry","Dewdrop","Meadowlight","Gigglesworth","Cottontail","Brightbloom","Mossypaws","Tinkerwhisk","Sugarplum","Pebblebrook","Willowwisp","Honeycomb","Berrybramble","Twinkletoes","Mapleshade","Cuddleburrow","Dapplewood","Snickerdoodle","Fernwhistle"] },
  israeli: { label:'ISRAELI', first:["Yossi","Noa","Avi","Shira","Tal","Yael","Eitan","Dana","Gal","Amit","Ronen","Ori","Roni","Maya","Itai","Nadav","Liron","Chen","Bar","Shani","Adi","Yarden","Omer","Hila","Lior","Guy","Tomer","Inbal","Doron","Sivan","Ziv","Nir","Gil","Rotem","Yuval","Moshe","Sagi","Dvir","Ayelet","Almog","Oren","Carin-Belle"],
    last:["Cohen","Levi","Mizrahi","Peretz","Biton","Dahan","Avraham","Friedman","Katz","Azoulay","Ben-David","Shapira","Bar-On","Malka","Gabai","Segal","Hadad","Barak","Regev","Ohayon","Amar","Klein","Ashkenazi","Elbaz","Tzur","Sasson","Vaknin","Nachmani","Aloni","Shalev","Yomtov","Feder"] },
  dev: { label:'DEV', first:["Segfault","Captain","Null","Sudo","Regex","Commit","Legacy","Hotfix","Boolean","Async","Cache","Merge","Kernel","Turbo","Lazy","Quantum","Rusty","Vim","Recursive","Undefined","Docker","Bcrypt"],
    last:["Overflow","Pointer","Deploy","Nullson","Bugsley","Pushington","Bytewise","Loopy","Debugger","Refactor","O'Reilly","McStacktrace","von Merge","Yeetson","Hashimoto","Snippets","Ramsson","Kernelson","Rebase","Semicolon","Payload","Heapman"] },
  robots: { label:'ROBOTS', first:["Unit","Servo","Chip","Proto","Mecha","Robo","Nano","Giga","Auto","Cy","Zeta","Beep","Clank","Data","Pixel","Opti","Turbo","Volt","Gizmo","Sprocket","Bolt","Widget"],
    last:["Boopmatic","Cogsworth","9000","Mk-II","Whirrley","Sparkplug","Bleepson","Databyte","Clankworth","Buzzbot","Gearhart","Pixelface","Ohmson","Widgeteer","von Circuit","3000","Beepson","Clankstein","Rustbucket","Boltsworth","Zappenheim","Motoroni"] },
};
const NAME_ORDER = ['magical','israeli','dev','robots'];
let nameStyle = localStorage.getItem('office_names'); if(!NAME_SETS[nameStyle]) nameStyle='israeli';
function nameFor(id){ const s=NAME_SETS[nameStyle]||NAME_SETS.magical; const h=hash(id||'x');
  return s.first[h % s.first.length]+' '+s.last[(h>>>8) % s.last.length]; }

// ---- drawing helpers ----
function px(x,y,w,h,col){ctx.fillStyle=col;ctx.fillRect(x|0,y|0,w|0,h|0);}
// scale subsequent drawing about an anchor point (used to enlarge sprites/desks)
function scaleAbout(ax,ay,s){ ctx.translate(ax,ay); ctx.scale(s,s); ctx.translate(-ax,-ay); }

// shade a #rrggbb colour: f>0 lightens toward white, f<0 darkens toward black.
// used for soft, cohesive shading on shirts/hair/furniture (no flat fills).
const _shadeCache={};
function shade(hex, f){
  const key=hex+'|'+f; if(_shadeCache[key]) return _shadeCache[key];
  let n=parseInt(hex.slice(1),16); let r=(n>>16)&255,g=(n>>8)&255,b=n&255;
  if(f>=0){ r+=(255-r)*f; g+=(255-g)*f; b+=(255-b)*f; } else { r*=(1+f); g*=(1+f); b*=(1+f); }
  return _shadeCache[key]='rgb('+(r|0)+','+(g|0)+','+(b|0)+')';
}
// a small white speech bubble with a pink heart (cozy kitchen vibe)
function heartBubble(x,y){
  px(x-8,y-7,18,12,PAL.paper); px(x-8,y-7,18,1,'#ececf2'); px(x-8,y+4,18,1,'#d6d6de');
  px(x-9,y-5,1,8,PAL.paper); px(x+10,y-5,1,8,PAL.paper);
  px(x-3,y+5,3,3,PAL.paper); px(x-2,y+8,2,2,PAL.paper);     // little tail
  px(x-3,y-4,3,3,PAL.pink); px(x+1,y-4,3,3,PAL.pink);        // heart lobes
  px(x-4,y-2,9,2,PAL.pink); px(x-2,y,5,2,PAL.pink); px(x,y+2,1,1,PAL.pink);
}
// a small speech bubble with 1-3 chat dots (kitchen small-talk)
function talkBubble(x,y,n){
  px(x-8,y-7,18,11,PAL.paper); px(x-8,y-7,18,1,'#ececf2'); px(x-8,y+3,18,1,'#d6d6de');
  px(x-9,y-5,1,7,PAL.paper); px(x+10,y-5,1,7,PAL.paper);
  px(x-3,y+4,3,3,PAL.paper); px(x-2,y+7,2,2,PAL.paper);     // little tail
  const dk='#8a8f9c';
  for(let i=0;i<n;i++) px(x-5+i*5,y-2,3,3,dk);              // 1..3 talk dots
}

const WALL_H = 78;
const WIN = { x:20, y:8, w:Math.round(W*0.36), h:WALL_H-20 };  // sky-window glass rect (drawWindow args)

function drawFloor(){
  const L=layout(), oh=L.office.h;
  // office floor: cohesive tiles with grout lines + gentle per-tile shading
  for(let ty=WALL_H; ty<oh; ty+=24){
    for(let tx=0; tx<W; tx+=24){
      const alt=((tx/24+Math.floor((ty-WALL_H)/24))&1);
      px(tx,ty,24,24, alt?PAL.ofloor:PAL.ofloor2);
      px(tx,ty,24,1,'rgba(255,255,255,.05)');      // tile top highlight
      px(tx,ty+23,24,1,'rgba(0,0,0,.10)');          // grout (bottom)
      px(tx+23,ty,1,24,'rgba(0,0,0,.08)');          // grout (right)
    }
  }
  px(0,WALL_H,W,26,'rgba(255,255,255,.04)');         // soft daylight band near the windows
  // back wall + picture-rail + skirting
  px(0,0,W,WALL_H,PAL.wall); px(0,0,W,10,shade(PAL.wall,.05));
  px(0,WALL_H-8,W,2,shade(PAL.wall,-.06)); px(0,WALL_H-5,W,3,PAL.trim); px(0,WALL_H-2,W,2,PAL.base);
  const winW = Math.round(W*0.36);   // slimmer window -> room for the wider board
  drawWindow(20, 8, winW, WALL_H-20);
  const wl = wallRowLayout();
  drawWallDecor(wl.boardX, 6, wl.clkL, wl.shfL);

  // kitchen floor (warm tiles)
  for(let y=L.kitchenTop;y<H;y+=20){
    for(let x=0;x<W;x+=20){ px(x,y,20,20, ((x/20+y/20)&1)?PAL.kfloor:PAL.kfloor2); }
  }
  // divider skirting between rooms
  px(0,L.kitchenTop-4,W,4,PAL.base); px(0,L.kitchenTop,W,2,'rgba(0,0,0,.16)');

  drawOfficeProps();
  drawKitchenProps();
}

// ---- furniture / decor helpers ----
function chair(x,y,col){ px(x,y,12,5,col); px(x,y-9,2,9,col); px(x+10,y-9,2,9,col); px(x,y-11,12,3,col); }
function woodTable(x,y,w,h){ px(x,y,w,h,PAL.wood); px(x,y,w,5,PAL.woodHi); px(x+3,y+9,w-6,2,PAL.woodDk);
  px(x-2,y+h-2,5,9,PAL.woodDk); px(x+w-3,y+h-2,5,9,PAL.woodDk); }
function laptop(x,y){ px(x,y,18,12,PAL.monitorLip); px(x+1,y+1,16,8,PAL.screen); px(x-1,y+11,20,3,PAL.metal); }
function mug(x,y,col){ px(x,y,7,7,PAL.paper); px(x+1,y+1,5,5,col); px(x+7,y+2,2,3,PAL.paper); }
// a single tapered leaf/frond: rises `h` px from (bx,baseY), drifting `dx` sideways,
// with a dark edge outline and a lighter inner stripe so it reads hand-drawn.
function blade(bx, baseY, h, dx, col){
  const hi=shade(col,.30), lo=shade(col,-.34);
  for(let i=0;i<h;i++){
    const t=i/h, cx=Math.round(bx+dx*t);
    const w=(i<h-4)?3:(i<h-2)?2:1;            // taper to a point
    px(cx-1, baseY-i, 1,1, lo);                // dark left edge
    px(cx,   baseY-i, w,1, col);               // leaf body
    px(cx+w-1, baseY-i, 1,1, lo);              // dark right edge
    if(i%2===0) px(cx, baseY-i, 1,1, hi);      // inner highlight speckle
  }
}
function smallPlant(x,y){
  const cx=x+6;
  ctx.fillStyle='rgba(0,0,0,.14)'; ctx.beginPath(); ctx.ellipse(cx,y+9,10,3,0,0,Math.PI*2); ctx.fill();
  // tapered little pot
  px(x,y,12,3,shade(PAL.pot,.16)); px(x+1,y+3,10,3,PAL.pot); px(x+2,y+6,8,3,shade(PAL.pot,-.10));
  px(x+1,y+3,2,5,shade(PAL.pot,.18)); px(x+1,y+2,10,1,PAL.potDk);
  // a few short blades
  [[-4,12,-5],[-1,17,-1],[2,15,2],[5,11,5]].forEach((d,i)=> blade(cx+d[0], y+3, d[1], d[2], i%2?PAL.leaf:PAL.leafDk));
}
function bigPlant(x,y){
  const cx=x+9;
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(cx,y+20,16,4,0,0,Math.PI*2); ctx.fill();
  // tapered terracotta pot with a rim + soil line
  px(x-1,y,20,5,shade(PAL.pot,.18));                                   // rim (widest)
  px(x+1,y+5,16,5,PAL.pot); px(x+2,y+10,14,5,PAL.pot); px(x+3,y+15,12,4,shade(PAL.pot,-.10)); // tapered body
  px(x+2,y+5,3,13,shade(PAL.pot,.16)); px(x+12,y+6,3,12,shade(PAL.pot,-.14)); // hi / shade
  px(x+1,y+4,16,2,PAL.potDk);                                          // soil line
  // a fan of fern/snake-plant blades of varied height
  [[-9,22,-12],[-6,32,-8],[-3,42,-4],[0,48,0],[3,42,4],[6,32,8],[9,24,12]]
    .forEach((d,i)=> blade(cx+d[0], y+5, d[1], d[2], (i===3)?PAL.leaf:(i%2?PAL.leaf:PAL.leafDk)));
}
function couch(x,y){ px(x,y,70,22,PAL.cabinet); px(x,y-10,70,12,'#4f6377');
  px(x-6,y-10,8,30,PAL.cabinet); px(x+68,y-10,8,30,PAL.cabinet);
  px(x+4,y+2,28,9,'#5a6e82'); px(x+38,y+2,28,9,'#5a6e82'); }
// a tall blue dining chair with a curved padded back (seen from the side of a table)
function blueChair(x,y){
  const c='#3f64c0', cd='#2f4a96', ch='#5a7ed8';
  px(x+2,y+2,2,12,'#1f1f24'); px(x+12,y+2,2,12,'#1f1f24');     // legs
  ro(x,y-2,16,6,cd); px(x+1,y-2,14,2,c);                        // seat
  ro(x+1,y-17,14,16,c); px(x+2,y-16,12,3,ch); px(x+2,y-4,12,2,cd); // curved back
  px(x+2,y-16,2,15,ch);                                         // left rail sheen
}
// a cute sleeping bear-style mascot lounging on the couch (pure scenery, not an agent)
function bearMascot(x,y){
  const fur='#4a6b88', furDk='#3a5572', furHi='#5f82a0', belly='#efe2c2', pad='#dcc99e';
  function el(cx,cy,rx,ry,col){ ctx.fillStyle=col; ctx.beginPath(); ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2); ctx.fill(); }
  el(x,y+13,9,6,furDk); el(x+18,y+13,9,6,furDk);               // feet
  el(x+3,y+14,4,3,pad); el(x+15,y+14,4,3,pad);                 // foot pads
  el(x+9,y-4,21,20,fur);                                       // body
  el(x+9,y-1,13,14,belly);                                     // cream belly
  el(x-8,y-2,7,9,fur); el(x+26,y-2,7,9,fur);                   // arms
  el(x-4,y-24,5,5,fur); el(x+22,y-24,5,5,fur);                 // ears
  el(x+9,y-19,15,13,fur);                                      // head
  el(x-3,y-24,3,3,furHi); el(x+9,y-26,5,3,furHi);              // head sheen
  // sleeping content face: two closed (downward-arc) eyes + a soft smile
  px(x+1,y-20,5,1,PAL.outline); px(x+1,y-19,1,1,PAL.outline); px(x+5,y-19,1,1,PAL.outline);
  px(x+12,y-20,5,1,PAL.outline); px(x+12,y-19,1,1,PAL.outline); px(x+16,y-19,1,1,PAL.outline);
  px(x+6,y-14,6,1,PAL.outline); px(x+5,y-15,1,1,PAL.outline); px(x+12,y-15,1,1,PAL.outline);
  // mug held in the left paw
  px(x-12,y-8,7,7,PAL.paper); px(x-11,y-7,5,5,PAL.mugC); px(x-5,y-7,2,3,PAL.paper);
  px(x-11,y-9,4,2,'rgba(255,255,255,.55)');                    // steam
  // "Z z" sleep symbols
  ctx.fillStyle=PAL.ink; ctx.font='7px "Press Start 2P", monospace'; ctx.fillText('Z', x+28, y-24);
  ctx.font='4px "Press Start 2P", monospace'; ctx.fillText('z', x+35, y-30);
}

// blend two #rrggbb colours (t: 0->a, 1->b)
function lerpCol(a,b,t){ const pa=parseInt(a.slice(1),16),pb=parseInt(b.slice(1),16);
  const ar=(pa>>16)&255,ag=(pa>>8)&255,ab=pa&255, br=(pb>>16)&255,bg=(pb>>8)&255,bb=pb&255;
  return 'rgb('+Math.round(ar+(br-ar)*t)+','+Math.round(ag+(bg-ag)*t)+','+Math.round(ab+(bb-ab)*t)+')'; }
function cloud(cx,cy){ cx|=0; cy|=0; px(cx,cy,15,4,PAL.cloud); px(cx+3,cy-3,9,4,PAL.cloud); px(cx+1,cy+3,17,2,'rgba(255,255,255,.75)'); }
// a row of city buildings sitting on the window sill (clipped to x..x+w).
// `lit` => night mode: warm yellow lit windows speckled across dark silhouettes.
function drawSkyline(x,y,w,h,col,hf,step,lit){
  const hs=[16,26,12,32,20,28,15,24,18,30,22,14]; let bx=x+1,i=0; const baseY=y+h;
  while(bx<x+w-1){ const bw=Math.min(10+(i%4)*5, x+w-1-bx);
    const bh=Math.round(h*hf*(0.45+0.55*(hs[(i*step)%hs.length]/32)));
    px(bx,baseY-bh,bw,bh,col);
    for(let wy=baseY-bh+3;wy<baseY-2;wy+=5) for(let wx=bx+2;wx<bx+bw-2;wx+=4){
      if(lit){ const on=((wx*31+wy*17+i*13)%5===0); px(wx,wy,1,2, on?PAL.litWin:'rgba(255,255,255,.05)'); }
      else px(wx,wy,1,2,PAL.bldgWin);
    }
    bx+=bw+3; i++;
  }
}
// ---- day / dusk / night in the window, from the REAL sun position -- season- AND place-aware,
// with NO location permission. The browser hands us the IANA time-zone name for free via Intl;
// we map it to a representative city lat/lng (tz-database zone.tab) and compute the sun's altitude
// locally. Nothing leaves the machine, and there is never a GPS prompt. __forceSky overrides. ----
const TZ_COORDS = {
  // North America
  "America/New_York":[40.71,-74.01],"America/Detroit":[42.33,-83.05],"America/Toronto":[43.65,-79.38],
  "America/Chicago":[41.85,-87.65],"America/Winnipeg":[49.90,-97.14],"America/Mexico_City":[19.43,-99.13],
  "America/Denver":[39.74,-104.98],"America/Edmonton":[53.55,-113.49],"America/Phoenix":[33.45,-112.07],
  "America/Los_Angeles":[34.05,-118.24],"America/Vancouver":[49.28,-123.12],"America/Tijuana":[32.53,-117.02],
  "America/Anchorage":[61.22,-149.90],"America/Halifax":[44.65,-63.57],"Pacific/Honolulu":[21.31,-157.86],
  // Central & South America
  "America/Guatemala":[14.61,-90.53],"America/Panama":[8.98,-79.52],"America/Bogota":[4.61,-74.08],
  "America/Lima":[-12.05,-77.04],"America/Caracas":[10.50,-66.92],"America/Santiago":[-33.45,-70.67],
  "America/Sao_Paulo":[-23.55,-46.63],"America/Argentina/Buenos_Aires":[-34.61,-58.38],
  // Europe
  "Europe/London":[51.51,-0.13],"Europe/Dublin":[53.35,-6.26],"Europe/Lisbon":[38.72,-9.14],
  "Europe/Madrid":[40.42,-3.70],"Europe/Paris":[48.85,2.35],"Europe/Brussels":[50.85,4.35],
  "Europe/Amsterdam":[52.37,4.90],"Europe/Berlin":[52.52,13.40],"Europe/Zurich":[47.37,8.55],
  "Europe/Rome":[41.90,12.50],"Europe/Vienna":[48.21,16.37],"Europe/Prague":[50.08,14.44],
  "Europe/Warsaw":[52.23,21.01],"Europe/Budapest":[47.50,19.04],"Europe/Copenhagen":[55.68,12.57],
  "Europe/Stockholm":[59.33,18.07],"Europe/Oslo":[59.91,10.75],"Europe/Helsinki":[60.17,24.94],
  "Europe/Athens":[37.98,23.73],"Europe/Bucharest":[44.43,26.10],"Europe/Sofia":[42.70,23.32],
  "Europe/Kyiv":[50.45,30.52],"Europe/Kiev":[50.45,30.52],"Europe/Moscow":[55.76,37.62],
  "Europe/Istanbul":[41.01,28.98],
  // Middle East
  "Asia/Jerusalem":[31.78,35.22],"Asia/Tel_Aviv":[32.07,34.79],"Asia/Beirut":[33.89,35.50],
  "Asia/Amman":[31.95,35.93],"Asia/Damascus":[33.51,36.29],"Asia/Baghdad":[33.31,44.36],
  "Asia/Riyadh":[24.71,46.68],"Asia/Dubai":[25.20,55.27],"Asia/Qatar":[25.29,51.53],
  "Asia/Kuwait":[29.38,47.99],"Asia/Tehran":[35.69,51.39],"Asia/Nicosia":[35.17,33.36],
  // Africa
  "Africa/Casablanca":[33.57,-7.59],"Africa/Algiers":[36.75,3.06],"Africa/Cairo":[30.04,31.24],
  "Africa/Lagos":[6.52,3.38],"Africa/Nairobi":[-1.29,36.82],"Africa/Addis_Ababa":[9.03,38.74],
  "Africa/Johannesburg":[-26.20,28.05],"Africa/Accra":[5.60,-0.19],
  // South, Central & East Asia
  "Asia/Karachi":[24.86,67.01],"Asia/Kolkata":[22.57,88.36],"Asia/Calcutta":[22.57,88.36],
  "Asia/Colombo":[6.93,79.85],"Asia/Kathmandu":[27.72,85.32],"Asia/Dhaka":[23.71,90.41],
  "Asia/Yangon":[16.87,96.20],"Asia/Bangkok":[13.75,100.52],"Asia/Ho_Chi_Minh":[10.82,106.63],
  "Asia/Saigon":[10.82,106.63],"Asia/Jakarta":[-6.21,106.85],"Asia/Singapore":[1.29,103.85],
  "Asia/Kuala_Lumpur":[3.14,101.69],"Asia/Manila":[14.60,120.98],"Asia/Hong_Kong":[22.32,114.17],
  "Asia/Shanghai":[31.23,121.47],"Asia/Taipei":[25.03,121.57],"Asia/Seoul":[37.57,126.98],
  "Asia/Tokyo":[35.68,139.65],"Asia/Almaty":[43.25,76.95],"Asia/Tashkent":[41.31,69.24],
  "Asia/Yekaterinburg":[56.84,60.65],"Asia/Novosibirsk":[55.01,82.93],"Asia/Vladivostok":[43.12,131.89],
  // Australia & Pacific
  "Australia/Perth":[-31.95,115.86],"Australia/Adelaide":[-34.93,138.60],"Australia/Darwin":[-12.46,130.84],
  "Australia/Brisbane":[-27.47,153.03],"Australia/Sydney":[-33.87,151.21],"Australia/Melbourne":[-37.81,144.96],
  "Pacific/Auckland":[-36.85,174.76],"Pacific/Fiji":[-18.14,178.44]
};
function localCoords(){
  let tz='';
  try{ tz=Intl.DateTimeFormat().resolvedOptions().timeZone||''; }catch(e){}
  if(TZ_COORDS[tz]) return TZ_COORDS[tz];
  // unknown zone: longitude from the UTC offset, equatorial latitude (a neutral ~6pm sunset)
  return [0, -new Date().getTimezoneOffset()/4];
}
// sun altitude (degrees above the horizon) right now, at lat/lng. Low-precision USNO formulas
// (good to a fraction of a degree -- ample for deciding day/dusk/night).
function sunAltitude(date, lat, lng){
  const rad=Math.PI/180, deg=180/Math.PI;
  const d = date.getTime()/86400000 - 10957.5;              // days since J2000 (2000-01-01 12:00 UTC)
  const g = ((357.529 + 0.98560028*d)%360)*rad;             // mean anomaly
  const q = (280.459 + 0.98564736*d)%360;                   // mean longitude
  const L = (q + 1.915*Math.sin(g) + 0.020*Math.sin(2*g))*rad;   // ecliptic longitude
  const e = (23.439 - 0.00000036*d)*rad;                    // obliquity
  const dec = Math.asin(Math.sin(e)*Math.sin(L));           // declination
  const ra  = Math.atan2(Math.cos(e)*Math.sin(L), Math.cos(L))*deg;   // right ascension (deg)
  let gmst = (18.697374558 + 24.06570982441908*d)%24; if(gmst<0) gmst+=24;
  let ha = ((gmst*15 + lng) - ra)%360; ha=((ha+540)%360)-180;   // hour angle, folded to [-180,180]
  return Math.asin(Math.sin(lat*rad)*Math.sin(dec) + Math.cos(lat*rad)*Math.cos(dec)*Math.cos(ha*rad))*deg;
}
function skyMode(){
  if(window.__forceSky) return window.__forceSky;
  const c=localCoords(), alt=sunAltitude(new Date(), c[0], c[1]);
  if(alt <= -6) return 'night';        // sun past civil twilight -> dark
  if(alt <   6) return 'dusk';         // sun near the horizon -> golden dawn/dusk
  return 'day';
}
function drawWindow(x,y,w,h){
  // chunky frame
  px(x-5,y-5,w+10,h+10,PAL.woodDk); px(x-3,y-3,w+6,h+6,PAL.wood); px(x-3,y-3,w+6,2,PAL.woodHi);
  const mode=skyMode(), night=(mode==='night'), bands=10, bh=Math.ceil(h/bands);
  if(night){
    for(let i=0;i<bands;i++) px(x, y+Math.round(i*h/bands), w, bh, lerpCol(PAL.nightTop, PAL.nightBot, i/(bands-1)));
    // scattered stars (deterministic) in the upper sky
    for(let s=0;s<48;s++){ const sx=x+((s*73)%(w-4))+2, sy=y+((s*37)%Math.max(1,Math.round(h*0.5)))+2;
      px(sx,sy,1,1, s%6? 'rgba(255,255,255,.85)':'rgba(255,255,255,.45)'); }
    // crescent moon (top-right)
    const mnx=x+w-Math.round(w*0.20), mny=y+Math.round(h*0.16);
    px(mnx,mny,8,8,PAL.moon); px(mnx+4,mny-1,6,8, lerpCol(PAL.moon,PAL.nightTop,.4));
    cloud(x+w*0.30, y+h*0.16);
    drawSkyline(x,y,w,h, PAL.bldgN2, 0.42, 7, true);
    drawSkyline(x,y,w,h, PAL.bldgN1, 0.64, 11, true);
  } else {
    let top=PAL.skyTop, bot=PAL.sky;
    if(mode==='dusk'){ top=lerpCol(PAL.skyTop,'#eaa86e',.30); bot=lerpCol(PAL.sky,'#f6c79a',.45); } // soft dawn/dusk tint
    for(let i=0;i<bands;i++) px(x, y+Math.round(i*h/bands), w, bh, lerpCol(top, bot, i/(bands-1)));
    drawSkyline(x,y,w,h, PAL.bldg2, 0.40, 7, false);
    cloud(x+w*0.16, y+h*0.20); cloud(x+w*0.44, y+h*0.12); cloud(x+w*0.70, y+h*0.26);
    drawSkyline(x,y,w,h, PAL.bldg1, 0.62, 11, false);
  }
  // occasional airliner drifting across the sky (clipped to the glass, behind the mullions)
  if(amb.plane){ ctx.save(); ctx.beginPath(); ctx.rect(x,y,w,h); ctx.clip(); drawPlane(amb.plane); ctx.restore(); }
  // chunky mullions: vertical panes + one horizontal transom (dark core + light edge)
  const panes=4, pw=w/panes;
  for(let i=1;i<panes;i++){ px(x+Math.round(i*pw)-1,y,3,h,PAL.woodDk); px(x+Math.round(i*pw)-1,y,1,h,PAL.wood); }
  px(x,y+Math.round(h*0.5)-1,w,3,PAL.woodDk); px(x,y+Math.round(h*0.5)-1,w,1,PAL.wood);
  px(x,y,w,1,'rgba(0,0,0,.22)'); px(x,y+h-1,w,1,'rgba(0,0,0,.22)');
  // glass sheen on the top-left pane
  px(x+2,y+2,Math.round(pw)-5,2, night?'rgba(255,255,255,.07)':'rgba(255,255,255,.20)');
}

// real, positive quotes (motivation / happiness / health) with attribution.
// 150+ entries, majority by women, plus a lighter witty/programmer-humour batch --
// the board shows a new one every 10 minutes.
const QUOTES = [
  ["Try to be a rainbow in someone's cloud.","Maya Angelou"],
  ["If you don't like something, change it. If you can't change it, change your attitude.","Maya Angelou"],
  ["Nothing will work unless you do.","Maya Angelou"],
  ["We may encounter many defeats but we must not be defeated.","Maya Angelou"],
  ["People will forget what you said, but never how you made them feel.","Maya Angelou"],
  ["Success is liking yourself, liking what you do, and liking how you do it.","Maya Angelou"],
  ["No one can make you feel inferior without your consent.","Eleanor Roosevelt"],
  ["The future belongs to those who believe in the beauty of their dreams.","Eleanor Roosevelt"],
  ["Do one thing every day that scares you.","Eleanor Roosevelt"],
  ["You must do the things you think you cannot do.","Eleanor Roosevelt"],
  ["With the new day comes new strength and new thoughts.","Eleanor Roosevelt"],
  ["When they go low, we go high.","Michelle Obama"],
  ["Success is about the difference you make in people's lives.","Michelle Obama"],
  ["Failure is an important part of your growth.","Michelle Obama"],
  ["There is no limit to what we, as women, can accomplish.","Michelle Obama"],
  ["Turn your wounds into wisdom.","Oprah Winfrey"],
  ["The more you praise and celebrate your life, the more there is to celebrate.","Oprah Winfrey"],
  ["Surround yourself with people who are going to lift you higher.","Oprah Winfrey"],
  ["Be thankful for what you have and you'll end up having more.","Oprah Winfrey"],
  ["Life is either a daring adventure or nothing at all.","Helen Keller"],
  ["Optimism is the faith that leads to achievement.","Helen Keller"],
  ["Keep your face to the sunshine and you cannot see a shadow.","Helen Keller"],
  ["Alone we can do so little; together we can do so much.","Helen Keller"],
  ["Nothing in life is to be feared, it is only to be understood.","Marie Curie"],
  ["Be less curious about people and more curious about ideas.","Marie Curie"],
  ["I never see what has been done; I only see what remains to be done.","Marie Curie"],
  ["The most difficult thing is the decision to act; the rest is merely tenacity.","Amelia Earhart"],
  ["Adventure is worthwhile in itself.","Amelia Earhart"],
  ["Think of all the beauty still left around you and be happy.","Anne Frank"],
  ["Whoever is happy will make others happy too.","Anne Frank"],
  ["No one has ever become poor by giving.","Anne Frank"],
  ["Not all of us can do great things, but we can do small things with great love.","Mother Teresa"],
  ["Spread love everywhere you go.","Mother Teresa"],
  ["Peace begins with a smile.","Mother Teresa"],
  ["Kind words are short to speak but their echoes are truly endless.","Mother Teresa"],
  ["One child, one teacher, one book, one pen can change the world.","Malala Yousafzai"],
  ["When the whole world is silent, even one voice becomes powerful.","Malala Yousafzai"],
  ["We realize the importance of our voices only when we are silenced.","Malala Yousafzai"],
  ["It is our choices that show what we truly are, far more than our abilities.","J.K. Rowling"],
  ["Happiness can be found even in the darkest of times if one remembers to turn on the light.","J.K. Rowling"],
  ["We carry all the power we need to change the world inside ourselves already.","J.K. Rowling"],
  ["Talk to yourself like you would to someone you love.","Brené Brown"],
  ["Vulnerability is the birthplace of innovation, creativity and change.","Brené Brown"],
  ["Courage starts with showing up and letting ourselves be seen.","Brené Brown"],
  ["If there's a book you want to read that hasn't been written, you must write it.","Toni Morrison"],
  ["If you want to fly, give up everything that weighs you down.","Toni Morrison"],
  ["Caring for myself is not self-indulgence, it is self-preservation.","Audre Lorde"],
  ["No need to hurry. No need to sparkle. No need to be anybody but oneself.","Virginia Woolf"],
  ["One cannot think well, love well, sleep well, if one has not dined well.","Virginia Woolf"],
  ["I am not afraid of storms, for I am learning how to sail my ship.","Louisa May Alcott"],
  ["Have regular hours for work and play; make each day both useful and pleasant.","Louisa May Alcott"],
  ["Far away there in the sunshine are my highest aspirations.","Louisa May Alcott"],
  ["Nothing is impossible; the word itself says 'I'm possible'!","Audrey Hepburn"],
  ["The most important thing is to enjoy your life and to be happy.","Audrey Hepburn"],
  ["For beautiful eyes, look for the good in others.","Audrey Hepburn"],
  ["We have two hands, one to help ourselves, the other to help others.","Audrey Hepburn"],
  ["Beauty begins the moment you decide to be yourself.","Coco Chanel"],
  ["The most courageous act is still to think for yourself. Aloud.","Coco Chanel"],
  ["In order to be irreplaceable one must always be different.","Coco Chanel"],
  ["Keep smiling, because life is a beautiful thing and there's so much to smile about.","Marilyn Monroe"],
  ["Life shrinks or expands in proportion to one's courage.","Anaïs Nin"],
  ["We write to taste life twice, in the moment and in retrospect.","Anaïs Nin"],
  ["You must never be fearful about what you are doing when it is right.","Rosa Parks"],
  ["Real change, enduring change, happens one step at a time.","Ruth Bader Ginsburg"],
  ["Fight for the things you care about, but in a way that leads others to join you.","Ruth Bader Ginsburg"],
  ["What you do makes a difference, and you decide what kind of difference to make.","Jane Goodall"],
  ["Every individual matters. Every individual has a role to play.","Jane Goodall"],
  ["At the end of the day, we can endure much more than we think we can.","Frida Kahlo"],
  ["Feet, what do I need them for if I have wings to fly.","Frida Kahlo"],
  ["A champion is defined by how they recover when they fall.","Serena Williams"],
  ["If you want the rainbow, you gotta put up with the rain.","Dolly Parton"],
  ["Find out who you are and do it on purpose.","Dolly Parton"],
  ["Change your life today. Don't gamble on the future, act now.","Simone de Beauvoir"],
  ["Dwell in possibility.","Emily Dickinson"],
  ["Hope is the thing with feathers that perches in the soul.","Emily Dickinson"],
  ["Tell me, what is it you plan to do with your one wild and precious life?","Mary Oliver"],
  ["Instructions for living a life: pay attention, be astonished, tell about it.","Mary Oliver"],
  ["Dreaming, after all, is a form of planning.","Gloria Steinem"],
  ["Never doubt that a small group of thoughtful people can change the world.","Margaret Mead"],
  ["How very little can be done under the spirit of fear.","Florence Nightingale"],
  ["You cannot shake hands with a clenched fist.","Indira Gandhi"],
  ["It's the little things citizens do. That's what will make the difference.","Wangari Maathai"],
  ["If you obey all the rules, you miss all the fun.","Katharine Hepburn"],
  ["Done is better than perfect.","Sheryl Sandberg"],
  ["Failure is not the opposite of success; it's part of success.","Arianna Huffington"],
  ["Do what you were born to do. You just have to trust yourself.","Beyoncé"],
  ["Every great dream begins with a dreamer.","Harriet Tubman"],
  ["I never dreamed about success. I worked for it.","Estée Lauder"],
  ["Just don't give up trying to do what you really want to do.","Ella Fitzgerald"],
  ["Love yourself first and everything else falls into line.","Lucille Ball"],
  ["Above all, be the heroine of your life, not the victim.","Nora Ephron"],
  ["Trust yourself. Create the self you'll be happy to live with all your life.","Golda Meir"],
  ["There are years that ask questions and years that answer.","Zora Neale Hurston"],
  ["Confidence -- if you have it, you can make anything look good.","Diane von Furstenberg"],
  ["A woman with a voice is, by definition, a strong woman.","Melinda Gates"],
  ["The only way to do great work is to love what you do.","Steve Jobs"],
  ["Your time is limited, so don't waste it living someone else's life.","Steve Jobs"],
  ["Stay hungry, stay foolish.","Steve Jobs"],
  ["It always seems impossible until it's done.","Nelson Mandela"],
  ["The greatest glory in living lies in rising every time we fall.","Nelson Mandela"],
  ["May your choices reflect your hopes, not your fears.","Nelson Mandela"],
  ["The best way to find yourself is to lose yourself in the service of others.","Mahatma Gandhi"],
  ["Live as if you were to die tomorrow. Learn as if you were to live forever.","Mahatma Gandhi"],
  ["The future depends on what you do today.","Mahatma Gandhi"],
  ["In the middle of difficulty lies opportunity.","Albert Einstein"],
  ["Life is like riding a bicycle. To keep your balance you must keep moving.","Albert Einstein"],
  ["Strive not to be a success, but rather to be of value.","Albert Einstein"],
  ["It does not matter how slowly you go as long as you do not stop.","Confucius"],
  ["Wherever you go, go with all your heart.","Confucius"],
  ["Happiness depends upon ourselves.","Aristotle"],
  ["We are what we repeatedly do; excellence is a habit.","Aristotle"],
  ["What lies within us matters more than what lies behind or before us.","Ralph Waldo Emerson"],
  ["Write it on your heart that every day is the best day in the year.","Ralph Waldo Emerson"],
  ["Go confidently in the direction of your dreams.","Henry David Thoreau"],
  ["It's not what you look at that matters, it's what you see.","Henry David Thoreau"],
  ["The secret of getting ahead is getting started.","Mark Twain"],
  ["Kindness is a language the deaf can hear and the blind can see.","Mark Twain"],
  ["Well done is better than well said.","Benjamin Franklin"],
  ["An investment in knowledge pays the best interest.","Benjamin Franklin"],
  ["Energy and persistence conquer all things.","Benjamin Franklin"],
  ["Do what you can, with what you have, where you are.","Theodore Roosevelt"],
  ["Believe you can and you're halfway there.","Theodore Roosevelt"],
  ["Faith is taking the first step even when you don't see the whole staircase.","Martin Luther King Jr."],
  ["Darkness cannot drive out darkness; only light can do that.","Martin Luther King Jr."],
  ["The time is always right to do what is right.","Martin Luther King Jr."],
  ["Happiness comes from your own actions.","Dalai Lama"],
  ["A calm mind brings inner strength and self-confidence.","Dalai Lama"],
  ["Be kind whenever possible. It is always possible.","Dalai Lama"],
  ["The wound is the place where the light enters you.","Rumi"],
  ["What you seek is seeking you.","Rumi"],
  ["Let yourself be silently drawn by what you really love.","Rumi"],
  ["The journey of a thousand miles begins with a single step.","Lao Tzu"],
  ["Nature does not hurry, yet everything is accomplished.","Lao Tzu"],
  ["New beginnings are often disguised as painful endings.","Lao Tzu"],
  ["Luck is what happens when preparation meets opportunity.","Seneca"],
  ["The happiness of your life depends upon the quality of your thoughts.","Marcus Aurelius"],
  ["Very little is needed to make a happy life.","Marcus Aurelius"],
  ["There are far, far better things ahead than any we leave behind.","C.S. Lewis"],
  ["You are never too old to set a new goal or to dream a new dream.","C.S. Lewis"],
  ["The best way out is always through.","Robert Frost"],
  ["In three words I can sum up everything about life: it goes on.","Robert Frost"],
  ["Life is what happens when you're busy making other plans.","John Lennon"],
  ["The way to get started is to quit talking and begin doing.","Walt Disney"],
  ["If you can dream it, you can do it.","Walt Disney"],
  ["Take care of your body. It's the only place you have to live.","Jim Rohn"],
  ["Either you run the day or the day runs you.","Jim Rohn"],
  ["You don't have to be great to start, but you have to start to be great.","Zig Ziglar"],
  ["Whether you think you can, or you think you can't, you're right.","Henry Ford"],
  ["When we can no longer change a situation, we are challenged to change ourselves.","Viktor Frankl"],
  ["The mind is everything. What you think you become.","Buddha"],
  ["Health is the greatest gift, contentment the greatest wealth.","Buddha"],
  ["Act as if what you do makes a difference. It does.","William James"],
  ["Change your thoughts and you change your world.","Norman Vincent Peale"],
  ["How people treat you is their karma; how you react is yours.","Wayne Dyer"],
  ["What you do today can improve all your tomorrows.","Ralph Marston"],
  ["Little by little, one travels far.","J.R.R. Tolkien"],
  ["Not all those who wander are lost.","J.R.R. Tolkien"],
  ["The only place success comes before work is in the dictionary.","Vince Lombardi"],
  // --- a lighter batch: witty / surprising / programmer-humour (all real & attributed) ---
  ["Do not let what you cannot do interfere with what you can do.","John Wooden"],
  ["There is no education like adversity.","Benjamin Disraeli"],
  ["Happiness is a direction, not a place.","Sydney J. Harris"],
  ["Trust yourself. You know more than you think you do.","Benjamin Spock"],
  ["The greater the obstacle, the more glory in overcoming it.","Molière"],
  ["The best way to predict the future is to invent it.","Alan Kay"],
  ["To live is the rarest thing in the world. Most people exist, that is all.","Oscar Wilde"],
  ["Talk is cheap. Show me the code.","Linus Torvalds"],
  ["One of my most productive days was throwing away 1000 lines of code.","Ken Thompson"],
  ["There are only two hard things in Computer Science: cache invalidation and naming things.","Phil Karlton"],
  ["Debugging is twice as hard as writing the code in the first place.","Brian Kernighan"],
  ["There are two ways to write error-free programs; only the third one works.","Alan J. Perlis"],
  ["I love deadlines. I like the whooshing sound they make as they fly by.","Douglas Adams"],
  ["I intend to live forever. So far, so good.","Steven Wright"],
  ["An escalator can never break: it can only become stairs.","Mitch Hedberg"],
  ["If it wasn't for coffee, I'd have no identifiable personality at all.","David Letterman"],
  ["A mathematician is a device for turning coffee into theorems.","Paul Erdős"],
  ["I'd rather take coffee than compliments just now.","Louisa May Alcott"],
  ["Doing nothing is very hard to do; you never know when you're finished.","Leslie Nielsen"],
  ["I work for myself, which is fun. Except when I call in sick, I know I'm lying.","Rita Rudner"],
];
const QUOTE_PERIOD_MS = 600*1000;   // a fresh quote every 10 minutes
// greedy word-wrap to a pixel width for the given canvas font
function wrapText(text, maxW, font){
  ctx.font=font;
  const words=text.split(' '); const lines=[]; let cur='';
  for(const w of words){ const test=cur?cur+' '+w:w;
    if(ctx.measureText(test).width>maxW && cur){ lines.push(cur); cur=w; } else cur=test; }
  if(cur) lines.push(cur);
  return lines;
}

// evenly space the clock (24w), bookshelf (50w) and DO GOOD WORK poster (54w) across the wall
// to the RIGHT of the inspiration board -> equal gaps between the three, robust to canvas W.
// Shared by drawWallDecor (clock + shelf) and drawOfficeProps (poster) so they stay in sync.
function wallRowLayout(){
  const boardX = 20 + Math.round(W*0.36) + 16, boardW = 210;
  const clkW = 24, shfW = 50, posW = 54;
  const boardRight = boardX + boardW;
  const gap = ((W-9 - (boardRight+12)) - (clkW+shfW+posW)) / 2;   // 2 equal gaps between 3 items
  const clkL = boardRight + 12;
  const shfL = clkL + clkW + gap;
  const posL = shfL + shfW + gap;
  return { boardX, clkL, shfL, posL };
}

function drawWallDecor(x, y, clkL, shfL){
  // ---- inspiration board: a quote that changes every 10 minutes (whole board) ----
  const bw=210, bh=58; px(x-3,y-3,bw+6,bh+6,PAL.metalDk); px(x,y,bw,bh,PAL.paper);
  px(x,y,bw,2,'#eef0f3'); px(x,y+bh-2,bw,2,'#cfcfd6'); px(x+bw-2,y,2,bh,'#dadbe0');
  ctx.textAlign='left';
  const q = QUOTES[Math.floor(Date.now()/QUOTE_PERIOD_MS) % QUOTES.length];
  // heading + a tiny heart in the corner
  ctx.fillStyle=PAL.leafDk; ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('INSPIRATION', x+8, y+12);
  const hh=x+bw-13; px(hh,y+5,3,2,PAL.pink); px(hh+4,y+5,3,2,PAL.pink); px(hh,y+7,7,2,PAL.pink); px(hh+1,y+9,5,1,PAL.pink); px(hh+2,y+10,3,1,PAL.pink);
  px(x+8,y+16,bw-16,1,'#dfe6da');
  // quote across the full board width
  ctx.fillStyle=PAL.ink; const qfont='5px "Press Start 2P", monospace';
  const lines=wrapText('“'+q[0]+'”', bw-18, qfont).slice(0,4);
  let qy=y+25; for(const ln of lines){ ctx.fillText(ln, x+8, qy); qy+=7; }
  ctx.fillStyle=PAL.leafDk; ctx.fillText('- '+q[1], x+8, qy+2);
  // ---- wall clock (live local time) -- x-pos comes from wallRowLayout() (even spacing) ----
  const clx=clkL+3, cly=y+6; px(clx-3,cly-3,24,24,PAL.woodDk); px(clx-1,cly-1,20,20,PAL.metalDk); px(clx,cly,18,18,PAL.paper);
  for(let a=0;a<12;a++){ const ang=a*Math.PI/6; px(clx+9+Math.round(7*Math.sin(ang)), cly+9-Math.round(7*Math.cos(ang)), 1,1, PAL.ink); }
  const ccx=clx+9, ccy=cly+9, now=new Date();
  const hA=((now.getHours()%12)+now.getMinutes()/60)*Math.PI/6;    // 30 deg/hr + drift
  const mA=(now.getMinutes()+now.getSeconds()/60)*Math.PI/30;      // 6 deg/min
  const sA=now.getSeconds()*Math.PI/30;                            // 6 deg/sec
  ctx.lineCap='round';
  ctx.strokeStyle=PAL.ink; ctx.lineWidth=1.5; ctx.beginPath();     // hour hand (short, thick)
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+4.5*Math.sin(hA), ccy-4.5*Math.cos(hA)); ctx.stroke();
  ctx.lineWidth=1.1; ctx.beginPath();                              // minute hand (long)
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+7*Math.sin(mA), ccy-7*Math.cos(mA)); ctx.stroke();
  ctx.strokeStyle=PAL.red; ctx.lineWidth=0.7; ctx.beginPath();     // thin red second hand
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+7.5*Math.sin(sA), ccy-7.5*Math.cos(sA)); ctx.stroke();
  ctx.lineCap='butt';
  px(clx+8,cly+8,2,2,PAL.red);                                  // center hub
  // ---- bookshelf with books + a little plant on top (x-pos from wallRowLayout) ----
  const shx=shfL+2, shy=y+12; px(shx-2,shy-2,50,56,PAL.woodDk); px(shx,shy,46,52,PAL.wood); px(shx,shy,46,2,PAL.woodHi);
  const cols=[PAL.mugA,PAL.mugB,PAL.mugC,PAL.leafDk,PAL.red,PAL.yellow,PAL.orange,'#8c5fd6'];
  for(let r=0;r<3;r++){ const ry=shy+5+r*16;
    for(let b=0;b<5;b++){ const bbh=11-((b+r)%2)*2; px(shx+4+b*8,ry+(11-bbh),6,bbh,cols[(b+r*3)%cols.length]); }
    px(shx+2,ry+13,42,2,PAL.woodDk);
  }
  smallPlant(shx+30, shy-2);
}

function drawOfficeProps(){
  const L=layout(), top=WALL_H;
  // plants flanking the window
  bigPlant(14, top+10); bigPlant(W-30, top+10);
  // "DO GOOD WORK" poster on the office back wall -- evenly spaced with the clock + bookshelf
  drawDoGoodWork(wallRowLayout().posL+3, 6);

  const lastDeskY = deskSlots.length ? Math.max.apply(null, deskSlots.map(s=>s.y)) : top+120;
  // soft rug spanning the desk area
  ctx.fillStyle='rgba(214,140,92,.13)'; ctx.fillRect(70, top+30, W-140, (lastDeskY+34)-(top+30));
  ctx.strokeStyle='rgba(160,96,52,.18)'; ctx.lineWidth=2; ctx.strokeRect(72, top+32, W-144, (lastDeskY+30)-(top+32));

  // ---- water cooler (far right) + floor plant (left) ----
  const wcx=W-56, wcy=lastDeskY+48; ro(wcx,wcy,18,30,PAL.steel); px(wcx+2,wcy-15,14,15,'#9fd9f0'); px(wcx+5,wcy+14,8,5,PAL.cabinet);
  bigPlant(34, lastDeskY+44);
}

function drawKitchenProps(){
  const L=layout(), k=L.kitchen, T=L.kitchenTop;
  // back wall band for mounting decor + counters
  px(0,T,W,30,PAL.wall); px(0,T+28,W,2,PAL.base);
  // tiled kitchen backsplash (subtle offset subway tiles) behind the counter/shelf
  for(let ty2=T+2; ty2<T+27; ty2+=6){
    const off=(((ty2-T)/6|0)%2)?5:0;
    for(let tx2=2-off; tx2<BEACH_X-2; tx2+=10){ px(tx2,ty2,9,5, ((tx2+ty2)&1)?'#e5ddc7':'#ede5d0'); }
  }
  drawBeachFloor();   // sand + water fill the right band (under the back-wall props)

  // ---- tall fridge (far left): freezer/fridge split, handles, magnets, photo ----
  const fx=8, fy=T+14, fw=30, fh=74; ro(fx,fy,fw,fh,PAL.fridge);
  px(fx,fy,fw,3,PAL.fridgeDk); px(fx+1,fy+1,fw-2,1,shade(PAL.fridge,.30));   // top + sheen
  px(fx,fy+30,fw,3,PAL.fridgeDk);                                            // freezer/fridge door split
  px(fx+fw-6,fy+7,3,17,PAL.metalDk); px(fx+fw-6,fy+38,3,28,PAL.metalDk);     // two vertical handles
  // magnets + a photo + a sticky note
  px(fx+5,fy+40,5,4,PAL.red); px(fx+12,fy+41,4,4,PAL.yellow); px(fx+18,fy+39,4,4,PAL.mugB);
  px(fx+5,fy+48,7,7,PAL.paper); px(fx+5,fy+48,7,1,'#e6e6ec'); px(fx+6,fy+50,5,3,'#9fd9f0'); // photo
  px(fx+15,fy+49,9,6,'#fff3b0'); px(fx+15,fy+49,9,1,shade('#fff3b0',-.2));                  // sticky note
  smallPlant(fx+9, fy-9);                                                    // little plant on top

  // ---- kitchen counter (center-back): solid countertop, cabinetry, inset sink,
  // espresso bar + a wall shelf with jars/mugs ----
  const cbx=150, cbw=224, cby=T+30, cbh=26, ctTop=cby-9;   // counter kept left of BEACH_X
  // solid countertop slab: bright tan surface, highlighted back edge + rounded
  // shaded front lip so it reads as a real worktop with depth.
  px(cbx-4,ctTop,cbw+8,9,PAL.cabinetTop);
  px(cbx-4,ctTop,cbw+8,1,shade(PAL.cabinetTop,.34));                        // back-edge highlight
  px(cbx-4,ctTop+1,cbw+8,1,shade(PAL.cabinetTop,.14));
  px(cbx-4,cby-3,cbw+8,3,shade(PAL.cabinetTop,-.16));                       // front lip
  px(cbx-4,cby-1,cbw+8,1,shade(PAL.cabinetTop,-.34));                       // lip undershadow
  // cabinetry: dark carcass + bevelled door/drawer fronts with steel pulls + toe-kick
  ro(cbx,cby,cbw,cbh,PAL.cabinet);
  const doors=6, dww=cbw/doors;
  for(let i=0;i<doors;i++){ const dx=cbx+3+i*dww;
    px(dx,cby+3,dww-6,cbh-8, shade(PAL.cabinet,.10));                       // raised front panel
    px(dx,cby+3,dww-6,1, shade(PAL.cabinet,.26));                          // top bevel (light)
    px(dx,cby+3,1,cbh-8, shade(PAL.cabinet,.18));                          // left bevel
    px(dx+dww-7,cby+3,1,cbh-8, shade(PAL.cabinet,-.26));                   // right bevel (dark)
    px(dx,cby+cbh-6,dww-6,1, shade(PAL.cabinet,-.30));                     // bottom bevel
    if(i%2===0){ px(dx+(dww-6)/2-1,cby+7,2,9,PAL.steel); px(dx+(dww-6)/2-1,cby+7,1,9,shade(PAL.steel,.3)); } // door pull (vertical)
    else { px(dx+4,cby+6,dww-14,2,PAL.steel); px(dx+4,cby+6,dww-14,1,shade(PAL.steel,.3)); }                 // drawer pull (horizontal)
  }
  px(cbx,cby+cbh-2,cbw,2, shade(PAL.cabinet,-.42)); px(cbx,cby+cbh,cbw,1,'rgba(0,0,0,.22)'); // toe-kick shadow
  // ---- espresso machine on the counter (left): body, bean hopper, display,
  // buttons, steam wand, a group head + portafilter and a cup catching the shot ----
  const cmw=34, cmh=23, cmx=cbx+8, cmy=ctTop-cmh;
  ro(cmx,cmy,cmw,cmh,'#3b3b46');                                            // body
  px(cmx+1,cmy+1,cmw-2,2,'#585863');                                        // top sheen
  px(cmx,cmy+cmh-4,cmw,4,'#2a2a32');                                        // darker base
  px(cmx+cmw-10,cmy-4,7,5,'#2a2a32'); px(cmx+cmw-9,cmy-3,5,2,'#4a4a55');    // bean hopper on top
  px(cmx+3,cmy+3,13,6,PAL.screen); px(cmx+3,cmy+3,13,1,'#c3f0f7');          // display
  px(cmx+4,cmy+12,3,3,PAL.red); px(cmx+9,cmy+12,3,3,PAL.yellow); px(cmx+14,cmy+12,3,3,PAL.leaf); // buttons
  px(cmx+cmw-4,cmy+6,2,9,PAL.metalDk); px(cmx+cmw-5,cmy+14,3,2,PAL.metalDk); // steam wand
  px(cmx+9,cmy+cmh-5,10,3,'#23232a');                                       // group head
  px(cmx+12,cmy+cmh-2,4,2,PAL.metalDk);                                     // portafilter neck
  mug(cmx+10,ctTop-7,'#ececf2');                                           // cup catching the shot
  // ---- wall shelf (center): plank holding two glass jars, a canister + two mugs ----
  const shx=cbx+54, shw=92, shy=T+1;
  px(shx-3,shy+16,shw+6,3,PAL.woodDk); px(shx-3,shy+15,shw+6,1,PAL.woodHi); // plank + edge
  px(shx-3,shy+19,shw+6,1,'rgba(0,0,0,.20)');                              // under-shelf shadow
  px(shx+4,shy+5,9,11,'rgba(212,226,233,.85)'); px(shx+4,shy+12,9,4,'#6b4a2e'); // clear jar w/ beans
  px(shx+4,shy+5,9,2,'#e3edf1'); px(shx+3,shy+3,11,2,PAL.metalDk);          // jar sheen + lid
  px(shx+18,shy+6,9,10,'rgba(183,217,192,.92)'); px(shx+18,shy+6,9,2,shade('#b7d9c0',.3)); px(shx+17,shy+4,11,2,PAL.leafDk); // green jar + lid
  px(shx+33,shy+4,9,12,PAL.mugC); px(shx+33,shy+4,9,2,shade(PAL.mugC,.34)); px(shx+33,shy+9,9,1,shade(PAL.mugC,-.18)); // canister
  mug(shx+48,shy+7,PAL.mugA); mug(shx+62,shy+7,PAL.mugB);
  smallPlant(shx+80, shy-1);                                                // a little trailing plant on the shelf end
  // ---- hanging planter in the gap between the coffee sign and the shelf ----
  const hgx=166;
  px(hgx,T,1,6,'#8a7a5a'); px(hgx+8,T,1,6,'#8a7a5a');                       // two cords
  px(hgx-3,T+6,15,5,PAL.pot); px(hgx-3,T+6,15,2,shade(PAL.pot,.18)); px(hgx-4,T+10,17,1,PAL.potDk); // pot
  blade(hgx-1,T+11,7,-3,PAL.leafDk); blade(hgx+4,T+11,9,0,PAL.leaf); blade(hgx+9,T+11,6,3,PAL.leafDk); // trailing leaves
  // ---- SINK (center-right): a stainless drop-in basin recessed into the counter
  // (steel rim, two-tone recessed interior, centre drain) with a proper goose-neck
  // faucet rising behind it (riser + arched spout + downspout + lever) -- clearly a sink ----
  const skx=cbx+150, skw=60, skBot=ctTop, skTop=skBot-14;
  ro(skx,skTop,skw,14,PAL.steel);                                           // stainless basin shell
  px(skx,skTop,skw,2,shade(PAL.steel,.34));                                 // rim top highlight
  px(skx,skTop+12,skw,2,shade(PAL.steel,-.26));                             // front rim shadow
  px(skx+4,skTop+3,skw-8,9,'#5a6e7d');                                      // recessed basin (upper)
  px(skx+6,skTop+5,skw-12,6,'#46586a');                                     // recessed basin (deeper)
  px(skx+6,skTop+10,skw-12,1,'#374755');                                    // basin floor
  px(skx+skw/2-2,skTop+8,4,2,'#2b3640');                                    // drain
  px(skx+6,skTop+4,skw-13,1,'rgba(255,255,255,.22)');                       // water sheen
  const fcx=skx+skw-18, fTop=T;                                             // faucet column (right-back)
  px(fcx-3,skTop-2,10,3,PAL.metalDk);                                       // escutcheon base plate
  px(fcx,fTop+2,4,skTop-fTop,PAL.steel); px(fcx,fTop+2,1,skTop-fTop,shade(PAL.steel,.34)); // vertical riser
  px(fcx-2,fTop,6,3,PAL.steel); px(fcx-7,fTop,6,3,PAL.steel); px(fcx-11,fTop+1,5,3,PAL.steel); // gooseneck arch (curving left)
  px(fcx-2,fTop,8,1,shade(PAL.steel,.3));                                   // arch highlight
  px(fcx-11,fTop+3,3,5,PAL.steel); px(fcx-11,fTop+7,3,2,PAL.metalDk);       // downspout + tip over the basin
  px(fcx+4,skTop-4,5,2,PAL.metalDk); px(fcx+4,skTop-4,5,1,shade(PAL.metalDk,.3)); // lever handle

  // ---- "COFFEE > CODE > CONQUER" wall sign (left) ----
  const sgx=58, sgy=T+3; px(sgx-2,sgy-2,90,24,PAL.woodDk); px(sgx,sgy,86,20,PAL.paper);
  ctx.fillStyle=PAL.ink; ctx.font='5px "Press Start 2P", monospace';
  ctx.fillText('COFFEE >', sgx+6, sgy+9); ctx.fillText('CODE > CONQUER', sgx+6, sgy+17);

  // (the "DO GOOD WORK" poster now hangs in the office; a "RETIRED AGENTS" beach
  //  sign takes its place -- both drawn elsewhere)

  // ---- "REFRESH!" drinks machine (far right): blue cabinet, lit sign, glass grid, side panel ----
  const vx=W-74, vy=T+10, vw=64, vh=88;
  ro(vx,vy,vw,vh,'#2f57a8'); px(vx,vy,vw,3,shade('#2f57a8',.28)); px(vx,vy,3,vh,shade('#2f57a8',.18)); // cabinet + sheen
  px(vx+vw-3,vy,3,vh,shade('#2f57a8',-.22));                                                          // right shade
  // lit header sign
  px(vx+4,vy+4,vw-8,13,'#0e1c44'); px(vx+4,vy+4,vw-8,1,'#3a5aa0');
  ctx.fillStyle='#ffd34d'; ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('REFRESH!', vx+5, vy+14);
  // glass display: 3 rows x 4 colorful bottles on lit shelves
  const gx=vx+4, gy=vy+19, gw=42, gh=54; ro(gx,gy,gw,gh,'#0e1530');
  const drinks=[PAL.red,PAL.mugB,PAL.yellow,PAL.leaf,PAL.orange,PAL.pink,PAL.mugC,'#8c5fd6','#22b9b9','#e673a8','#5bc05b','#3f74d6'];
  for(let r=0;r<3;r++){ const ry=gy+4+r*17;
    px(gx+1,ry+14,gw-2,2,'#243a6a');                                                                  // shelf
    for(let c=0;c<4;c++){ const idx=r*4+c, bxv=gx+3+c*10, col=drinks[idx];
      vendSlots.push({idx, bxv, ry, x0:bxv-1, y0:ry-1, x1:bxv+7, y1:ry+15, col});                     // click target
      if(vendDrops[idx]) continue;                                                                    // slot empty while its can is out
      px(bxv,ry+2,6,12,col); px(bxv,ry+2,6,2,shade(col,.32)); px(bxv+1,ry,3,3,col); } }               // bottle + cap
  px(gx+3,gy+2,2,gh-6,'rgba(255,255,255,.12)'); px(gx+8,gy+2,1,gh-6,'rgba(255,255,255,.06)');         // glass reflection
  // side panel: keypad + card reader + coin slot
  const spx=vx+48, spw=vw-(spx-vx)-4; px(spx,vy+19,spw,54,'#24407e'); px(spx,vy+19,spw,1,shade('#24407e',.3));
  for(let r=0;r<3;r++) for(let c=0;c<2;c++) px(spx+2+c*5,vy+23+r*5,3,3,'#cdd6dd');                     // keypad
  px(spx+1,vy+42,spw-2,11,'#0e1a36'); px(spx+2,vy+44,spw-4,2,'#cdd6dd');                               // card reader
  px(spx+2,vy+55,spw-4,3,'#0a1024');                                                                  // coin slot
  // dispense slot / tray at the bottom
  px(vx+5,vy+vh-13,vw-10,9,'#0e1c44'); px(vx+7,vy+vh-11,vw-14,5,'#0a1024');
  // clicked drinks fall from their slot into the tray, rest a few seconds, then restock (see tick())
  const _vnow=performance.now(), trayCX=vx+vw/2-3, trayTopY=vy+vh-22;   // rest: centered, poking out of the tray
  for(const k in vendDrops){ const dp=vendDrops[k], el=_vnow-dp.start;
    const pf=Math.min(1, el/620), ease=pf*pf;                            // accelerate downward (gravity)
    const cx0=dp.fromX+(trayCX-dp.fromX)*pf;                             // slide toward tray x
    let   cy0=dp.fromY+(trayTopY-dp.fromY)*ease;                         // fall with easing
    if(pf>=1){ const bt=Math.max(0,1-(el-620)/240); cy0-=Math.abs(Math.sin((el-620)*0.03))*4*bt; }    // small settle bounce
    px(cx0,cy0+2,6,12,dp.col); px(cx0,cy0+2,6,2,shade(dp.col,.32)); px(cx0+1,cy0,3,3,dp.col); }        // the dispensed can

  // ---- lounge: BIG wood table w/ fruit bowl + two white mugs, flanked by round
  // pink poufs (bottom-left). Sized to fill the corner; agents kept clear. ----
  const tx=66, ty=T+150, tw=116, tth=20;
  // round cushioned poufs -- a clear 3D cylinder: floor shadow, a darker rounded
  // side (lower ellipse + side band), a lighter domed cushion top, stitched seams
  // radiating from a centre button + a soft sheen.
  function pouf(cx0,cy0){
    const top='#d98fbe', side='#b06a96', sideDk='#8c4d79', sheen='#ecb6d6';
    const rx=18;
    ctx.fillStyle='rgba(0,0,0,.20)'; ctx.beginPath(); ctx.ellipse(cx0,cy0+14,rx+2,5,0,0,Math.PI*2); ctx.fill(); // floor shadow
    ctx.fillStyle=sideDk; ctx.beginPath(); ctx.ellipse(cx0,cy0+9,rx,7,0,0,Math.PI*2); ctx.fill();    // rounded base
    ctx.fillStyle=side;   ctx.fillRect(cx0-rx,cy0-2,rx*2,11);                                          // cylindrical side
    ctx.fillStyle=sideDk; ctx.fillRect(cx0-rx,cy0+6,rx*2,3);                                           // lower side shade
    ctx.fillStyle=top;    ctx.beginPath(); ctx.ellipse(cx0,cy0-2,rx,9,0,0,Math.PI*2); ctx.fill();      // domed cushion top
    ctx.fillStyle=sheen;  ctx.beginPath(); ctx.ellipse(cx0-6,cy0-4,8,4,0,0,Math.PI*2); ctx.fill();     // sheen
    ctx.strokeStyle=side; ctx.lineWidth=1;                                                             // seam dimples
    [[-12,3],[-5,5],[5,5],[12,3]].forEach(d=>{ ctx.beginPath(); ctx.moveTo(cx0,cy0-3); ctx.lineTo(cx0+d[0],cy0+d[1]); ctx.stroke(); });
    ctx.fillStyle=sideDk; ctx.beginPath(); ctx.ellipse(cx0,cy0-3,2,1.5,0,0,Math.PI*2); ctx.fill();     // centre button
  }
  pouf(tx-28, ty+10); pouf(tx+tw+28, ty+10);
  // table: floor shadow + front/back legs (with foot shadows) + grained top w/ shaded edges
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(tx+tw/2,ty+38,tw/2,8,0,0,Math.PI*2); ctx.fill();
  px(tx+22,ty+tth,4,18,PAL.woodDk); px(tx+tw-26,ty+tth,4,18,PAL.woodDk);            // back legs (inset)
  px(tx+10,ty+tth,5,22,PAL.wood); px(tx+10,ty+tth,2,22,PAL.woodHi);                 // front-left leg
  px(tx+tw-15,ty+tth,5,22,PAL.wood); px(tx+tw-15,ty+tth,2,22,PAL.woodHi);           // front-right leg
  px(tx+9,ty+tth+21,7,2,'rgba(0,0,0,.22)'); px(tx+tw-16,ty+tth+21,7,2,'rgba(0,0,0,.22)'); // foot shadows
  ro(tx,ty,tw,tth,PAL.wood); px(tx,ty,tw,4,PAL.woodHi); px(tx,ty+tth-3,tw,3,PAL.woodDk); // top + edges
  px(tx,ty+4,tw,1,shade(PAL.wood,.14));                                            // surface highlight band
  for(let g=0;g<tw-12;g+=13) px(tx+7+g,ty+9,9,1,shade(PAL.wood,-.09));              // grain hints
  // two white coffee mugs (left + right of the bowl)
  mug(tx+14,ty-5,PAL.paper); mug(tx+tw-21,ty-5,PAL.paper);
  // ---- central fruit bowl: ceramic bowl holding apples, a banana + leaves ----
  const bwx=tx+tw/2, bwy=ty-1, brw=22;
  // bowl body (exterior lower half) + shaded underside
  ctx.fillStyle='#ddd4bd'; ctx.beginPath(); ctx.ellipse(bwx,bwy,brw,10,0,0,Math.PI); ctx.fill();
  ctx.fillStyle=shade('#ddd4bd',-.22); ctx.beginPath(); ctx.ellipse(bwx,bwy+3,brw-3,6,0,0,Math.PI); ctx.fill();
  // rim ring at the opening with a shadowed interior
  ctx.fillStyle='#efe8d6'; ctx.beginPath(); ctx.ellipse(bwx,bwy-1,brw,5,0,0,Math.PI*2); ctx.fill();
  ctx.fillStyle='#3a342e'; ctx.beginPath(); ctx.ellipse(bwx,bwy-1,brw-4,3,0,0,Math.PI*2); ctx.fill();
  // fruit piled in the bowl (sitting above the rim line)
  blade(bwx-3,bwy-4,11,-3,PAL.leafDk); blade(bwx+2,bwy-5,12,2,PAL.leaf); blade(bwx+6,bwy-3,9,4,PAL.leafDk); // leaves
  px(bwx-2,bwy-12,14,4,PAL.yellow); px(bwx-3,bwy-11,2,3,PAL.yellow); px(bwx+12,bwy-11,2,3,shade(PAL.yellow,-.2)); px(bwx-3,bwy-12,3,1,shade(PAL.yellow,.3)); // banana
  function apple(ax,ay){ px(ax+1,ay,6,2,PAL.red); px(ax,ay+2,8,4,PAL.red); px(ax+1,ay+6,6,1,shade(PAL.red,-.25)); px(ax+1,ay+1,2,2,shade(PAL.red,.45)); px(ax+3,ay-1,1,2,PAL.leafDk); }
  apple(bwx-15,bwy-7); apple(bwx-3,bwy-6); apple(bwx+7,bwy-7);
  // thin front lip over the fruit bottoms so they nest inside the bowl
  ctx.fillStyle='#e7dfc9'; ctx.beginPath(); ctx.ellipse(bwx,bwy+1,brw,3,0,0,Math.PI); ctx.fill();
  px(bwx-brw,bwy-2,brw*2,1,'#f3eede');                                              // rim top highlight

  // ---- the beach: towels, umbrella, beach ball + the office mascot napping on sand ----
  drawBeachProps();
}

// a striped beach towel laid on the sand (finished agents rest on these)
function towel(x,y,col){
  px(x-1,y-1,32,16,PAL.outline);
  px(x,y,30,14,col);
  px(x,y,30,3,shade(col,.30));                             // top highlight
  px(x,y+11,30,3,shade(col,-.16));                         // shadow band
  for(let i=3;i<30;i+=8) px(x+i,y,3,14,shade(col,-.10));   // stripes
}
// a classic red/white beach umbrella; canopy floats above the resting agents
function beachUmbrella(x,y){
  const cx=x+24, r1='#e0533b', r2='#f6f6f8';
  px(cx-1,y+8,3,66,'#7a5a30'); px(cx-1,y+8,1,66,'#9a7440');            // pole
  const bands=[[54,20],[46,16],[36,12],[24,8],[12,4]];                 // widen toward the bottom
  for(const b of bands){ const w=b[0], yo=b[1];
    for(let i=0;i<w;i+=8) px(cx-w/2+i, y+yo, Math.min(8,w-i), 4, ((i>>3)%2)?r2:r1); }
  px(cx-27,y+22,54,1,PAL.outline);                                     // canopy rim
  px(cx-2,y+2,4,4,'#ffd34d');                                          // finial
}
let _sandGrains=null;                                                   // grain built once -> no per-frame flicker & no per-frame hashing
function drawBeachFloor(){
  const T=layout().kitchenTop, x0=BEACH_X, y0=T+30, y1=H, wx=W-22;
  const base='#e7d3a0', sandW=wx-x0, hgt=y1-y0;
  px(x0-1,y0,2,hgt,shade(PAL.base,-.10));                              // divider edge
  // --- dry sand: warm base + soft vertical gradient (paler/drier up near the wall) ---
  px(x0,y0,sandW,hgt,base);
  px(x0,y0,sandW,Math.round(hgt*0.30),shade(base,.05));               // dry top strip
  const _by=y0+Math.round(hgt*0.74); px(x0,_by,sandW,y1-_by,shade(base,-.05)); // warmer front
  // --- damp sand graduating toward the waterline on the right ---
  px(wx-11,y0,11,hgt,shade(base,-.06)); px(wx-5,y0,5,hgt,shade(base,-.13)); px(wx-2,y0,2,hgt,'#cfb77c');
  // --- fine grain: deterministic stipple, computed once from hash() (stable, no flicker) ---
  if(!_sandGrains){
    _sandGrains=[];
    for(let y=y0;y<y1;y+=4) for(let x=x0;x<wx-2;x+=4){
      const h=hash(x+'_'+y), r=h%11;
      if(r===0)      _sandGrains.push([x,y,1,1,'rgba(120,96,52,.22)']);         // dark grain
      else if(r===1) _sandGrains.push([x,y,1,1,'rgba(255,247,216,.30)']);       // light fleck
      else if(r===2 && (h>>>4)%5===0) _sandGrains.push([x,y,2,1,'rgba(150,122,64,.16)']); // pebble
    }
  }
  for(const g of _sandGrains) px(g[0],g[1],g[2],g[3],g[4]);
  // --- water strip + foam shoreline along the far-right edge (unchanged) ---
  for(let y=y0;y<y1;y+=6) px(wx,y,W-wx,6, ((y/6)&1)?'#49b0c8':'#57c2d8');
  px(wx,y0,W-wx,2,'rgba(255,255,255,.40)');                            // foam
  for(let y=y0+5;y<y1;y+=14) px(wx+3,y,6,1,'rgba(255,255,255,.5)');    // ripples
}
function drawBeachProps(){
  const T=layout().kitchenTop, y1=H, x0=BEACH_X;
  towel(x0+30, y1-58, '#e0533b'); towel(x0+96, y1-72, '#2f93d8'); towel(x0+66, y1-34, '#37b56c');
  beachUmbrella(x0+40, T+34);
  // beach ball
  const bx=x0+126, by=y1-28; px(bx-1,by-1,12,12,PAL.outline);
  px(bx,by,10,10,'#f6f6f8'); px(bx,by,5,5,PAL.red); px(bx+5,by+5,5,5,'#2f93d8'); px(bx,by+5,5,5,PAL.yellow);
  // the office mascot bear, now napping on the sand instead of on a couch
  ctx.save(); scaleAbout(x0+172, y1-40, 1.12); bearMascot(x0+158, y1-52); ctx.restore();
  drawBeachSign();
}

// a wooden "RETIRED AGENTS" signpost planted in the sand (between umbrella + REFRESH)
function drawBeachSign(){
  const T=layout().kitchenTop, cx=BEACH_X+136;
  const bw=84, bh=24, bx=cx-bw/2, by=T+32, groundY=T+96;
  px(cx-5, groundY-2, 10, 3, 'rgba(0,0,0,.15)');                    // sand contact shadow
  px(cx-2, by+bh, 4, groundY-(by+bh), PAL.woodDk); px(cx-2, by+bh,1, groundY-(by+bh), PAL.wood); // post
  px(bx-2,by-2,bw+4,bh+4,PAL.woodDk); ro(bx,by,bw,bh,'#cf9350');    // plank
  px(bx,by,bw,3,shade('#cf9350',.22)); px(bx,by+bh-3,bw,3,shade('#cf9350',-.20));
  for(let g=0;g<bw-10;g+=15) px(bx+7+g,by+13,11,1,shade('#cf9350',-.12));   // grain
  px(bx+4,by+4,2,2,PAL.metalDk); px(bx+bw-6,by+4,2,2,PAL.metalDk);          // nails
  ctx.fillStyle='#3a2410'; ctx.textAlign='center'; ctx.font='7px "Press Start 2P", monospace';
  ctx.fillText('RETIRED', cx, by+11); ctx.fillText('AGENTS', cx, by+20);
  ctx.textAlign='left';
}

// framed "DO GOOD WORK" poster (heart + 3 lines); pcx,pcy = top-left of the mat
function drawDoGoodWork(pcx, pcy){
  const pw=48, ph=46;
  px(pcx-3,pcy-3,pw+6,ph+6,'#15151a');                       // outer dark frame
  px(pcx-1,pcy-1,pw+2,ph+2,'#3c3c46');                       // frame bevel
  px(pcx+2,pcy+2,pw-4,ph-4,PAL.paper);                       // white mat
  px(pcx+2,pcy+2,pw-4,1,'#ffffff'); px(pcx+2,pcy+ph-3,pw-4,1,'#e2e2e8');
  const hx=pcx+pw/2, hy=pcy+6;
  px(hx-6,hy,4,3,PAL.pink); px(hx+2,hy,4,3,PAL.pink);
  px(hx-6,hy+3,12,2,PAL.pink); px(hx-5,hy+5,10,2,PAL.pink);
  px(hx-3,hy+7,6,2,PAL.pink);  px(hx-1,hy+9,2,1,PAL.pink);
  px(hx-5,hy+1,2,1,shade(PAL.pink,.45));
  ctx.fillStyle=PAL.ink; ctx.textAlign='center'; ctx.font='6px "Press Start 2P", monospace';
  ctx.fillText('DO',   hx, pcy+24); ctx.fillText('GOOD', hx, pcy+32); ctx.fillText('WORK', hx, pcy+40);
  ctx.textAlign='left';
}

// outlined rectangle (dark 1px border) - the key to the chunky pixel look
function ro(x,y,w,h,c){ px((x|0)-1,(y|0)-1,(w|0)+2,(h|0)+2,PAL.outline); px(x|0,y|0,w|0,h|0,c); }

// hair + headwear, drawn on a 14px-wide head whose top-left is (x-7, hy)
// a courier / baseball cap in one solid color -- shared so messengers look identical
// whether the sprite is drawn as male, female, seated or standing
function drawCap(x, hy, col){
  px(x-8,hy-3,16,5,col);              // dome sitting on the crown
  px(x-8,hy-3,16,1,shade(col,.35));   // top gloss
  px(x-9,hy,2,3,col); px(x+7,hy,2,3,col);   // side wrap over the ears
  px(x-14,hy+1,8,2,shade(col,-.15));  // front visor / brim
  px(x-8,hy+1,16,1,shade(col,-.22));  // band shadow
}
// a small envelope emblem (like ✉️) stamped on a courier's chest, centered on (cx,cy)
function drawEnvelope(cx, cy){
  const paper='#f4f4f6', edge='#3a3a44';
  px(cx-4, cy-3, 8, 6, paper);                              // body
  px(cx-4, cy-3, 8, 1, edge); px(cx-4, cy+2, 8, 1, edge);  // top + bottom border
  px(cx-4, cy-3, 1, 6, edge); px(cx+3, cy-3, 1, 6, edge);  // left + right border
  // flap: a shallow V from the top corners meeting in the middle
  px(cx-3,cy-2,1,1,edge); px(cx-2,cy-1,1,1,edge); px(cx-1,cy,1,1,edge);
  px(cx+2,cy-2,1,1,edge); px(cx+1,cy-1,1,1,edge); px(cx,cy,1,1,edge);
}
function drawHairAcc(x, hy, f){
  const hr=f.hair, hl=shade(hr,.34), hd=shade(hr,-.30);
  if(f.female){
    // rounded crown framing the face (clearly feminine), with shading
    px(x-8,hy-4,16,7,hr); px(x-8,hy-4,16,1,hd);          // crown + top outline
    px(x-9,hy+1,3,13,hr); px(x+6,hy+1,3,13,hr);          // long sides past the cheeks
    px(x-7,hy-3,9,1,hl); px(x-9,hy+1,2,5,hl);            // soft crown + side highlight
    px(x-6,hy-4,7,1,shade(hr,.55)); px(x+5,hy-2,2,6,hd); // bright top sheen + right-side depth
    px(x-9,hy+12,3,3,hd); px(x+6,hy+12,3,3,hd);          // tip shade
    if(f.femStyle===0){                                  // long flowing
      px(x-10,hy+12,3,7,hr); px(x+7,hy+12,3,7,hr); px(x+7,hy+5,1,11,hl); px(x-10,hy+17,3,2,hd);
    } else if(f.femStyle===1){                           // side ponytail
      px(x+8,hy,4,14,hr); px(x+9,hy+12,3,7,hr); px(x+7,hy-1,4,4,hr); px(x+9,hy+2,1,10,hl);
      px(x-5,hy-4,3,2,PAL.pink);                         // little clip
    } else if(f.femStyle===2){                           // bun + bow
      px(x-3,hy-8,6,5,hr); px(x-2,hy-7,3,1,hl);
      px(x-5,hy-9,3,3,PAL.pink); px(x+2,hy-9,3,3,PAL.pink); px(x-1,hy-8,2,2,PAL.pink);
    } else {                                             // high top-knot
      px(x-3,hy-10,6,5,hr); px(x-2,hy-10,4,1,hl); px(x-1,hy-12,2,2,hr);
      px(x-9,hy+1,3,8,hr); px(x+6,hy+1,3,8,hr);          // shorter tucked sides
    }
    if(f.acc===3){ px(x-9,hy+3,3,7,'#222'); px(x+6,hy+3,3,7,'#222'); px(x-8,hy-4,16,3,'#222'); } // headphones
    if(f.acc===2){ drawCap(x, hy, f.accCol); }           // cap (e.g. courier uniform)
    return;
  }
  // ---- men / neutral ----
  if(f.hairStyle!==2){ px(x-7,hy-3,14,6,hr); px(x-8,hy+1,2,7,hr); px(x+6,hy+1,2,7,hr);       // base + sideburns
    px(x-6,hy-4,12,1,hr);                                                                     // rounded crown
    px(x-7,hy-3,14,1,hd); px(x-5,hy-3,6,1,hl); px(x-6,hy-2,3,1,shade(hr,.5)); px(x+4,hy-2,2,5,hd); } // outline + sheen streak + temple depth
  if(f.hairStyle===1){ px(x-5,hy-7,3,5,hr); px(x-1,hy-8,3,6,hr); px(x+3,hy-7,3,5,hr); px(x-1,hy-8,2,1,hl); } // spiky
  else if(f.hairStyle===3){ px(x-2,hy-7,5,5,hr); px(x-1,hy-7,3,1,hl); }                                      // bun
  else if(f.hairStyle===4){ px(x-8,hy-4,16,8,hr); px(x-9,hy+4,2,6,hr); px(x+7,hy+4,2,6,hr);
    px(x-6,hy-3,5,1,hl); px(x-1,hy-4,4,1,hl); px(x+3,hy-3,3,1,hl); }                                         // curly mop
  else if(f.hairStyle===5){ px(x-1,hy-8,4,9,hr); px(x-1,hy-8,2,1,hl); }                                      // mohawk
  else if(f.hairStyle===6){ px(x-2,hy-4,1,5,hd); px(x-6,hy-3,4,1,shade(hr,.5)); px(x+1,hy-3,5,1,hl); }        // side part
  else if(f.hairStyle===7){ px(x-8,hy-6,16,4,hr); px(x-9,hy-2,3,5,hr); px(x+6,hy-2,3,5,hr);
    px(x-6,hy-6,10,1,hl); px(x-8,hy-6,16,1,hd); }                                                             // afro / big volume
  else if(f.hairStyle===0){ px(x-7,hy-4,14,4,hr); px(x-6,hy-3,7,1,hl); }                                     // flat
  if(f.acc===2){ drawCap(x, hy, f.accCol); }                                                   // cap
  else if(f.acc===3){ px(x-8,hy-2,16,3,'#222'); px(x-10,hy+3,3,8,'#222'); px(x+7,hy+3,3,8,'#222'); } // headphones
  else if(f.acc===4){ px(x-8,hy-4,16,8,f.accCol); px(x-8,hy+3,16,2,'rgba(0,0,0,.25)'); }      // beanie
  else if(f.acc===5){ px(x-1,hy-8,2,7,'#9aa'); px(x-2,hy-11,4,4,PAL.red); }                   // antenna
}
function drawFace(x, hy, f, beach){
  const sk=f.skin;
  // ears
  px(x-9,hy+5,2,4,sk); px(x-9,hy+5,1,4,PAL.outline);
  px(x+7,hy+5,2,4,sk); px(x+8,hy+5,1,4,PAL.outline);
  // soft roundness: shadow down the right cheek, highlight on the upper-left,
  // and a gentle chin shade -- gives the face dimension across every skin tone
  px(x+4,hy,3,11,'rgba(60,40,25,.12)');
  px(x-6,hy,2,5,'rgba(255,255,255,.16)');
  px(x-6,hy+11,12,1,'rgba(60,40,25,.12)');
  // relaxed, slightly raised eyebrows (friendly, never angled-down)
  px(x-5,hy+2,3,1,'rgba(70,50,40,.55)'); px(x+2,hy+2,3,1,'rgba(70,50,40,.55)');
  if(beach){ // dark sunglasses (beach only) -- two tinted lenses + a bridge
    px(x-6,hy+4,5,4,'#15151a'); px(x+1,hy+4,5,4,'#15151a'); px(x-1,hy+5,2,1,'#15151a');
    px(x-5,hy+4,2,1,'rgba(120,200,230,.55)'); px(x+2,hy+4,2,1,'rgba(120,200,230,.55)'); // lens glint
  } else if(f.acc===1){ // glasses (over the eyes)
    px(x-6,hy+5,5,4,'#1b1b1b'); px(x+1,hy+5,5,4,'#1b1b1b'); px(x-1,hy+6,2,1,'#1b1b1b');
    px(x-5,hy+5,3,3,'#eaf6ff'); px(x+2,hy+5,3,3,'#eaf6ff');
    px(x-4,hy+6,1,1,'#101010'); px(x+3,hy+6,1,1,'#101010');
  } else { // open eyes -- with an occasional blink (staggered per sprite by x)
    const blink = ((performance.now() + ((x*131)&1023)*4) % 3400) < 130;
    if(blink){
      px(x-5,hy+6,3,1,PAL.outline); px(x+2,hy+6,3,1,PAL.outline);   // closed (mid-blink)
    } else {
      px(x-5,hy+5,3,3,'#ffffff'); px(x+2,hy+5,3,3,'#ffffff');
      px(x-4,hy+6,2,2,PAL.outline); px(x+3,hy+6,2,2,PAL.outline);
      px(x-4,hy+5,1,1,'#ffffff'); px(x+3,hy+5,1,1,'#ffffff'); // catch-light sparkle
    }
  }
  // eyelashes for women (outer corners)
  if(f.female){ px(x-6,hy+4,1,1,PAL.outline); px(x+6,hy+4,1,1,PAL.outline); }
  // small nose
  px(x,hy+8,1,2,'rgba(0,0,0,.20)');
  // HAPPY upturned smile: base line low in the middle, corners curving UP
  const mc='#6e352f';
  px(x-1,hy+11,3,1,mc);                 // bottom of the curve (middle, lowest)
  px(x-2,hy+10,1,1,mc); px(x+2,hy+10,1,1,mc);   // sides rising
  px(x-3,hy+9,1,1,mc);  px(x+3,hy+9,1,1,mc);    // corners turned UP
  px(x-1,hy+12,3,1,'rgba(214,90,110,.55)');     // warm lower-lip hint
  // rosy cheeks
  px(x-6,hy+8,2,2,'rgba(232,120,120,.55)'); px(x+5,hy+8,2,2,'rgba(232,120,120,.55)');
}

// a little tropical cocktail (glass + drink + straw + paper umbrella); cy = glass base
function drawCocktail(cx, cy){
  const glass='#d5edf5', drink='#f39a3a';
  px(cx-2,cy-6,5,6,glass);            // glass body
  px(cx-2,cy-6,5,1,'#eef8fb');        // rim highlight
  px(cx-1,cy-5,3,4,drink);            // drink
  px(cx+2,cy-5,1,4,'#b7d5df');        // glass shade
  px(cx-2,cy,5,1,'#b7d5df');          // base
  px(cx+2,cy-11,1,6,'#37b56c');       // straw
  px(cx-1,cy-12,6,1,'#e0533b'); px(cx,cy-11,4,1,'#f6f6f8'); px(cx+1,cy-10,2,1,'#2f93d8'); // paper umbrella
}

// a finished agent relaxing on the sand: seated, shades on, cocktail in hand.
// Only used for beach agents once they've settled, so the vacation look never
// leaks into the kitchen or the desks.
function drawBeachSitter(p, t){
  const x=Math.round(p.x), y=Math.round(p.y);   // y = where they sit on the sand
  const f=p.feat||featuresFor(p.id||'x');
  const sk=f.skin, sh=f.shirt, pants=f.pants, shoe='#4a3526';
  ctx.fillStyle='rgba(0,0,0,.18)'; ctx.beginPath(); ctx.ellipse(x,y+8,15,4,0,0,Math.PI*2); ctx.fill(); // shadow
  // legs stretched out on the sand + feet at the ends
  ro(x-11, y+2, 22, 6, pants); px(x-11,y+2,22,1,shade(pants,.18)); px(x-11,y+7,22,1,shade(pants,-.14));
  px(x-14, y+3, 5, 4, shoe); px(x+9, y+3, 5, 4, shoe);
  px(x-14,y+3,5,1,shade(shoe,.3)); px(x+9,y+3,5,1,shade(shoe,.3));
  // seated torso
  ro(x-8, y-9, 16, 13, sh);
  px(x-8,y-9,16,2,shade(sh,.30)); px(x+5,y-8,3,11,shade(sh,-.20)); px(x-8,y+2,16,2,shade(sh,-.16));
  px(x-2,y-9,4,2,shade(sh,-.28));                              // collar
  torsoDetail(x, y-9, 8, 13, sh, f);                          // outfit variety + sheen
  // left arm propped back on the sand
  ro(x-12, y-6, 5, 8, sh); px(x-12, y+1, 5, 3, sk);
  // right arm raised, holding the cocktail
  ro(x+7, y-8, 5, 7, sh); px(x+8, y-3, 4, 3, sk);
  drawCocktail(x+12, y-1);
  // neck + head
  px(x-3, y-13, 6, 4, sk); px(x-3,y-13,6,1,'rgba(0,0,0,.16)');
  ro(x-7, y-26, 14, 15, sk);
  px(x-7,y-12,14,1,'rgba(0,0,0,.10)');
  drawHairAcc(x, y-24, f); drawFace(x, y-24, f, true);        // sunglasses ON (beach only)
}

// a full workstation: office chair + desk + monitor + filing cabinet + plant,
// with (optionally) a worker seated behind it, facing us. Even empty it looks furnished.
function drawDeskPod(x, y, p, t){
  const f = p ? (p.feat||featuresFor(p.id)) : null;
  // a seated worker "works" (types, its screen animates, its mug steams) only while its OWN
  // turn is active; when it is merely working because a subagent / workflow is live it sits
  // still with a dimmed standby screen, so only the helper dwarves animate (item 8).
  const selfActive = !p || !p.agent || p.agent.self_active !== false;
  const whipped = !!(p && p.whipUntil && performance.now()<p.whipUntil);   // "work harder": faster typing/scroll + a shudder
  // --- soft contact shadow on the floor under the whole workstation ---
  ctx.fillStyle='rgba(0,0,0,.14)'; ctx.beginPath(); ctx.ellipse(x, y+26, 35, 6, 0, 0, Math.PI*2); ctx.fill();
  // --- rolling office chair: gas post + 5-star wheel base (peeks below the desk) ---
  px(x-2,y+10,4,14,PAL.metalDk);                                       // gas post
  px(x-18,y+23,36,2,shade(PAL.metalDk,.14));                           // hub bar
  px(x-18,y+24,4,4,'#2b2b30'); px(x-10,y+25,4,4,'#2b2b30');
  px(x-2,y+25,4,4,'#2b2b30'); px(x+6,y+25,4,4,'#2b2b30'); px(x+14,y+24,4,4,'#2b2b30'); // 5 wheels
  // --- curved padded backrest + armrests (behind the worker) ---
  ro(x-13, y-23, 26, 21, PAL.chairW);
  px(x-10,y-26,20,4,PAL.chairW); px(x-10,y-27,20,1,PAL.outline);        // rounded headrest cap
  px(x-13,y-23,26,3, shade(PAL.chairW,.20)); px(x-13,y-6,26,3, shade(PAL.chairW,-.22));
  px(x-14,y-20,2,15, shade(PAL.chairW,-.12)); px(x+12,y-20,2,15, shade(PAL.chairW,-.12)); // side bolsters
  px(x-18,y-4,5,8, shade(PAL.chairW,-.10)); px(x+13,y-4,5,8, shade(PAL.chairW,-.10));     // armrests
  if(p){
    const sh=f.shirt, sk=f.skin;
    // celebration: a little seated bounce while the flag is live (visual only;
    // hitbox uses deskX/deskY, so a transient offset is safe)
    const hop=(p.celebrateUntil && performance.now()<p.celebrateUntil)
      ? -Math.abs(Math.sin(performance.now()*0.018))*4 : 0;
    const flin=whipped ? Math.sin(performance.now()*0.06)*1.6 : 0;   // whip: a brief startled shudder
    const x=Math.round(arguments[0]+flin), y=Math.round(arguments[1]+hop); // shadow desk x/y for the worker BODY only
    // torso (soft shaded shirt + collar)  -- anchors UNCHANGED (hitbox-critical)
    ro(x-11, y-12, 22, 16, sh);
    px(x-11,y-12,22,2, shade(sh,.30)); px(x+7,y-11,3,14, shade(sh,-.20)); px(x-11,y+2,22,2, shade(sh,-.16));
    px(x-2,y-12,4,2, shade(sh,-.28));
    torsoDetail(x, y-12, 11, 16, sh, f);                                // outfit variety + sheen
    if(f.messenger){ drawEnvelope(x, y-5); }                            // courier envelope badge
    // typing arms -- frozen when the parent is idle-waiting on a subagent (selfActive above)
    const tap = selfActive ? (Math.floor(t*(whipped?1.1:0.4))&1) : 0;
    ro(x-15, y-2+tap, 6, 8, sh); ro(x+9, y-2+(1-tap), 6, 8, sh);
    px(x-14, y+5+tap, 5,3, sk); px(x+10, y+5+(1-tap), 5,3, sk);
    // neck + head  -- anchors UNCHANGED (hitbox-critical)
    px(x-3, y-15, 6, 4, sk); px(x-3, y-15, 6, 1, 'rgba(0,0,0,.16)');
    ro(x-7, y-28, 14, 15, sk);
    px(x-7,y-14,14,1,'rgba(0,0,0,.10)');                                // soft jaw shade
    drawHairAcc(x, y-26, f); drawFace(x, y-26, f);
  }
  // --- wood desk top: bright surface + grain hint + shaded front edge ---
  px(x-26,y+1,52,4,PAL.woodHi);                                         // bright top surface
  ro(x-26, y+5, 52, 6, PAL.wood); px(x-26,y+5,52,2, shade(PAL.wood,.22));
  for(let g=0; g<46; g+=11) px(x-22+g,y+7,7,1, shade(PAL.wood,-.10));    // grain
  px(x-26,y+10,52,2,PAL.woodDk);                                        // shaded front edge
  // --- grey TWO-DRAWER pedestal under the left side + a right leg ---
  const pbx=x-24; ro(pbx, y+11, 20, 15, PAL.metal); px(pbx,y+11,20,2,PAL.steel);
  px(pbx+1,y+13,18,5, shade(PAL.metal,.05)); px(pbx+1,y+19,18,5, shade(PAL.metal,-.07)); // drawer faces
  px(pbx+6,y+15,8,1,PAL.metalDk); px(pbx+6,y+21,8,1,PAL.metalDk);       // drawer handles
  px(x+19,y+11,3,14,PAL.woodDk);                                        // right desk leg
  // --- chunkier monitor on a stand with a soft screen glow ---
  const mx=x-23, my=y-16, mw=26;
  ctx.fillStyle='rgba(150,222,236,.16)'; ctx.fillRect(mx-2,my-1,mw+4,18);  // glow halo
  px(x-11,y-1,4,3,PAL.monitorLip); px(x-15,y+2,12,2,PAL.monitorLip);       // stand + base
  ro(mx, my, mw, 16, PAL.monitor); px(mx,my,mw,2, shade(PAL.monitor,.5));
  if(p){ const tints=['#7fd3e0','#9fe0c0','#7fb0e0','#cfe9a0'];
    const fr = selfActive ? Math.floor((t*(whipped?0.34:0.12)+p.seed)%4) : 0;            // freeze frame when idle
    px(mx+2,my+2,mw-4,12, selfActive ? tints[fr] : '#586a72');           // bright code vs dim standby
    px(mx+3,my+4,16,2,PAL.ink); px(mx+3,my+7,10,2,PAL.ink); px(mx+3,my+10,19,2,PAL.ink);
    px(mx+2,my+2,mw-4,1,'rgba(255,255,255,.22)');                         // screen gloss
  } else { px(mx+2,my+2,mw-4,12,'#39404a'); px(mx+4,my+7,12,2,'#4a525d'); } // dim when empty
  // keyboard + mouse on the desk top
  px(x-15,y+1,20,4,'#d3dae0'); px(x-15,y+1,20,1,'#fff'); for(let k=0;k<5;k++) px(x-13+k*4,y+3,2,1,'#aeb6bd');
  px(x+8,y+2,4,3,'#d3dae0');
  // little terracotta desk plant (right) + paper stack
  px(x+13,y-4,9,6,PAL.pot); px(x+13,y-4,9,2,shade(PAL.pot,.18)); px(x+12,y,11,1,PAL.potDk);
  blade(x+15,y-4,9,-2,PAL.leafDk); blade(x+17,y-4,12,0,PAL.leaf); blade(x+19,y-4,8,2,PAL.leafDk);
  px(x-22,y+6,9,5,PAL.paper); px(x-22,y+6,9,1,'#e6e6ec'); px(x-21,y+8,7,1,'#cfcfd6');
  // mug on the desk; steam rises only while the worker is actively at its own turn
  if(p){ mug(x+3, y-1, PAL.mugC);
    if(selfActive) for(let i=0;i<3;i++){ const yy=y-3-((t*1.0+i*5)%8); px(x+5,yy,1,2,'rgba(255,255,255,.5)'); } }
  // desk name-plate: the agent's task on a little white placard in front of the desk,
  // white-board look like the workflow easel; wrapped by LETTER (packs the most text in)
  // in a slightly smaller font (item 7).
  if(p && p.agent && p.agent.title){
    ctx.font='4px "Press Start 2P", monospace';
    const plLines = wrapChars(p.agent.title, 50, 2, '');       // no trailing ellipsis
    const pw=56, ph=5*plLines.length+3, plx=x-pw/2, ply=y+30;   // centered, below the chair wheels
    ro(plx, ply, pw, ph, PAL.paper);                            // white plate + dark ro() outline
    px(plx+1, ply+1, pw-2, 1, shade(PAL.paper,-.08));
    ctx.fillStyle=PAL.ink; ctx.textAlign='center';
    // vertically centre the 1-2 lines: 4px glyphs (~4px ascent) on a 5px line step give a
    // text block 5n-1 tall, so first baseline ply+6 leaves equal ~2px padding top & bottom.
    let ppy=ply+6; for(const ln of plLines){ ctx.fillText(ln, x, ppy); ppy+=5; }
    ctx.textAlign='left';
  }
  // running subagents: a helper dwarf digging away next to the desk (one per subagent).
  // We also register a hover region so you can see what each one is doing.
  if(p && p.agent && p.agent.subs>0){
    const subs=p.agent.subagents||[]; const n=Math.min(p.agent.subs,4);
    for(let i=0;i<n;i++){
      const cx=x-40-i*22, cy=y+15;
      drawHelper(cx, cy, t, (hash(p.id)+i*7)%997);
      // pod is drawn scaled by SC about (x,y); convert the dwarf centre to mouse-logical coords
      helperHits.push({ x: x+(cx-x)*SC, y: y+((cy-6)-y)*SC, r: 15*SC, sub: subs[i]||null });
      const sb0 = subs[i] && subs[i].id ? subBubbles[subs[i].id] : null;
      if(sb0){ const lo=(i&1)===1;   // stagger: even dwarf -> above the hat, odd -> below the face
        bubbleAnchors.push({ x: x+(cx-x)*SC, y: y+((cy+(lo?2:-15))-y)*SC, text:sb0.text, start:sb0.start, until:sb0.until, below:lo, tool:sb0.tool }); }
    }
  }
  // dynamic-workflow easel (drawn beside the desk; returns its hover hit centre)
  if(p && p.agent && p.agent.workflows && p.agent.workflows.length){
    const hit = drawWorkflowTent(x, y, p.agent.workflows, t);
    if(hit) workflowHits.push({ x: x+(hit.x-x)*SC, y: y+(hit.y-y)*SC, r: hit.r*SC, workflow: p.agent.workflows });
  }
  // open background shells: up to 3 tiny terminal windows in a row just above the desk
  // name-plate, filling left -> middle -> right. Hover shows the command + output tail.
  if(p && p.agent && p.agent.shells && p.agent.shells.length){
    const shells=p.agent.shells, n=Math.min(shells.length,3);
    for(let i=0;i<n;i++){
      // shells[] is newest-first -> draw oldest at the leftmost slot so they fill L->R in the
      // order the shells were opened. 22px pitch on 17px windows -> ~5px gap between them.
      const slot=n-1-i, sx=x-30+slot*22, sy=y+8;    // row bottom (sy+12) clears the name-plate (y+30) with a ~10px local gap
      drawShellWin(sx, sy, t, (hash(p.id)+i*5)%997);
      shellHits.push({ x: x+((sx+8)-x)*SC, y: y+((sy+6)-y)*SC, r: 11*SC, shell: shells[i] });
    }
  }
}

// a small "open shell" terminal window humming above the desk: a dark CRT with a title
// bar, a green prompt/command line, an output line, and a blinking cursor. One per running
// background shell (up to 3). Drawn in the pod's local frame (scaled by SC with the desk).
function drawShellWin(sx, sy, t, seed){
  sx=Math.round(sx); sy=Math.round(sy);
  const w=17, h=12;
  px(sx+1, sy+h, w, 1, 'rgba(0,0,0,.28)');                 // drop shadow
  ro(sx, sy, w, h, '#111620');                             // dark terminal body (+ dark outline)
  px(sx+1, sy+1, w-2, 3, '#2b313d');                       // title bar
  px(sx+2, sy+2, 1,1, '#e0564e'); px(sx+4, sy+2, 1,1, '#e0a53e'); px(sx+6, sy+2, 1,1, '#5fbf5a'); // 3 dots
  px(sx+2, sy+6, 1,1, '#63e6a0');                          // green ">" prompt
  px(sx+4, sy+6, 8,1, '#3c7a58');                          // dim command echo
  px(sx+2, sy+9, 10,1, '#356b4e');                         // output line
  if((Math.floor(t*0.10)+seed)&1) px(sx+13, sy+6, 2,1, '#a6f2c6');  // blinking cursor
}

// a helper "subagent" dwarf: pointy hat, beard, tunic with belt, boots, swinging a
// pickaxe over a little dirt mound. One is drawn per running subagent, animated.
function drawHelper(cx, cy, t, seed){
  const bob = (Math.floor(t*0.22+seed)&1);                 // gentle bob
  const y = cy - bob;
  const up = (Math.floor(t*0.40+seed)&1);                  // pickaxe raised / struck
  px(cx-6, cy+7, 14, 2, 'rgba(0,0,0,.22)');                // ground shadow
  px(cx+4, cy+4, 7, 3, '#8a5a30'); px(cx+4, cy+4, 7, 1, '#a06a3a'); // little dirt mound
  // boots
  px(cx-4, cy+4, 3, 3, '#3a2a18'); px(cx+1, cy+4, 3, 3, '#3a2a18');
  // tunic (green) + belt + buckle
  px(cx-5, y-2, 10, 7, '#4f7d3a'); px(cx-5,y-2,10,1,'#67a04c'); px(cx-5,y+4,10,1,'#3c612c');
  px(cx-5, y+2, 10, 1, '#6b4a2a'); px(cx-1, y+1, 2, 2, '#caa33a');
  // arms + hands
  px(cx-6, y, 2, 4, '#4f7d3a'); px(cx+5, y, 2, 4, '#4f7d3a');
  px(cx-6, y+3, 2, 2, '#f0d2a8'); px(cx+5, y+3, 2, 2, '#f0d2a8');
  // face + big white beard + eyes + rosy nose
  px(cx-3, y-6, 7, 4, '#f0d2a8');
  px(cx-4, y-2, 9, 3, '#eef0f4'); px(cx-3, y+1, 7, 1, '#dcdfe6');
  px(cx-2, y-5, 1, 1, PAL.outline); px(cx+2, y-5, 1, 1, PAL.outline);
  px(cx-1, y-4, 2, 1, '#d98f7a');
  // pointy red hat with brim + pom
  px(cx-5, y-8, 11, 2, '#a83226');
  px(cx-3, y-10, 7, 2, '#c0392b'); px(cx-2, y-12, 5, 2, '#c0392b'); px(cx-1, y-14, 3, 2, '#d2452f'); px(cx, y-16, 1, 2, '#d2452f');
  px(cx, y-16, 1, 1, '#f4f4f4');
  // pickaxe
  if(up){ px(cx+7, y-6, 2, 8, '#8a5a30'); px(cx+5, y-7, 6, 2, '#aab2ba'); px(cx+5,y-7,2,1,'#cdd6dd'); }
  else  { px(cx+7, y+1, 2, 6, '#8a5a30'); px(cx+7, y+6, 6, 2, '#aab2ba');
          px(cx+11, y+5, 1, 1, 'rgba(150,110,60,.6)'); px(cx+9, y+7, 1, 1, 'rgba(150,110,60,.5)'); }
}

// dynamic-workflow easel: a little whiteboard on legs beside the desk showing the
// workflow name (wrapped, mid-word if a token is too long), a big WHITE done/total
// count, and 1-3 tiny helper dwarves at its base (one per running agent). Only drawn
// while something is running. Returns the hover hit centre (local coords) or null.
// slug -> human title: "f2-deterministic-noat-trigger" -> "F2 Deterministic Noat Trigger".
// Keeps ALL-CAPS tokens as-is (API, MCP, CI); the full summary still lives in the hover card.
function humanizeWf(s){
  s = String(s||'').replace(/[_\-]+/g,' ').replace(/\s+/g,' ').trim();
  if(!s) return 'Workflow';
  return s.split(' ').map(w => (w===w.toUpperCase() ? w : (w[0].toUpperCase()+w.slice(1)))).join(' ');
}
function drawWorkflowTent(x, y, workflows, t){
  if(!workflows || !workflows.length) return null;   // backend already gates to genuinely-live runs
  // a WHITE whiteboard (like the wall inspiration board), floating a few px above the desk
  // on easel legs. Always to the RIGHT of the desk with a small horizontal gap so it reads
  // as "beside" the desk, not sitting on it; desks are ~216px apart so adjacent easels
  // never collide, and the far-right column clips only a few px past the edge.
  const bw=44, bh=40, cxT = x + 56, byT = y - 46, bxT = cxT - bw/2;   // left edge clears the desk + the above desk's name-plate (which reaches anchor+42px on screen)
  // easel: just the 2 side legs (no middle leg), each on a little caster wheel
  const legH = (y+22) - (byT + bh - 2);
  px(bxT+4, byT+bh-2, 2, legH-2, PAL.woodDk); px(bxT+bw-6, byT+bh-2, 2, legH-2, PAL.woodDk);
  const wheel=(wx)=>{ px(wx-2, y+21, 6,2,'rgba(0,0,0,.20)');          // floor shadow
                      px(wx-2, y+18, 5,4, '#2b2f36'); px(wx-1, y+19, 3,2, '#565c66'); }; // dark caster + hub
  wheel(bxT+5); wheel(bxT+bw-5);
  // white board face (ro() paints the 1px dark outline for free) + light-grey header strip
  ro(bxT, byT, bw, bh, PAL.paper);
  px(bxT+1, byT+bh-2, bw-2, 1, 'rgba(0,0,0,.10)');                    // faint bottom shade
  px(bxT+1, byT+1, bw-2, 7, shade(PAL.paper,-.10));
  ctx.fillStyle=PAL.ink; ctx.textAlign='center'; ctx.font='4px "Press Start 2P", monospace';
  ctx.fillText(workflows.length>1?'WORKFLOWS':'WORKFLOW', cxT, byT+6);
  // workflow name (or "N runs" when several share a desk), wrapped mid-word, max 3 lines.
  // small font (matches the desk name-plate), tight side inset, no trailing ellipsis.
  const wname = workflows.length>1 ? (workflows.length+' runs') : humanizeWf(workflows[0].name);
  ctx.fillStyle=PAL.ink; ctx.font='4px "Press Start 2P", monospace';
  const nameLines = wrapTextMid(wname, bw-4, 3, '');
  // vertically centre the name in the band between the header strip and the count
  const nblk = 5*nameLines.length - 1;                       // 4px glyphs on a 5px step
  const bandTop = byT+9, bandBot = byT+bh-10;                // header strip ends ~byT+8; count sits at the bottom
  let ty = Math.round(bandTop + (bandBot-bandTop-nblk)/2) + 4;   // +4 ascent -> first baseline
  for(const ln of nameLines){ ctx.fillText(ln, cxT, ty); ty+=5; }
  // progress: done/total in dark ink
  const done=workflows.reduce((s,w)=>s+(w.done||0),0);
  const total=workflows.reduce((s,w)=>s+(w.total||0),0);
  const running=workflows.reduce((s,w)=>s+(w.running||0),0);
  ctx.fillStyle=PAL.ink; ctx.font='bold 7px "Press Start 2P", monospace';
  ctx.fillText(done+'/'+total, cxT, byT+bh-4);
  ctx.textAlign='left';
  // tiny helper dwarves at the easel base (one per running agent, capped 3, 0.7 scale)
  const n=Math.min(3, running);
  const acts=workflows.reduce((L,w)=>L.concat(w.active||[]),[]);   // flatten running-sub infos
  for(let i=0;i<n;i++){
    const hx=cxT - (n-1)*8 + i*16, hy=y+18;
    ctx.save(); scaleAbout(hx, hy, 0.7); drawHelper(hx, hy, t, (hash(wname)+i*7)%997); ctx.restore();
    // each easel dwarf IS a running workflow subagent -> its own hover region showing what
    // it's doing (not the whole-workflow tooltip). Small radius so the board still hovers
    // as the workflow; the easel hit below is shrunk to the board so these win at the base.
    helperHits.push({ x: x+(hx-x)*SC, y: y+((hy-4)-y)*SC, r: 10*SC, sub: acts[i]||null });
    const sbw = acts[i] && acts[i].id ? subBubbles[acts[i].id] : null;
    if(sbw){ const lo=(i&1)===1;   // stagger easel dwarves: even -> above the hat, odd -> below the face
      bubbleAnchors.push({ x: x+(hx-x)*SC, y: y+((hy+(lo?1:-12))-y)*SC, text:sbw.text, start:sbw.start, until:sbw.until, below:lo, tool:sbw.tool }); }
  }
  return { x: cxT, y: y-26, r: 26 };   // hit only the board face, not the dwarves at its base
}

// wrap `text` to <= maxLines lines that each fit `maxW` px at the CURRENT ctx.font,
// breaking INSIDE a word when a single token is too long. `ell` is the clip marker
// appended when the text overflows maxLines -- pass '' to truncate with no marker.
function wrapTextMid(text, maxW, maxLines, ell){
  ell = (ell===undefined ? '…' : ell);
  const fits = s => ctx.measureText(s).width <= maxW;
  const words = String(text).split(/\s+/).filter(Boolean);
  const lines=[]; let cur='';
  const flush=()=>{ if(cur){ lines.push(cur); cur=''; } };
  for(let w of words){
    while(!fits(w) && w.length>1){                 // hard-break an over-long token
      flush();
      let i=1; while(i<w.length && fits(w.slice(0,i+1))) i++;
      lines.push(w.slice(0,i)); w=w.slice(i);
    }
    const cand = cur ? cur+' '+w : w;
    if(fits(cand)) cur=cand; else { flush(); cur=w; }
  }
  flush();
  if(maxLines && lines.length>maxLines){
    const out=lines.slice(0,maxLines);
    let last=out[maxLines-1];
    while(last.length>1 && !fits(last+ell)) last=last.slice(0,-1);
    out[maxLines-1]=last+ell;
    return out;
  }
  return lines;
}

// pack `text` into <= maxLines lines that each fit `maxW` px at the CURRENT ctx.font,
// breaking at ANY character (fills the most text per line -- used by the desk name-plate).
// `ell` is the clip marker appended on overflow -- pass '' to truncate with no marker.
function wrapChars(text, maxW, maxLines, ell){
  ell = (ell===undefined ? '…' : ell);
  const fits = s => ctx.measureText(s).width <= maxW;
  const s = String(text); const lines=[]; let cur='';
  for(const ch of s){
    if(cur && !fits(cur+ch)){ lines.push(cur); cur=''; }
    cur += ch;
  }
  if(cur) lines.push(cur);
  if(maxLines && lines.length>maxLines){
    const out=lines.slice(0,maxLines);
    let last=out[maxLines-1];
    while(last.length && !fits(last+ell)) last=last.slice(0,-1);
    out[maxLines-1]=last+ell;
    return out;
  }
  return lines;
}

// first ~90 chars, whitespace-collapsed (drawBubble wraps + ellipsizes the rest)
function firstWords(s){ s=String(s||'').replace(/\s+/g,' ').trim(); return s.length>90?s.slice(0,90):s; }
// small white speech bubble centred on (x,y) in SCREEN coords. Tail points DOWN to the
// anchor (bubble sits above) unless `below` is set, in which case it sits below with an
// up-pointing tail -- used to stagger neighbouring dwarf bubbles so they don't overlap.
function drawBubble(x, y, text, alpha, below){
  if(!text || alpha<=0) return;
  ctx.save();
  ctx.globalAlpha = Math.max(0, Math.min(1, alpha));
  ctx.font = '4px "Press Start 2P", monospace';
  const lines = wrapTextMid(text, 78, 3, '…');       // reuse existing word-wrap + ellipsis
  let tw=0; for(const ln of lines) tw=Math.max(tw, ctx.measureText(ln).width);
  const padX=4, padY=3, lh=6;
  const bw=Math.max(14, Math.ceil(tw)+padX*2), bh=lh*lines.length+padY*2-1;
  const bx=Math.round(x-bw/2), by=Math.round(below ? y+4 : y-bh);
  ro(bx, by, bw, bh, PAL.paper);                     // white box + 1px dark outline
  px(bx+1, by+1, bw-2, 1, shade(PAL.paper,-.06));    // faint header shade
  const tx=Math.round(x);
  if(below){                                         // upward pixel tail (box hangs below)
    px(tx-2, by-1, 4,1, PAL.paper); px(tx-1, by-2, 2,1, PAL.paper); px(tx, by-3, 1,1, PAL.paper);
    px(tx-3, by-1, 1,1, PAL.outline); px(tx+2, by-1, 1,1, PAL.outline);
    px(tx-2, by-2, 1,1, PAL.outline); px(tx+1, by-2, 1,1, PAL.outline);
    px(tx-1, by-3, 1,1, PAL.outline); px(tx+1, by-3, 1,1, PAL.outline);
    px(tx-1, by-4, 2,1, PAL.outline);
  } else {                                           // downward pixel tail (box sits above)
    px(tx-2, by+bh, 4,1, PAL.paper); px(tx-1, by+bh+1, 2,1, PAL.paper); px(tx, by+bh+2, 1,1, PAL.paper);
    px(tx-3, by+bh, 1,1, PAL.outline); px(tx+2, by+bh, 1,1, PAL.outline);
    px(tx-2, by+bh+1, 1,1, PAL.outline); px(tx+1, by+bh+1, 1,1, PAL.outline);
    px(tx-1, by+bh+2, 1,1, PAL.outline); px(tx+1, by+bh+2, 1,1, PAL.outline);
    px(tx-1, by+bh+3, 2,1, PAL.outline);
  }
  ctx.fillStyle=PAL.ink; ctx.textAlign='center';
  let ty=by+padY+4; for(const ln of lines){ ctx.fillText(ln, x, ty); ty+=lh; }
  ctx.textAlign='left'; ctx.restore();
}
// accent colour for a tool chip, by tool family -- so the same class of action reads the same.
function toolColor(name){
  const n=(name||'').toLowerCase();
  if(/bash|shell|exec|run|terminal|command/.test(n)) return '#6ad06a';        // green: run
  if(/edit|write|replace|create|apply|notebook|patch/.test(n)) return '#f0a23b'; // orange: write
  if(/read|cat|open|view|file/.test(n)) return '#5bb0e6';                      // blue: read
  if(/grep|glob|search|find|explore|list|ls/.test(n)) return '#b98cf0';        // purple: search
  if(/task|agent|workflow|dispatch|spawn/.test(n)) return '#e673a8';           // pink: delegate
  if(/web|fetch|http|url|browser|navigate/.test(n)) return '#4fd0c0';          // teal: web
  return '#d9c37a';                                                            // default: sand-gold
}
// ephemeral TOOL CHIP: a small dark pill with a tool-coloured icon + the tool name, popped
// when an agent/dwarf runs a tool. Deliberately distinct from the white speech bubble.
function drawToolChip(x, y, name, alpha, below){
  if(!name || alpha<=0) return;
  ctx.save();
  ctx.globalAlpha = Math.max(0, Math.min(1, alpha));
  ctx.font = '4px "Press Start 2P", monospace';
  const label = name.length>24 ? name.slice(0,24) : name;   // pre-formatted "NAME detail"; keep the detail
  const tw = ctx.measureText(label).width;
  const icon=5, padX=3, gap=3, h=9;
  const bw = padX + icon + gap + Math.ceil(tw) + padX;
  const bx = Math.round(x-bw/2), by = Math.round(below ? y+4 : y-h);
  const col = toolColor(name.split(' ')[0]);                 // colour by the tool name, not the detail
  ro(bx, by, bw, h, '#22262e');                      // dark slate pill + outline
  px(bx+1, by+1, bw-2, 1, '#333a46');                // top sheen
  const tx=Math.round(x);
  if(below){ px(tx-1, by-1, 2,1, '#22262e'); px(tx, by-2, 1,1, '#22262e'); }   // small nub up
  else     { px(tx-1, by+h, 2,1, '#22262e'); px(tx, by+h+1, 1,1, '#22262e'); } // small nub down
  const ix=bx+padX, iy=by+Math.round((h-icon)/2);    // little gear/cog icon in the tool colour
  px(ix+1,iy,3,1,col); px(ix,iy+1,5,3,col); px(ix+1,iy+4,3,1,col); px(ix+2,iy+2,1,1,'#22262e');
  ctx.fillStyle=col; ctx.textAlign='left';
  ctx.fillText(label, ix+icon+gap, by+h-3);
  ctx.textAlign='left'; ctx.restore();
}
// tool chip label: just the short tool NAME (e.g. "BASH", "EDIT") for the compact ephemeral
// chip. The detailed "Bash: npm run dev" lives in the hover card (last_tool), not here.
function toolChip(s){ s=String(s||''); const i=s.indexOf(':'); return (i>0?s.slice(0,i):s).trim().toUpperCase(); }
// a stern "boss" / supervisor in a suit + red tie, one arm pointing at the desk. Same scale as
// a standing worker -- pops up beside a desk to deliver a fresh user instruction (see below).
function drawBoss(x, y, t, moving){
  x=Math.round(x); y=Math.round(y);
  const suit='#31363f', suitLt='#3d434e', shirt='#eef1f6', tie='#c0392b', skin='#e6b38a', shoe='#191c22', hair='#3a2c20';
  const walking=!!moving;
  const step=walking?(Math.floor(t*0.16)&1):-1;                     // -1 = both feet planted (standing)
  const pt=(!walking) && (Math.floor(t*0.05)&1);                     // point only when stopped at the desk
  ctx.fillStyle='rgba(0,0,0,.22)'; ctx.beginPath(); ctx.ellipse(x,y+16,11,3,0,0,Math.PI*2); ctx.fill();
  ro(x-6,y+4,5,10,suit); ro(x+1,y+4,5,10,suit);                      // slacks
  px(x-2,y+5,1,9,shade(suit,-.25));
  const fa=step<0?0:(step?2:-2), fb=step<0?0:(step?-2:2);           // walk: swing the feet fore/aft
  px(x-8+fa,y+13,7,3,shoe); px(x-8+fa,y+13,7,1,shade(shoe,.4));      // left shoe
  px(x+fb,  y+13,7,3,shoe); px(x+fb,  y+13,7,1,shade(shoe,.4));      // right shoe
  ro(x-9,y-12,18,17,suit); px(x-9,y-12,18,2,suitLt); px(x-9,y+3,18,1,shade(suit,-.2)); // jacket
  px(x-2,y-11,4,11,shirt);                                          // shirt panel
  px(x-4,y-11,3,7,suitLt); px(x+1,y-11,3,7,suitLt);                 // lapels
  px(x-1,y-10,2,9,tie); px(x-1,y-1,2,2,shade(tie,-.25)); px(x-1,y-11,2,1,shade(tie,.3)); // tie
  ro(x+7,y-10,4,10,suit); px(x+7,y+0,4,3,skin);                     // right arm at side
  if(pt){ px(x-15,y-9,7,3,suit); px(x-16,y-9,3,3,skin); }           // left arm out, pointing at the desk
  else  { ro(x-11,y-10,4,10,suit); px(x-11,y+0,4,3,skin); }         // left arm down
  px(x-3,y-15,6,4,skin);                                            // neck
  ro(x-7,y-28,14,15,skin); px(x-7,y-14,14,1,'rgba(0,0,0,.10)');     // head
  px(x-7,y-28,14,4,hair); px(x-7,y-28,5,7,hair); px(x+5,y-28,2,5,hair); // side-part hair
  px(x-4,y-22,2,1,PAL.outline); px(x+3,y-22,2,1,PAL.outline);       // brows
  px(x-4,y-20,2,2,'#33373e'); px(x+3,y-20,2,2,'#33373e');           // eyes
  px(x-1,y-18,2,1,shade(skin,-.28));                               // nose
  px(x-3,y-16,7,1,shade(skin,-.35));                              // firm mouth
}

// a standing person (kitchen / lounge), facing us
function drawStanding(p, t){
  // celebration dance: little hops + side-to-side wiggle while the flag is live
  let dx0=0, dy0=0;
  if(p.celebrateUntil && performance.now()<p.celebrateUntil){
    const tt=performance.now();
    dy0 = -Math.abs(Math.sin(tt*0.018))*5;     // quick hops
    dx0 = Math.sin(tt*0.013)*3;                // wiggle
  } else if(p.whipUntil && performance.now()<p.whipUntil){
    dx0 = Math.sin(performance.now()*0.06)*2;  // whip: startled shudder (no hop)
  }
  const x=Math.round(p.x+dx0), y=Math.round(p.y+dy0);
  const f=p.feat||featuresFor(p.id||'x');
  const sk=f.skin, sh=f.shirt, pants=f.pants, shoe='#4a3526';
  const walking=(Math.abs(p.vx)+Math.abs(p.vy))>0.05;
  const step=walking?(Math.floor(t*0.16)&1):0;
  // deterministic kitchen "persona": a held item, stable per agent id (salted so it
  // doesn't merely echo the appearance bits featuresFor() already used).
  const kh = hash((p.id||'x')+'|kit');
  const item = (f.messenger || p.kind==='work') ? -1 : (kh % 6);
  //  -1 courier/worker(none)  0 mug  1 pastry  2 phone  3 plate  4 bottle  5 hands-free
  const settled = p.kind!=='work' && !walking && p.mode==='idle';
  const now = performance.now();
  const canSip = settled && item===0;                       // only the mug persona sips
  const sip = canSip && ((now + ((x*197)&2047)*3) % 5200) < 700;
  // occasional small-talk: face the paired neighbour on a staggered ~4.2s-in-12s window
  const talking = settled && p.talkX!=null && ((now + (kh%24000)) % 26000) < 2600;  // chat rarely: ~2.6s in every 26s
  const faceDir = talking ? (Math.sign(p.talkX - x)||0) : 0; // -1 look left, +1 look right
  const ht = sip ? -1 : (item===2 ? 1 : 0);                  // sip: tip back; phone: glance down
  const hx = faceDir*2;                                      // subtle head turn toward neighbour
  // shadow
  ctx.fillStyle='rgba(0,0,0,.20)'; ctx.beginPath(); ctx.ellipse(x,y+16,11,3,0,0,Math.PI*2); ctx.fill();
  // legs + rounded shoes (feet stay at ~y+16 to match the hitbox)
  const l1=9+(walking?step:0), l2=9+(walking?(1-step):0);
  ro(x-6, y+4, 5, l1, pants); ro(x+1, y+4, 5, l2, pants);
  px(x-6,y+4,5,1, shade(pants,.18)); px(x+1,y+4,5,1, shade(pants,.18));     // pant sheen
  px(x-2,y+5,1,l1-1, shade(pants,-.20)); px(x+5,y+5,1,l2-1, shade(pants,-.20)); // inner + outer leg shadow
  px(x-8, y+4+l1, 7,3, shoe); px(x-8, y+4+l1, 7,1, shade(shoe,.32));        // left shoe
  px(x,   y+4+l2, 7,3, shoe); px(x,   y+4+l2, 7,1, shade(shoe,.32));        // right shoe
  // torso (soft shaded shirt: top highlight, side + hem shadow, collar, belt)
  ro(x-9, y-11, 18, 16, sh);
  px(x-9,y-11,18,2, shade(sh,.30)); px(x+6,y-10,3,13, shade(sh,-.20)); px(x-9,y+3,18,2, shade(sh,-.16));
  px(x-2,y-11,4,2, shade(sh,-.28));                         // collar notch
  px(x-9,y+4,18,1, shade(pants,-.10));                      // belt/hem line
  torsoDetail(x, y-11, 9, 16, sh, f);                       // outfit variety + sheen
  if(f.messenger){ drawEnvelope(x, y-3); }                  // courier envelope badge
  // ---- arms + the held item (deterministic persona) --------------------------
  const gL = talking && (item===2||item===3 ? false : (faceDir<=0));  // lift left free hand
  const gR = talking && (item===5||item===-1) && faceDir>0;           // hands-free can lift right
  if(item===0){                                            // coffee mug (+ steam / sip)
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    const ay = sip?-4:0, my = sip?-6:0;
    ro(x+9, y-9+ay, 5, 7, sh); px(x+9, y-3+ay, 5,3, sk);
    ro(x+10, y-13+my, 7, 7, PAL.paper); px(x+11,y-12+my,5,5,PAL.mugA); px(x+17,y-12+my,2,4,PAL.paper);
    if(!sip){ for(let i=0;i<3;i++){ const yy=y-15-((t*1.1+i*5)%8); px(x+13,yy,1,2,'rgba(255,255,255,.5)'); } }
  } else if(item===1){                                     // pastry / muffin in the right hand
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    ro(x+9, y-6, 5, 6, sh); px(x+9, y-1, 5,3, sk);
    px(x+9,y-4,6,4,PAL.orange); px(x+9,y-4,6,1,shade(PAL.orange,.34)); px(x+11,y-2,2,1,shade(PAL.orange,-.3));
    px(x+9,y-1,6,1,'#c98a52');                             // pastry base
  } else if(item===2){                                     // phone in both hands, glancing down
    ro(x-13, y-6, 5, 7, sh); px(x-11, y-1, 4,3, sk);
    ro(x+9,  y-6, 5, 7, sh); px(x+7,  y-1, 4,3, sk);
    px(x-3,y-3,7,5,'#20242c'); px(x-2,y-2,5,3,'#7fd3e0'); px(x-2,y-2,5,1,'#b8ecf3'); // phone + lit screen
  } else if(item===3){                                     // plate of food in both hands
    ro(x-13, y-5, 5, 6, sh); px(x-11, y-1, 4,3, sk);
    ro(x+9,  y-5, 5, 6, sh); px(x+7,  y-1, 4,3, sk);
    px(x-6,y-2,13,3,'#eef0f4'); px(x-6,y-2,13,1,'#ffffff'); px(x-6,y+1,13,1,'#c9ccd4'); // plate
    px(x-3,y-3,3,2,PAL.orange); px(x+1,y-3,3,2,'#6aa72f'); // two bites of food
  } else if(item===4){                                     // water bottle / soda in the right hand
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    ro(x+9, y-7, 5, 7, sh); px(x+9, y-1, 5,3, sk);
    px(x+9,y-11,5,9,PAL.mugB); px(x+9,y-11,5,1,shade(PAL.mugB,.4)); px(x+13,y-11,1,9,shade(PAL.mugB,-.3));
    px(x+10,y-13,3,2,'#dfeefa');                           // cap
  } else {                                                 // item 5 / courier / worker: free hands
    ro(x-14, y-7-(gL?4:0), 5, 8, sh); px(x-14, y+1-(gL?4:0), 4,4, sk);
    ro(x+10, y-7-(gR?4:0), 5, 8, sh); px(x+10, y+1-(gR?4:0), 4,4, sk);
  }
  // neck + head (tips back while sipping / down on the phone; turns toward a chat neighbour)
  px(x-3+hx, y-14+ht, 6, 4, sk); px(x-3+hx, y-14+ht, 6, 1, 'rgba(0,0,0,.16)');
  ro(x-7+hx, y-27+ht, 14, 15, sk);
  px(x-7+hx,y-13+ht,14,1,'rgba(0,0,0,.10)');               // soft jaw shade
  drawHairAcc(x+hx, y-25+ht, f); drawFace(x+hx, y-25+ht, f);
  // small-talk bubble while chatting, else the cozy heart when settled
  if(settled){
    if(talking){ const nd=1+((((now/700)|0)+(kh%3))%3); talkBubble(x + (faceDir<0?-15:15), y-34, nd); }
    else heartBubble(x+15, y-34);
  }
}

// ---- update loop ----
let last=performance.now(), tCount=0;
const WALK_PXPS = 80;   // constant walk speed -> a room crossing takes ~2-4s
function tick(now){
  const dt=Math.min(40, now-last); last=now; tCount+= dt*0.06;
  const L=layout();
  const step = WALK_PXPS * dt/1000;   // distance to advance this frame
  // advance + expire confetti particles
  if(confetti.length){
    const ds=dt/1000;
    for(let i=confetti.length-1;i>=0;i--){ const c=confetti[i]; c.age+=ds;
      if(c.age>=c.life){ confetti.splice(i,1); continue; }
      c.vy+=c.g*ds; c.x+=c.vx*ds; c.y+=c.vy*ds; c.vx*=0.99; c.rot+=c.vr*ds;
    }
  }
  // advance + expire whip-crack particles (streaks decelerate; the lash line just fades)
  if(whipFx.length){
    const ds=dt/1000;
    for(let i=whipFx.length-1;i>=0;i--){ const c=whipFx[i]; c.age+=ds;
      if(c.age>=c.life){ whipFx.splice(i,1); continue; }
      if(!c.lash){ c.x+=c.vx*ds; c.y+=c.vy*ds; c.vx*=0.90; c.vy*=0.90; }
    }
  }
  // restock vending slots whose can has finished dropping + resting
  for(const k in vendDrops){ if(now-vendDrops[k].start>3200) delete vendDrops[k]; }
  for(const p of people){
    if(p.kind==='exit'){
      // a filtered-out scheduled agent walking off the bottom of the screen
      const dx=p.exitX-p.x, dy=p.exitY-p.y, dist=Math.hypot(dx,dy);
      if(dist>0.5){ p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      else { p.vx=p.vy=0; }
      continue;
    }
    if(p.kind==='work'){
      if(p.seated){ p.x=p.deskX; p.y=p.deskY; p.vx=p.vy=0; }
      else {
        // walk in from wherever it was (e.g. the kitchen) up to the desk, then sit
        const dx=p.deskX-p.x, dy=p.deskY-p.y, dist=Math.hypot(dx,dy);
        if(dist<=step+0.5){ p.x=p.deskX; p.y=p.deskY; p.seated=true; p.vx=p.vy=0; }
        else { p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      }
    } else {
      // walk once to the assigned spot, then stand still so it's easy to hover
      if(p.mode!=='idle'){
        const dx=p.home.x-p.x, dy=p.home.y-p.y, dist=Math.hypot(dx,dy);
        if(dist<=step+0.5){ p.x=p.home.x; p.y=p.home.y; p.mode='idle'; p.vx=p.vy=0; }
        else { p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      } else { p.vx=p.vy=0; }
      // clamp once settled (lets cross-room walks pass through first). Beach agents
      // stay on the sand (right of BEACH_X, clear of the water); kitchen agents stay
      // to the left of the divider.
      if(p.mode==='idle'){
        if(p.kind==='beach'){
          p.x=Math.max(BEACH_X+16, Math.min(W-30, p.x));   // W-30 keeps them out of the water
        } else {
          p.x=Math.max(L.kitchen.x+18, Math.min(BEACH_X-18, p.x));
        }
        p.y=Math.max(L.kitchenTop+44,Math.min(H-20,p.y));
      }
    }
  }
  updateAmbient(now, dt);
  render(tCount);
  requestAnimationFrame(tick);
}

// is a supervisor currently delivering an instruction to this agent? while so, the boss is
// the one "talking" -- the agent's own speech bubble is suppressed so they don't both pop one.
function bossActive(id){ const b=bossVisits[id]; return !!(b && b.until>performance.now()); }

function render(t){
  helperHits = [];                   // rebuilt each frame as dwarves are drawn
  workflowHits = [];                 // rebuilt each frame as workflow tents are drawn
  shellHits = [];                    // rebuilt each frame as open-shell terminals are drawn
  bubbleAnchors = [];                // rebuilt each frame; drawn as an overlay below
  vendSlots = [];                    // rebuilt each frame as the vending slots are drawn
  ctx.setTransform(SS,0,0,SS,0,0);   // map logical 640x576 onto the super-sampled backing
  ctx.clearRect(0,0,W,H);
  drawFloor();
  // office desks (always shown); seated worker drawn only once docked, otherwise
  // the desk is shown empty and the worker is drawn separately as a walker.
  const bt = performance.now();
  const slots=[...deskSlots].sort((a,b)=>a.y-b.y);
  for(const s of slots){ const w=s.worker;
    ctx.save(); scaleAbout(s.x, s.y, SC); drawDeskPod(s.x, s.y, (w&&w.seated)?w:null, t); ctx.restore();
    if(w && w.seated && w.bubbleUntil>bt && !bossActive(w.id)) bubbleAnchors.push({x:s.x, y:s.y-30*SC, text:w.bubbleText, start:w.bubbleStart, until:w.bubbleUntil, tool:w.bubbleTool}); }
  // everyone currently standing/walking (kitchen agents + workers still walking in),
  // interleaved with the ambient dog/cat so overlaps sort correctly by y (painter's).
  const drawList=[];
  people.filter(p=> p.kind!=='work' || !p.seated).forEach(p=> drawList.push({y:p.y, p}));
  if(amb.dog) drawList.push({y:amb.dog.y, dog:amb.dog});
  if(amb.cat) drawList.push({y:amb.cat.y, cat:amb.cat});
  drawList.sort((a,b)=>a.y-b.y);
  for(const e of drawList){
    if(e.p){ ctx.save(); scaleAbout(e.p.x, e.p.y, SC);
      // beach agents sit (with shades + cocktail) once settled; still walk in standing
      if(e.p.kind==='beach' && e.p.mode==='idle') drawBeachSitter(e.p,t); else drawStanding(e.p,t);
      ctx.restore();
      // a WAITING (kitchen) agent's open background shells float above its head, so a running
      // shell (e.g. a dev server) stays visible after the chat leaves the desk for the kitchen.
      if(e.p.kind==='wait' && e.p.agent && e.p.agent.shells && e.p.agent.shells.length){
        const sh=e.p.agent.shells, m=Math.min(sh.length,3);
        const base = Math.round(e.p.x - ((m-1)*22+17)/2);   // centre the row over the head
        ctx.save(); scaleAbout(e.p.x, e.p.y, SC);
        for(let i=0;i<m;i++){ const slot=m-1-i, sx=base+slot*22, sy=e.p.y-42;
          drawShellWin(sx, sy, t, (hash(e.p.id)+i*5)%997);
          shellHits.push({ x: e.p.x+((sx+8)-e.p.x)*SC, y: e.p.y+((sy+6)-e.p.y)*SC, r: 11*SC, shell: sh[i] }); }
        ctx.restore();
      }
      if(e.p.bubbleUntil>bt && !bossActive(e.p.id)) bubbleAnchors.push({x:e.p.x, y:e.p.y-34*SC, text:e.p.bubbleText, start:e.p.bubbleStart, until:e.p.bubbleUntil, tool:e.p.bubbleTool}); }
    else if(e.dog) drawDog(e.dog, t);
    else if(e.cat) drawCat(e.cat, t);
  }
  // supervisor "boss" visits: a stern suited figure delivering a fresh user instruction.
  // The boss ESCORTS the agent -- it appears the moment the instruction lands and walks
  // ALONGSIDE the agent from the kitchen to the desk (trailing the direction of travel),
  // then parks beside the desk once the agent is docked. Drawn after the people pass so it
  // reads as in front of the agent it's walking with.
  for(const id in bossVisits){
    const bv=bossVisits[id]; if(bv.until<=bt) continue;
    const p=people.find(q=>q.id===id); if(!p) continue;
    let bx, by, moving=false;
    if(p.kind==='work' && p.seated){
      bx=p.deskX+46; by=p.deskY-10;                 // parked beside the docked desk (bigger + raised)
    } else {
      const dir=(p.vx<-0.01)?-1:1;                   // stay on the trailing side of the walk
      bx=p.x-dir*22; by=p.y-2;
      moving=(Math.abs(p.vx)+Math.abs(p.vy))>0.02;   // swing the legs only while actually moving
    }
    const bs=SC*1.25;
    const a=Math.min(1,(bt-bv.start)/180, (bv.until-bt)/500);
    ctx.save(); ctx.globalAlpha=Math.max(0,a); scaleAbout(bx, by, bs); drawBoss(bx, by, t, moving); ctx.restore();
    bubbleAnchors.push({x:bx, y:by-30*bs, text:bv.text, start:bv.start, until:bv.until});
  }
  // ---- transient speech bubbles (desk/kitchen agents + subagent/workflow dwarves) ----
  for(const b of bubbleAnchors){
    const rem=b.until-bt; if(rem<=0) continue;
    const fin=Math.min(1,(bt-b.start)/160), fout=Math.min(1, rem/BUBBLE_FADE);
    if(b.tool) drawToolChip(b.x, b.y, b.text, Math.min(fin,fout), b.below);
    else drawBubble(b.x, b.y, b.text, Math.min(fin,fout), b.below);
  }
  // hover ring (around the drawn sprite, scaled to match SC)
  if(hover){
    ctx.strokeStyle='#ffffff'; ctx.lineWidth=2;
    if(hover.kind==='work' && hover.seated) ctx.strokeRect(hover.deskX-24*SC, hover.deskY-33*SC, 48*SC, 56*SC);
    else ctx.strokeRect(Math.round(hover.x)-14*SC, Math.round(hover.y)-31*SC, 28*SC, 51*SC);
  }
  // subtle dot-matrix vignette (kept faint + crisp so text/sprites stay readable)
  if(!render._vig){
    const g=ctx.createRadialGradient(W/2,H*0.46,H*0.34,W/2,H*0.5,H*0.78);
    g.addColorStop(0,'rgba(20,16,28,0)'); g.addColorStop(1,'rgba(20,16,28,0.15)');
    render._vig=g;
  }
  ctx.fillStyle=render._vig; ctx.fillRect(0,0,W,H);
  // celebration confetti, rendered above everything
  for(const c of confetti){
    const a=Math.max(0, 1 - c.age/c.life);
    ctx.save(); ctx.globalAlpha=a; ctx.translate(c.x,c.y); ctx.rotate(c.rot);
    ctx.fillStyle=c.col; ctx.fillRect(-c.w/2,-c.h/2,c.w,c.h); ctx.restore();
  }
  // whip crack: a bright lash line + sharp shock streaks, above everything
  for(const c of whipFx){
    const a=Math.max(0, 1 - c.age/c.life);
    if(c.lash){
      // curved, tapering whip lash (quadratic bezier hx,hy -> control mx,my -> tip tx,ty)
      ctx.save(); ctx.globalAlpha=a; ctx.lineCap='round'; ctx.lineJoin='round';
      const P=10; let lx=c.hx, ly=c.hy;
      for(let i=1;i<=P;i++){
        const u=i/P, iu=1-u;
        const bx=iu*iu*c.hx + 2*iu*u*c.mx + u*u*c.tx;
        const by=iu*iu*c.hy + 2*iu*u*c.my + u*u*c.ty;
        ctx.strokeStyle = u>0.82 ? '#ffffff' : '#f3e6c2';   // bright white at the cracking tip
        ctx.lineWidth = 3.4*(1-u) + 0.5;                    // thick at the handle -> thin at the tip
        ctx.beginPath(); ctx.moveTo(lx,ly); ctx.lineTo(bx,by); ctx.stroke();
        lx=bx; ly=by;
      }
      ctx.fillStyle='#ffffff'; ctx.beginPath(); ctx.arc(c.tx,c.ty,1.6,0,Math.PI*2); ctx.fill(); // tip spark
      ctx.restore();
    } else {
      ctx.save(); ctx.globalAlpha=a; ctx.translate(c.x,c.y); ctx.rotate(c.rot);
      ctx.fillStyle=c.col; ctx.fillRect(-c.w/2,-c.h/2,c.w,c.h); ctx.restore();
    }
  }
  ctx.globalAlpha=1;
}

// burst ~110 confetti pieces: half from the agent's head, half across the whole screen
function spawnConfetti(ox, oy){
  const cols=['#e23b3b','#f0a23b','#ffd84d','#4fd06a','#3fa0e0','#8c5fd6','#e673a8','#ffffff'];
  const N=110;
  for(let i=0;i<N;i++){
    const fromOrigin = (ox!=null) && (i<55);
    confetti.push({
      x: fromOrigin? ox : Math.random()*W,
      y: fromOrigin? oy : -10 - Math.random()*H*0.3,
      vx: fromOrigin? (Math.random()-0.5)*170 : (Math.random()-0.5)*45,
      vy: fromOrigin? (-130 - Math.random()*120) : (20 + Math.random()*60),
      g: 190 + Math.random()*120,
      w: 3+Math.random()*4, h: 4+Math.random()*5,
      col: cols[(Math.random()*cols.length)|0],
      rot: Math.random()*Math.PI, vr:(Math.random()-0.5)*10,
      life: 2.6 + Math.random()*1.0, age:0,
    });
  }
  if(confetti.length>200) confetti.splice(0, confetti.length-200);   // hard cap
}

// a whip CRACK snapping down at the strike point (ox,oy): a curved tapering lash + a short
// sharp tip-crack (a few streaks flicking down, NOT a radial burst -- reads as a whip, not a meteor)
function spawnWhip(ox, oy){
  const tx=(ox!=null)?ox:W/2, ty=(oy!=null)?oy:H*0.22;
  const dir=Math.random()<0.5?1:-1;                        // swing in from the left or the right
  // curved lash: handle up-&-to-the-side, arcs over, snaps down to the tip (tx,ty)
  whipFx.push({ lash:true, hx:tx-82*dir, hy:ty-72, mx:tx-24*dir, my:ty-50, tx:tx, ty:ty, life:0.20, age:0 });
  const N=8;
  for(let i=0;i<N;i++){
    const a=Math.PI/2 + (dir>0?-0.55:0.55) + (Math.random()-0.5)*1.7;   // downward fan, leaning w/ the swing
    const sp=150+Math.random()*160;
    whipFx.push({
      x:tx, y:ty, vx:Math.cos(a)*sp, vy:Math.sin(a)*sp,
      w:4+Math.random()*4, h:1+Math.random()*1.1,
      col: Math.random()<0.5?'#ffffff':'#ffe9a8',
      rot:a, life:0.14+Math.random()*0.10, age:0,
    });
  }
  if(whipFx.length>160) whipFx.splice(0, whipFx.length-160);   // hard cap
}

// ======================================================================
// AMBIENT RANDOM EVENTS  (dog crossing / cat nap / agent relocate)
// Scheduled + animated entirely off the rAF clock (see tick()).
// ======================================================================

// next-event delay. Override for testing with:  window.__eventInterval=[2000,4000]
// (and restore with:  delete window.__eventInterval)
function scheduleNextEvent(now){
  let mn=30000, mx=60000;
  if(window.__eventInterval){ mn=window.__eventInterval[0]; mx=window.__eventInterval[1]; }
  nextEventAt = now + mn + Math.random()*(mx-mn);
}

// independent, long-gap scheduler for the occasional window fly-by (test hook:
// window.__planeInterval=[3000,6000]; restore with delete window.__planeInterval)
function schedulePlane(now){
  let mn=60000, mx=150000;
  if(window.__planeInterval){ mn=window.__planeInterval[0]; mx=window.__planeInterval[1]; }
  nextPlaneAt = now + mn + Math.random()*(mx-mn);
}

// pick ONE event at random, avoiding an immediate repeat; if the chosen type can't
// run (dog/cat already on screen, or no waiting agent for a relocate) try another.
function fireRandomEvent(now){
  const types=[1,2,3];
  for(let i=types.length-1;i>0;i--){ const j=(Math.random()*(i+1))|0; const tmp=types[i]; types[i]=types[j]; types[j]=tmp; }
  if(types[0]===lastEventType){ types.push(types.shift()); }   // soft anti-repeat
  for(const t of types){
    if(t===1 && !amb.dog){ startDog(now); lastEventType=1; return; }
    if(t===2 && !amb.cat){ startCat(now); lastEventType=2; return; }
    if(t===3 && startRelocate(now)){ lastEventType=3; return; }
  }
}

// ---- 1) DOG walks across the OFFICE floor and exits ----
const DOG_BREEDS=['dachshund','husky','retriever'];
function startDog(now){
  const L=layout();
  const dir = Math.random()<0.5 ? 1 : -1;            // 1: L->R, -1: R->L
  const breed = DOG_BREEDS[(Math.random()*DOG_BREEDS.length)|0];
  amb.dog = {
    breed, dir,
    x: dir>0 ? -36 : W+36,
    y: L.kitchenTop - 24,                            // near-front office lane (in front of desks)
    spd: 118 + Math.random()*26,                     // px/s -> ~4-5s to cross
  };
}

// ---- 2) CAT walks into the KITCHEN, curls up and naps, then leaves ----
const CAT_FURS=['#e09a4a','#9aa0a6','#caa97a','#cfcfcf'];  // ginger / grey / fawn / silver
const CAT_SPOTS=[[490,556],[300,478],[200,556],[410,556]]; // open floor, clear of furniture
function startCat(now){
  // choose the floor spot furthest from every agent (so the cat doesn't overlap)
  let best=CAT_SPOTS[0], bestD=-1;
  for(const s of CAT_SPOTS){
    let mind=1e9;
    for(const p of people){ if(p.kind==='work') continue; const d=Math.hypot(p.x-s[0],p.y-s[1]); if(d<mind) mind=d; }
    if(mind>bestD){ bestD=mind; best=s; }
  }
  const dir = best[0] < W/2 ? 1 : -1;                // enter from the nearer side
  let nap = 120000 + Math.random()*120000;          // 2-4 min
  if(window.__catNapMs) nap = window.__catNapMs;     // testing override
  amb.cat = {
    fur: CAT_FURS[(Math.random()*CAT_FURS.length)|0],
    dir, x: dir>0 ? -20 : W+20, y: best[1],
    tx: best[0], state:'in', spd:74, napMs:nap, sleepUntil:0,
  };
}

// ---- a tiny airliner drifts across the WINDOW sky, above the buildings, near the clouds ----
function startPlane(now){
  const dir = Math.random()<0.5 ? 1 : -1;               // 1: L->R, -1: R->L
  amb.plane = {
    dir,
    x: dir>0 ? WIN.x-16 : WIN.x+WIN.w+16,               // start just off the clipped glass edge
    y: WIN.y + 6 + Math.random()*14,                    // upper sky band, near the clouds
    spd: 22 + Math.random()*16,                         // px/s -> ~9-13s to drift across
  };
}

// ---- 3) RELOCATE: a waiting agent strolls to a different open kitchen spot ----
function startRelocate(now){
  const cands = people.filter(p=> p.kind==='wait' && p.mode==='idle');
  if(!cands.length) return false;
  const p = cands[(Math.random()*cands.length)|0];
  // collect spots that are free (no other agent within ~40px) and not where we already are
  const others = people.filter(q=> q!==p);
  const open = [];
  for(const s of KSPOTS){
    if(Math.hypot(s[0]-p.x, s[1]-p.y) < 30) continue;          // too close to current spot
    let free=true;
    for(const q of others){ if(Math.hypot(q.x-s[0],q.y-s[1])<40){ free=false; break; } }
    if(free) open.push(s);
  }
  if(!open.length) return false;
  const s = open[(Math.random()*open.length)|0];
  p.relocHome = { x:s[0], y:s[1] };       // sticky across refreshes (see rebuild)
  p.home = p.relocHome;
  p.mode = 'walk';                         // reuse existing walk->idle mechanics
  return true;
}

// advance ambient critters; called from tick()
function updateAmbient(now, dt){
  if(!nextEventAt) scheduleNextEvent(now);          // first event ~30-60s after load
  if(now>=nextEventAt){ fireRandomEvent(now); scheduleNextEvent(now); }
  const sec=dt/1000;
  if(amb.dog){ const d=amb.dog;
    if(!(d.react && now<d.react.until)) d.x += d.dir*d.spd*sec;   // pause walking mid-pet
    if((d.dir>0 && d.x>W+44) || (d.dir<0 && d.x<-44)) amb.dog=null; }
  if(amb.cat){ const c=amb.cat;
    if(c.state==='in'){
      if(Math.abs(c.tx-c.x) <= c.spd*sec+0.5){ c.x=c.tx; c.state='sleep'; c.sleepUntil=now+c.napMs; }
      else c.x += Math.sign(c.tx-c.x)*c.spd*sec;
    } else if(c.state==='sleep'){
      if(now>=c.sleepUntil){ c.state='out'; c.dir = (c.x < W/2) ? -1 : 1; }   // leave the nearer side
    } else { // out
      c.x += c.dir*c.spd*sec;
      if((c.dir>0 && c.x>W+24) || (c.dir<0 && c.x<-24)) amb.cat=null;
    }
  }
  // occasional airliner across the window sky (independent long-gap scheduler)
  if(!nextPlaneAt) schedulePlane(now);
  else if(now>=nextPlaneAt){ if(!amb.plane) startPlane(now); schedulePlane(now); }
  if(amb.plane){ const pl=amb.plane; pl.x += pl.dir*pl.spd*sec;
    if((pl.dir>0 && pl.x>WIN.x+WIN.w+24) || (pl.dir<0 && pl.x<WIN.x-24)) amb.plane=null; }
}

// ---------- pixel-art critters (drawn scaled by SC about their anchor) ----------

// a single shaded leg segment
function _leg(lx, topY, len, w, col){ px(lx,topY,w,len,col); px(lx,topY+len-1,w,1,shade(col,-.34)); }

// AIRLINER: a tiny plane drifting across the window sky. Drawn in absolute window
// coords at logical scale (no SC), mirrored to face its heading, with a faint contrail.
function drawPlane(pl){
  const x=Math.round(pl.x), y=Math.round(pl.y);
  ctx.save();
  if(pl.dir<0){ ctx.translate(x,0); ctx.scale(-1,1); ctx.translate(-x,0); }   // face left
  const body='#eef2f6', bodyDk='#b9c2cc', porthole='#8fb7d8', tailc='#d24b4b';
  // faint contrail streaming out behind the tail (the -x side while facing right)
  for(let i=1;i<=6;i++){ const a=(0.18*(7-i)/6).toFixed(3);
    px(x-9-i*3, y+2, 2, 1, 'rgba(255,255,255,'+a+')'); }
  px(x-8, y-2, 2, 4, tailc); px(x-7, y-2, 1, 3, shade(tailc,.15));            // tail fin (back, raised)
  px(x-7, y+1, 13, 4, body); px(x-7, y+1, 13, 1, '#ffffff'); px(x-7, y+4, 13, 1, bodyDk); // fuselage
  px(x+6, y+2, 2, 2, body);                                                   // pointed nose (front)
  px(x-2, y+4, 7, 2, bodyDk);                                                  // swept wing under body
  px(x, y+2, 1, 1, porthole); px(x+2, y+2, 1, 1, porthole);                    // two cabin windows
  ctx.restore();
}

// DOG: three visually distinct breeds, side-on, facing its walk direction.
function drawDog(d, t){
  ctx.save();
  scaleAbout(d.x, d.y, SC);
  if(d.dir<0){ ctx.translate(d.x,0); ctx.scale(-1,1); ctx.translate(-d.x,0); }  // face left
  // pet reactions: a hop, an extra-waggy tail, or a tongue-out lick
  const _now=performance.now();
  const react=(d.react && _now<d.react.until)?d.react:null;
  const rp = react ? (_now-react.start)/(react.until-react.start) : 0;
  const jump = (react&&react.type==='jump') ? -Math.abs(Math.sin(rp*Math.PI))*11 : 0;
  const wagAmp=(react&&react.type==='wag')?4:2, wagSpd=(react&&react.type==='wag')?1.4:0.55;
  const x=d.x, groundY=d.y, y=d.y+jump;
  const ph = (Math.floor(t*0.34)&1) ? 1 : -1;        // leg swing phase
  const bob = Math.round(Math.sin(t*0.30))|0;        // head bob (0/1)
  const wag = Math.round(Math.sin(t*wagSpd)*wagAmp); // tail wag (bigger/faster mid-pet)
  // ground contact shadow (stays on the floor even during a hop)
  ctx.fillStyle='rgba(0,0,0,.18)'; ctx.beginPath(); ctx.ellipse(x, groundY+1, 22, 4, 0, 0, Math.PI*2); ctx.fill();

  if(d.breed==='dachshund'){
    const c='#8a5a2b', cd='#6b431d', ch='#a3743f', ear='#5a3717', nose='#241c2b';
    const bw=42, bh=9, by=y-12;                       // long, low body
    // short legs (front pair near +x/head, back pair near -x/tail)
    _leg(x-15, by+bh, 6+ph, 4, cd); _leg(x-8, by+bh, 6-ph, 4, cd);
    _leg(x+8,  by+bh, 6-ph, 4, c);  _leg(x+15, by+bh, 6+ph, 4, c);
    ro(x-bw/2, by, bw, bh, c);                        // body
    px(x-bw/2, by, bw, 2, ch); px(x-bw/2, by+bh-2, bw, 2, cd);
    // tail (thin, low, wagging) at the back-left
    px(x-bw/2-4, by+1+wag, 6, 2, c); px(x-bw/2-6, by-1+wag, 3, 2, c);
    // neck + head at the front-right, slightly raised by bob
    const hx=x+bw/2-1, hy=by-6+bob;
    px(hx-2, by-2, 7, 6, c);                          // neck wedge
    ro(hx, hy, 13, 11, c); px(hx,hy,13,2,ch);         // head
    px(hx+11, hy+4, 6, 5, c); px(hx+11,hy+4,6,1,ch);  // snout
    px(hx+16, hy+5, 2, 3, nose);                      // nose
    px(hx-2, hy+1, 5, 12, ear);                       // long floppy ear hanging down
    px(hx-2, hy+1, 5, 2, shade(ear,.2));
    px(hx+6, hy+4, 2, 2, nose);                       // eye
  }
  else if(d.breed==='husky'){
    const c='#9aa3ab', cd='#6f7780', ch='#cfd5da', wht='#f3f5f7', ear='#5b636b', nose='#241c2b';
    const bw=30, bh=12, by=y-16;                      // medium body, taller legs
    _leg(x-11, by+bh, 9+ph, 4, wht); _leg(x-5, by+bh, 9-ph, 4, wht);
    _leg(x+5,  by+bh, 9-ph, 4, wht); _leg(x+11, by+bh, 9+ph, 4, wht);
    ro(x-bw/2, by, bw, bh, c);                        // grey back
    px(x-bw/2, by, bw, 2, ch);
    px(x-bw/2, by+bh-4, bw, 4, wht);                  // white belly band
    // curled tail (plumed, sweeping up over the back)
    px(x-bw/2-4, by-2+wag, 4, 8, c); px(x-bw/2-6, by-6+wag, 5, 5, ch);
    px(x-bw/2-3, by-8+wag, 6, 4, wht);
    // neck + head with mask markings
    const hx=x+bw/2-2, hy=by-9+bob;
    px(hx-2, by-3, 8, 8, c);                          // neck
    ro(hx, hy, 14, 13, c); px(hx,hy,14,2,ch);         // head (grey)
    px(hx+5, hy+4, 9, 9, wht);                        // white muzzle/mask
    px(hx+12, hy+6, 6, 5, wht);                       // snout
    px(hx+17, hy+7, 2, 3, nose);                      // nose
    px(hx+1, hy-5, 4, 6, c); px(hx+1,hy-5,4,1,ch);    // pointy ear (back)
    px(hx+8, hy-5, 4, 6, c); px(hx+8,hy-5,4,1,ch);    // pointy ear (front)
    px(hx+2, hy-3, 2, 3, shade(c,-.3)); px(hx+9, hy-3, 2, 3, shade(c,-.3)); // ear insides
    px(hx+9, hy+4, 2, 2, '#5aa0d8');                  // pale husky eye
  }
  else { // golden retriever
    const c='#e0a84a', cd='#bd8730', ch='#f0c878', nose='#2a2018';
    const bw=32, bh=13, by=y-16;
    _leg(x-12, by+bh, 9+ph, 5, cd); _leg(x-5, by+bh, 9-ph, 5, cd);
    _leg(x+5,  by+bh, 9-ph, 5, c);  _leg(x+12, by+bh, 9+ph, 5, c);
    ro(x-bw/2, by, bw, bh, c);                        // tan body
    px(x-bw/2, by, bw, 2, ch); px(x-bw/2, by+bh-2, bw, 2, cd);
    // plumed bushy tail held out/up, wagging
    px(x-bw/2-6, by-1+wag, 8, 4, c); px(x-bw/2-10, by-4+wag, 7, 5, ch);
    px(x-bw/2-12, by-7+wag, 6, 4, c); px(x-bw/2-8, by+2+wag, 6, 3, cd);
    // neck + head with long floppy ears
    const hx=x+bw/2-2, hy=by-8+bob;
    px(hx-2, by-3, 9, 8, c);                          // neck
    ro(hx, hy, 14, 12, c); px(hx,hy,14,2,ch);         // head
    px(hx+11, hy+4, 7, 6, c); px(hx+11,hy+4,7,1,ch);  // muzzle
    px(hx+17, hy+5, 2, 3, nose);                      // nose
    px(hx-3, hy+1, 5, 11, cd); px(hx-3,hy+1,5,2,c);   // floppy ear
    px(hx+8, hy+4, 2, 2, nose);                       // eye
  }
  // pet-reaction flourishes: happy hearts, plus a big pink tongue for a 'lick'
  if(react){
    miniHeart(x-5, y-24-rp*8); miniHeart(x+5, y-20-rp*10);
    if(react.type==='lick'){ px(x+20, y-6, 4, 7, '#e79ab0'); px(x+20, y-1, 4, 2, '#d47a92'); px(x+21, y-6, 1, 3, '#f4c0d0'); } // tongue
  }
  ctx.restore();
}

// CAT: rounded curled body when sleeping (tail wrapped, Zzz rising), or a small
// side-on walker when entering/leaving.
function drawCat(c, t){
  ctx.save();
  scaleAbout(c.x, c.y, SC);
  const fur=c.fur, furDk=shade(fur,-.30), furHi=shade(fur,.30), pink='#e79ab0', nose='#cf7a8e';
  const el=(cx,cy,rx,ry,col)=>{ ctx.fillStyle=col; ctx.beginPath(); ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2); ctx.fill(); };
  const x=c.x, y=c.y;
  const _now=performance.now();
  const react=(c.react && _now<c.react.until)?c.react:null;
  const rp = react ? (_now-react.start)/(react.until-react.start) : 0;
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(x, y+2, 16, 4, 0, 0, Math.PI*2); ctx.fill();

  if(c.state==='sleep'){
    el(x, y-6, 15, 9, fur);                           // curled body
    el(x, y-9, 11, 5, furHi);                         // back highlight
    el(x-9, y-3, 7, 6, fur);                          // tucked head (front-left)
    px(x-15, y-12, 4, 6, fur); px(x-15,y-12,4,2,furHi); // ear
    px(x-9, y-12, 4, 6, fur);  px(x-9,y-12,4,2,furHi);  // ear
    px(x-12, y-3, 4, 1, PAL.outline);                 // closed eye (sleepy arc)
    px(x-13, y-2, 1, 1, PAL.outline); px(x-8, y-2, 1, 1, PAL.outline);
    // tail wrapped around the front of the body
    ctx.strokeStyle=furDk; ctx.lineWidth=3; ctx.beginPath();
    ctx.arc(x+2, y-4, 12, -0.2, 1.5); ctx.stroke();
    px(x+13, y+2, 3, 3, furDk);                       // tail tip
    // rising sleep "z"s (animated)
    ctx.fillStyle=PAL.ink;
    const f=(t*0.6);
    ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('z', x+5-((f)%10), y-16-((f)%10));
    ctx.font='5px "Press Start 2P", monospace'; ctx.fillText('z', x+10-((f+5)%12), y-12-((f+5)%12));
    // pet reactions while curled up: purr (music notes) or an annoyed screen-swipe
    if(react && react.type==='purr'){
      ctx.fillStyle=PAL.leafDk; ctx.font='6px "Press Start 2P", monospace';
      ctx.fillText('♪', x+7-rp*4, y-15-rp*10); ctx.fillText('♫', x+12-rp*3, y-11-rp*13);
      miniHeart(x-3, y-17-rp*7);
    } else if(react && react.type==='violence'){
      const sw=Math.sin(rp*Math.PI);
      px(x-13,y-4,4,1,PAL.outline); px(x-8,y-4,4,1,PAL.outline);        // angry slit eyes (over the sleepy ones)
      px(x-2+sw*7, y-11, 5,3, fur); px(x-2+sw*7, y-11, 5,1, furHi);     // paw swiping at the screen
      const a=1-Math.abs(rp-0.5)*2;                                     // slashes flash in then out
      ctx.strokeStyle='rgba(255,255,255,'+(0.6*a).toFixed(2)+')'; ctx.lineWidth=1.6;
      for(let i=0;i<3;i++){ ctx.beginPath(); ctx.moveTo(x-7+i*6, y-19); ctx.lineTo(x-2+i*6, y-1); ctx.stroke(); }
    }
  } else {
    if(c.dir<0){ ctx.translate(x,0); ctx.scale(-1,1); ctx.translate(-x,0); }  // face walk dir
    const ph=(Math.floor(t*0.4)&1)?1:-1;
    _leg(x-7, y-7, 7+ph, 3, furDk); _leg(x-2, y-7, 7-ph, 3, furDk);
    _leg(x+4, y-7, 7-ph, 3, fur);  _leg(x+8, y-7, 7+ph, 3, fur);
    ro(x-9, y-13, 18, 7, fur); px(x-9,y-13,18,2,furHi);   // body
    // upright tail with a slight wag
    const wag=Math.round(Math.sin(t*0.5)*2);
    px(x-11, y-18+wag, 3, 8, fur); px(x-12, y-22+wag, 3, 5, furDk);
    // head (front-right) with ears + face
    const hx=x+7, hy=y-19;
    ro(hx, hy, 11, 10, fur); px(hx,hy,11,2,furHi);
    px(hx, hy-4, 4, 5, fur); px(hx+7, hy-4, 4, 5, fur);   // pointy ears
    px(hx+1, hy-3, 2, 3, pink); px(hx+8, hy-3, 2, 3, pink);
    px(hx+8, hy+4, 2, 2, PAL.outline);                   // eye
    px(hx+10, hy+6, 2, 2, nose);                         // nose
  }
  ctx.restore();
}

// ---- petting the ambient pets ----
function miniHeart(hx,hy){ px(hx-2,hy,2,2,PAL.pink); px(hx+1,hy,2,2,PAL.pink); px(hx-2,hy+1,5,2,PAL.pink); px(hx-1,hy+3,3,1,PAL.pink); px(hx,hy+4,1,1,PAL.pink); }
// which pet (if any) is under the cursor -- cat first, then dog
function pickPet(mx,my){
  if(amb.cat){ const c=amb.cat, cy=(c.state==='sleep')?c.y-6:c.y-13;
    if(Math.abs(mx-c.x)<18*SC && Math.abs(my-cy)<16*SC) return 'cat'; }
  if(amb.dog){ const d=amb.dog;
    if(Math.abs(mx-d.x)<24*SC && my>d.y-30*SC && my<d.y+8*SC) return 'dog'; }
  return null;
}
function petDog(){ const d=amb.dog; if(!d) return;
  const type=['wag','lick','jump'][(Math.random()*3)|0];
  const now=performance.now(); d.react={type, start:now, until:now+950};
}
function petCat(){ const c=amb.cat; if(!c) return; initAudio();
  const type=['purr','reposition','violence'][(Math.random()*3)|0];
  const now=performance.now();
  if(type==='reposition'){
    // stand up and scoot along the floor to a nearby spot, then re-settle
    c.tx=Math.max(40, Math.min(W-40, c.x + (Math.random()<0.5?-1:1)*(60+Math.random()*80)));
    c.state='in'; c.react=null;
  } else if(type==='purr'){
    c.react={type, start:now, until:now+1600}; c.sleepUntil=Math.max(c.sleepUntil, now+2500); playPurr();
  } else { // violence: an annoyed swipe at the screen
    c.react={type, start:now, until:now+800}; c.sleepUntil=Math.max(c.sleepUntil, now+3000); playScratch();
  }
}

// ---- interaction ----
function toCanvas(ev){
  const r=cv.getBoundingClientRect();
  return { x:(ev.clientX-r.left)/r.width*W, y:(ev.clientY-r.top)/r.height*H, cx:ev.clientX-r.left, cy:ev.clientY-r.top, r };
}
function pick(mx,my){
  let best=null,bd=1e9;
  for(const p of people){
    const seatedWorker = p.kind==='work' && p.seated;
    // hit-test against where the sprite is actually drawn
    const sx = seatedWorker ? p.deskX : p.x;
    const sy = seatedWorker ? p.deskY : p.y;
    const dx=mx-sx;
    let hit;
    // hitboxes scale with SC (sprites are drawn scaled about their anchor)
    if(seatedWorker) hit = (Math.abs(dx)<24*SC && my>sy-32*SC && my<sy+22*SC);
    else             hit = (Math.abs(dx)<15*SC && my>sy-32*SC && my<sy+18*SC); // standing
    if(hit){ const cy=sy-12*SC, d=dx*dx+(my-cy)*(my-cy); if(d<bd){bd=d;best=p;} }
  }
  return best;
}
const nametag=document.getElementById('nametag');
// place the hover card near the cursor, flipped/clamped to stay on-screen
function placeNametag(m){
  // anchor BELOW the cursor and grow downward; only pull up as much as needed and never
  // above `pad`, so a tall card's TOP (its title) always stays on-screen (item 2).
  const sw=m.r.width, sh=m.r.height, pad=8;
  const bw=nametag.offsetWidth, bh=nametag.offsetHeight;
  let left=m.cx+16;
  if(left+bw+pad>sw) left=m.cx-bw-16;
  if(left<pad) left=pad;
  let top=m.cy+18;
  if(top+bh+pad>sh) top=Math.max(pad, sh-bh-pad);
  nametag.style.left=Math.round(left)+'px'; nametag.style.top=Math.round(top)+'px';
}
function pickHelper(mx,my){ let best=null,bd=1e9;
  for(const h of helperHits){ const d=(mx-h.x)*(mx-h.x)+(my-h.y)*(my-h.y); if(d<h.r*h.r && d<bd){bd=d;best=h;} }
  return best; }
function pickWorkflow(mx,my){ let best=null,bd=1e9;
  for(const w of workflowHits){ const d=(mx-w.x)*(mx-w.x)+(my-w.y)*(my-w.y); if(d<w.r*w.r && d<bd){bd=d;best=w;} }
  return best; }
function pickShell(mx,my){ let best=null,bd=1e9;
  for(const s of shellHits){ const d=(mx-s.x)*(mx-s.x)+(my-s.y)*(my-s.y); if(d<s.r*s.r && d<bd){bd=d;best=s;} }
  return best; }
function pickVend(mx,my){
  for(const s of vendSlots){ if(mx>=s.x0 && mx<=s.x1 && my>=s.y0 && my<=s.y1) return s; }
  return null; }
function dispenseDrink(s){
  if(vendDrops[s.idx]) return;                       // already dispensing this slot
  vendDrops[s.idx]={start:performance.now(), col:s.col, fromX:s.bxv, fromY:s.ry}; }
cv.addEventListener('mousemove', e=>{
  const m=toCanvas(e);
  // a pettable pet under the cursor?
  const pet=pickPet(m.x,m.y);
  if(pet){ hover=null; cv.style.cursor='pointer';
    nametag.innerHTML='<div class="nt-hint">click to pet the '+pet+'</div>';
    nametag.style.display='block'; placeNametag(m); return; }
  // a vending-machine drink? (click drops it into the tray)
  const vs=pickVend(m.x,m.y);
  if(vs){ hover=null; cv.style.cursor='pointer';
    nametag.innerHTML='<div class="nt-hint">click for a cold one</div>';
    nametag.style.display='block'; placeNametag(m); return; }
  // a workflow tent? (takes precedence over helpers)
  const wf=pickWorkflow(m.x,m.y);
  if(wf){
    hover=null; cv.style.cursor='help';
    const runs = wf.workflow;
    const done = runs.reduce((s,w)=>s+(w.done||0),0);
    const total = runs.reduce((s,w)=>s+(w.total||0),0);
    const running = runs.reduce((s,w)=>s+(w.running||0),0);
    const title = runs.length>1 ? (runs.length+' workflows') : humanizeWf(runs[0].name);
    let html =
      '<div class="nt-name">'+esc(title)+'<span class="nt-badge workflow">workflow</span></div>'+
      '<div class="nt-meta">'+done+' done  ·  '+running+' running  ·  '+total+' launched</div>';
    if(runs.length===1){
      const w=runs[0];
      if(w.summary) html += '<div class="nt-label">Summary</div><div class="nt-text">'+esc(w.summary)+'</div>';
      if(w.phases && w.phases.length)
        html += '<div class="nt-label">Phases</div><div class="nt-text wf-phases">'+
          w.phases.map(p=>'<span class="wf-phase '+(p.state||'pending')+'">'+esc(p.title)+
            (p.count!=null?(' '+p.done+'/'+p.count):'')+'</span>').join('<span class="wf-sep">›</span>')+
          '</div>';
      if(w.active && w.active.length)
        html += '<div class="nt-label">Running now</div><div class="nt-text">'+w.active.map(a=>esc((a.detail||'a subagent').slice(0,64))).join('<br>')+'</div>';
    } else {
      html += '<div class="nt-label">Runs</div><div class="nt-text">'+
        runs.map(w=>esc(w.name||'workflow')+' — '+(w.done||0)+'/'+(w.total||0)+(w.running?(' ('+w.running+' live)'):'')).join('<br>')+'</div>';
    }
    html += '<div class="nt-hint">a dynamic workflow (Workflow tool)</div>';
    nametag.innerHTML = html;
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  // an open-shell terminal window? (above the desk) -- takes precedence over the agent
  const shx=pickShell(m.x,m.y);
  if(shx){
    hover=null; cv.style.cursor='help';
    const s=shx.shell||{};
    nametag.innerHTML =
      '<div class="nt-name">shell<span class="nt-badge working">running</span></div>'+
      '<div class="nt-label">Command</div>'+
      '<div class="nt-text">'+esc(s.command||'(background command)')+'</div>'+
      (s.output_tail ? ('<div class="nt-label">Latest output</div><div class="nt-text">'+esc(s.output_tail)+'</div>') : '')+
      '<div class="nt-hint">a running background shell</div>';
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  // a subagent dwarf? (they sit by the desk) -- takes precedence over the agent
  const dw=pickHelper(m.x,m.y);
  if(dw){
    hover=null; cv.style.cursor='help';
    // subagent dwarf
    const s=dw.sub||{};
    // workflow subagents reuse the regular subagent tooltip (same structure + badge style).
    // "general-purpose"/"workflow-subagent" (uninformative default types) tell you nothing --
    // for those (or a missing type) show the task detail as the title, dropping the detail line.
    const isWf = s.type==='workflow-subagent';
    const generic = !s.type || !s.type.length || s.type==='general-purpose' || isWf;
    const ttl = generic ? (s.detail || 'a background task') : s.type;
    nametag.innerHTML =
      '<div class="nt-name">'+esc(ttl)+'<span class="nt-badge scheduled">'+(isWf?'workflow subagent':'helper')+'</span></div>'+
      (generic ? '' :
        '<div class="nt-label">This subagent is</div>'+
        '<div class="nt-text">'+esc(s.detail||'working on a background task')+'</div>')+
      (s.last_tool ? ('<div class="nt-label">Last tool used</div><div class="nt-text">'+esc(s.last_tool)+'</div>') : '')+
      (s.last_message ? ('<div class="nt-label">Last message</div><div class="nt-text">'+esc(s.last_message)+'</div>') : '')+
      '<div class="nt-hint">a running '+(isWf?'workflow ':'')+'subagent</div>';
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  hover=pick(m.x,m.y);
  if(hover){
    cv.style.cursor='pointer';
    const a=hover.agent;
    const where = a.status==='working' ? 'at a desk' : 'in the kitchen';
    const meta = [a.project, a.last_activity_rel? ('active '+a.last_activity_rel):null,
                  (a.message_count!=null? a.message_count+' msgs':null),
                  (a.subs>0? (a.subs+' subagent'+(a.subs>1?'s':'')):null),
                  (a.spend!=null? '$'+a.spend.toFixed(2):null),
                  fmtTokens(a.tokens),
                  (a.model!=null? a.model:null)].filter(Boolean).join('  ·  ');
    // show the last tool used (with detail) and the last text message SEPARATELY. Fall back
    // to the generic "latest" only when the split fields aren't populated (e.g. Cursor).
    const toolLbl = a.status==='working' ? 'Currently running' : 'Last tool used';
    const hasSplit = a.last_tool || a.last_message;
    nametag.innerHTML =
      '<div class="nt-name">'+esc(nameFor(a.id))+
        '<span class="nt-badge '+a.status+'">'+esc(a.status)+'</span>'+
        srcBadgeHTML(a.source)+
        (a.scheduled?'<span class="nt-badge scheduled">scheduled</span>':'')+'</div>'+
      '<div class="nt-meta">'+esc(meta)+'  ·  '+where+'</div>'+
      '<div class="nt-label">Task</div>'+
      '<div class="nt-text">'+esc(a.title||'(untitled session)')+'</div>'+
      (a.last_instruction ? ('<div class="nt-label">Last instruction</div><div class="nt-text">'+esc(a.last_instruction)+'</div>') : '')+
      (a.last_tool ? ('<div class="nt-label">'+toolLbl+'</div><div class="nt-text">'+esc(a.last_tool)+'</div>') : '')+
      (a.last_message ? ('<div class="nt-label">Last message</div><div class="nt-text">'+esc(a.last_message)+'</div>') : '')+
      (hasSplit ? '' : ('<div class="nt-label">Latest activity</div><div class="nt-text">'+esc(a.latest||a.preview||a.title||'')+'</div>'))+
      '<div class="nt-hint">click to open full session</div>';
    nametag.style.display='block'; placeNametag(m);
  } else { nametag.style.display='none'; cv.style.cursor='default'; }
});
cv.addEventListener('mouseleave',()=>{hover=null;nametag.style.display='none';});
cv.addEventListener('click', e=>{
  const m=toCanvas(e);
  const pet=pickPet(m.x,m.y);                 // pet the dog/cat before opening any worker
  if(pet){ if(pet==='dog') petDog(); else petCat(); return; }
  const slot=pickVend(m.x,m.y);               // click a drink -> it drops into the tray
  if(slot){ dispenseDrink(slot); return; }
  const p=pick(m.x,m.y);
  if(p) openDetail(p.agent.id);
});

function esc(s){return (s||'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));}
// compact token count for the hover card ("1.2M tokens" / "840k tokens")
function fmtTokens(n){ if(n==null) return null;
  if(n>=1e6) return (n/1e6).toFixed(n>=1e7?0:1)+'M tokens';
  if(n>=1e3) return Math.round(n/1e3)+'k tokens';
  return n+' tokens'; }
// which tool made this worker -- Cursor vs Claude Code
function srcLabel(source){ return source==='claude' ? 'Claude Code' : 'Cursor'; }
function srcBadgeHTML(source){
  const cls = source==='claude' ? 'src-claude' : 'src-cursor';
  return '<span class="nt-badge '+cls+'">'+esc(srcLabel(source))+'</span>';
}
// small on-canvas source marker (a little colored sign floating above the head)
const SRC_COLORS = { cursor:'#2b6d84', claude:'#d97757' };
function drawSourceTag(x, topY, source){
  const col = SRC_COLORS[source] || SRC_COLORS.cursor;
  // a 6x4 rounded plaque with a soft outline + top gloss, centered on x
  px(x-4, topY,   8, 1, 'rgba(0,0,0,.35)');
  px(x-4, topY,   8, 4, col);
  px(x-4, topY,   8, 1, 'rgba(255,255,255,.4)');
  px(x-4, topY+3, 8, 1, 'rgba(0,0,0,.28)');
}

// ---- overlay ----
const overlay=document.getElementById('overlay');
let currentDetail=null;
async function openDetail(id){
  let d=detailCache[id];
  if(!d){
    try{ const res=await fetch('/api/agent/'+encodeURIComponent(id)); d=await res.json(); detailCache[id]=d; }
    catch(err){ toast('failed to load'); return; }
  }
  if(!d||d.error){ toast('not found'); return; }
  currentDetail=d;
  updateFinishBtn(d.id);
  document.getElementById('d-name').textContent=nameFor(d.id);
  document.getElementById('d-sub').innerHTML=
    '<span class="badge '+d.status+'">'+d.status.toUpperCase()+'</span> '+
    '<span class="badge '+(d.source==='claude'?'src-claude':'src-cursor')+'">'+esc(srcLabel(d.source).toUpperCase())+'</span> '+
    (d.scheduled?'<span class="badge scheduled">SCHEDULED</span> ':'')+'&nbsp; '+
    esc(d.project)+' &nbsp;·&nbsp; '+esc(d.last_activity_rel)+' &nbsp;·&nbsp; '+d.message_count+' msgs';
  const body=document.getElementById('dbody');
  let html='';
  html+='<section><h4>Task</h4><div class="box role-user">'+esc(d.task_full||d.title||'(none)')+'</div></section>';
  if(d.latest_tool){
    html+='<section><h4>Last action</h4><span class="tool">'+esc(d.latest_tool.name)+'</span> '+esc(d.latest_tool.detail||'')+'</section>';
  }
  // dynamic Workflow runs -- the easel only shows while the parent is seated, so this
  // is the place to review a workflow after it finishes and its tent has closed.
  if(d.workflows && d.workflows.length){
    html+='<section><h4>Workflows</h4>';
    for(const w of d.workflows){
      html+='<div class="box" style="margin-bottom:8px">'+
        '<div style="font-size:11px;color:var(--card-ink)"><b>'+esc(w.name||'workflow')+'</b> '+
        '<span class="badge workflow">'+(w.done||0)+'/'+(w.total||0)+'</span>'+
        (w.running?' <span class="badge working">'+w.running+' running</span>':'')+'</div>'+
        (w.summary?('<div style="font-size:10px;color:var(--card-ink-lo);margin-top:4px">'+esc(w.summary)+'</div>'):'')+
        (w.phases&&w.phases.length?('<div style="margin-top:5px">'+w.phases.map(p=>'<span class="tool">'+esc(p.title)+'</span>').join('')+'</div>'):'')+
      '</div>';
    }
    html+='</section>';
  }
  html+='<section><h4>Latest thinking / response</h4><div class="box">'+esc(d.latest_response||'(no assistant message yet)')+'</div></section>';
  if(d.timeline && d.timeline.length){
    html+='<section><h4>Recent activity</h4>';
    for(const ev of d.timeline){
      if(ev.role==='system'){ html+='<div class="turn">'+esc(ev.text)+'</div>'; continue; }
      let tools=''; (ev.tools||[]).forEach(tl=>{ tools+='<span class="tool">'+esc(tl.name)+(tl.detail?': '+esc(tl.detail):'')+'</span>'; });
      const cls = ev.role==='user'?'role-user':'';
      if(ev.text || tools){
        html+='<div class="'+cls+'" style="margin-bottom:8px"><div style="font-size:8px;letter-spacing:1px;color:'+(ev.role==='user'?'#6b6e78':'#3a3d46')+';margin-bottom:3px">'+ev.role.toUpperCase()+'</div>';
        if(ev.text) html+='<div class="box">'+esc(ev.text)+'</div>';
        if(tools) html+='<div style="margin-top:4px">'+tools+'</div>';
        html+='</div>';
      }
    }
    html+='</section>';
  }
  const jumpHelp = d.source==='claude'
    ? 'Claude Code has no public deep link to a past session yet. Use <b>Open Transcript File</b> to view the raw <code>.jsonl</code>, or <b>Copy Session ID</b> and resume with <code>claude --resume '+esc(d.id)+'</code>.'
    : 'Cursor has no public deep link to a specific past chat session yet, so this id can\u2019t auto-open the chat. Use <b>Open Transcript File</b> to view the raw <code>.jsonl</code> in Cursor, or <b>Copy Session ID</b> and find it under the sidebar\u2019s Previous Chats.';
  html+='<section><h4>Jump back to this chat</h4><div class="box">'+jumpHelp+'<br><br>session id: '+esc(d.id)+'</div></section>';
  body.innerHTML=html; body.scrollTop=0;
  overlay.style.display='flex';
}
function closeDetail(){overlay.style.display='none';currentDetail=null;}
document.getElementById('d-x').addEventListener('click',closeDetail);
overlay.addEventListener('click',e=>{ if(e.target===overlay) closeDetail(); });
document.addEventListener('keydown',e=>{ if(e.key==='Escape') closeDetail(); });

// mark / unmark an agent as "finished" -> it walks to the beach (or back to work)
function updateFinishBtn(id){
  const b=document.getElementById('d-finish');
  const on=finishedIds.has(id);
  b.innerHTML = on ? '&#8617;&#65039; BRING BACK TO WORK' : '&#127958; SEND TO BEACH';
  b.classList.toggle('ghost', on);
}
document.getElementById('d-finish').addEventListener('click',()=>{
  if(!currentDetail) return;
  const id=currentDetail.id;
  if(finishedIds.has(id)){ finishedIds.delete(id); toast('back to work'); }
  else { finishedIds.add(id); toast('off to the beach 🏖️'); }
  saveFinished(); updateFinishBtn(id); rebuild();
});
document.getElementById('d-open').addEventListener('click',()=>{
  if(!currentDetail) return;
  const path=currentDetail.transcript_path||'';
  if(!path || path.indexOf('demo')>=0){ toast('demo worker - no file'); return; }
  // Cursor has no deep link to a past chat session, so we open the raw
  // transcript file (.jsonl) in Cursor as the closest available action.
  window.location.href='cursor://file'+ (path.startsWith('/')?'':'/') + path.split('/').map(encodeURIComponent).join('/');
  toast('opening transcript file in Cursor...');
});
document.getElementById('d-copy').addEventListener('click',async ()=>{
  if(!currentDetail) return;
  try{ await navigator.clipboard.writeText(currentDetail.id); toast('session id copied'); }
  catch(e){ toast(currentDetail.id); }
});
// CELEBRATE button: everyone dances ~3s + a screen-wide confetti burst (reuses finish-fx)
document.getElementById('celebrate').addEventListener('click',()=>{
  const now=performance.now();
  people.forEach(p=>{ p.celebrateUntil=now+3000; });
  spawnConfetti(W/2, H*0.22);
  toast('party time!');
});
// WHIP button: crack the whip -- everyone flinches + works harder ~3s (opposite of CELEBRATE)
document.getElementById('whip').addEventListener('click',()=>{
  const now=performance.now();
  // ONLY the working (seated, at-desk) agents get whipped -- kitchen / beach folk are left alone
  let struck=0;
  people.forEach(p=>{ if(p.kind==='work' && p.seated){
    p.whipUntil=now+1400;                                  // brief "work harder" burst (short)
    spawnWhip(Math.round(p.x), Math.round(p.y)-Math.round(28*SC));  // a lash snaps over each desk
    struck++;
  } });
  toast(struck ? 'back to work!' : 'nobody at their desk!');
});

let toastT=null;
function toast(msg){ const el=document.getElementById('toast'); el.textContent=msg; el.style.display='block';
  clearTimeout(toastT); toastT=setTimeout(()=>el.style.display='none',1800); }

// ---- data polling ----
async function refresh(){
  try{
    const res=await fetch('/api/agents'); const data=await res.json();
    WINDOW_HOURS=data.hours||24; document.getElementById('emh').textContent=WINDOW_HOURS;
    document.getElementById('scope').textContent='scope: '+(data.scope||'all projects');
    agents=data.agents||[]; rebuild();
    detectMessages(agents);
    detectInstructions(agents);
    detectFinishes(agents);
  }catch(e){/* keep last */}
}
// ---- gentle "an agent finished" chime (Web Audio, no files) ----
let audioCtx = null;
let soundOn = (localStorage.getItem('office_sound') !== 'off');
function initAudio(){
  if(!audioCtx){ try{ audioCtx = new (window.AudioContext||window.webkitAudioContext)(); }catch(e){ audioCtx=null; } }
  if(audioCtx && audioCtx.state==='suspended') audioCtx.resume();
}
// browsers block audio until a user gesture -- unlock on the first interaction
['pointerdown','keydown'].forEach(ev=>window.addEventListener(ev, initAudio));
function playFinishChime(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime;
  // a soft two-note bell (C6 -> E6): quiet sine tones with a gentle attack/decay
  [[1046.5,0.0],[1318.5,0.085]].forEach(([freq,dt])=>{
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.type='sine'; o.frequency.value=freq;
    const s=t0+dt;
    g.gain.setValueAtTime(0.0001, s);
    g.gain.exponentialRampToValueAtTime(0.07, s+0.015);   // soft attack (kept low = not annoying)
    g.gain.exponentialRampToValueAtTime(0.0001, s+0.33);  // gentle decay
    o.connect(g).connect(audioCtx.destination);
    o.start(s); o.stop(s+0.35);
  });
}
// a low rumbly purr (triangle tone with a fast tremolo LFO) when you pet the cat
function playPurr(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime;
  const o=audioCtx.createOscillator(), g=audioCtx.createGain();
  const lfo=audioCtx.createOscillator(), lg=audioCtx.createGain();
  o.type='triangle'; o.frequency.value=55;
  lfo.type='sine'; lfo.frequency.value=24; lg.gain.value=0.035;   // tremolo -> purr rumble
  lfo.connect(lg).connect(g.gain);
  g.gain.setValueAtTime(0.06, t0); g.gain.setValueAtTime(0.06, t0+1.1);
  g.gain.exponentialRampToValueAtTime(0.0001, t0+1.45);
  o.connect(g).connect(audioCtx.destination);
  o.start(t0); lfo.start(t0); o.stop(t0+1.45); lfo.stop(t0+1.45);
}
// a short filtered-noise "scritch" when the cat swipes the screen
function playScratch(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime, dur=0.18, n=Math.floor(audioCtx.sampleRate*dur);
  const buf=audioCtx.createBuffer(1,n,audioCtx.sampleRate), ch=buf.getChannelData(0);
  for(let i=0;i<n;i++) ch[i]=(Math.random()*2-1)*(1-i/n);       // decaying white noise
  const src=audioCtx.createBufferSource(); src.buffer=buf;
  const bp=audioCtx.createBiquadFilter(); bp.type='bandpass'; bp.frequency.value=2800; bp.Q.value=1.1;
  const g=audioCtx.createGain(); g.gain.value=0.09;
  src.connect(bp).connect(g).connect(audioCtx.destination); src.start(t0);
}
const soundBtn=document.getElementById('sound');
function updateSoundBtn(){ soundBtn.innerHTML=(soundOn?'&#9834; ON':'&#9834; OFF'); soundBtn.classList.toggle('off', !soundOn); }
soundBtn.addEventListener('click',()=>{
  soundOn=!soundOn; localStorage.setItem('office_sound', soundOn?'on':'off');
  initAudio(); if(soundOn) playFinishChime();   // the toggle also previews the sound
  updateSoundBtn();
});
updateSoundBtn();

// ---- hide-scheduled (courier) filter toggle ----
const filterBtn=document.getElementById('filter');
function updateFilterBtn(){
  filterBtn.innerHTML = hideScheduled ? '&#9993; HIDDEN' : '&#9993; SHOWN';
  filterBtn.classList.toggle('on', hideScheduled);
  filterBtn.classList.toggle('off', !hideScheduled);
  filterBtn.title = hideScheduled
    ? 'scheduled / courier agents hidden — click to show'
    : 'click to hide scheduled / courier agents';
}
filterBtn.addEventListener('click',()=>{
  hideScheduled=!hideScheduled;
  localStorage.setItem('office_hide_scheduled', hideScheduled?'on':'off');
  rebuild();            // immediate: couriers walk off-screen, or walk back in
  updateFilterBtn();
});
updateFilterBtn();

// ---- agent name-style cycle (magical / israeli / dev / robots) ----
const namesBtn=document.getElementById('names');
function updateNamesBtn(){ namesBtn.textContent='NAMES: '+NAME_SETS[nameStyle].label; }
namesBtn.addEventListener('click',()=>{
  nameStyle=NAME_ORDER[(NAME_ORDER.indexOf(nameStyle)+1)%NAME_ORDER.length];
  localStorage.setItem('office_names', nameStyle);
  updateNamesBtn();
  if(currentDetail) document.getElementById('d-name').textContent=nameFor(currentDetail.id);  // refresh open card
  toast('names: '+NAME_SETS[nameStyle].label.toLowerCase());
});
updateNamesBtn();

// pop a temporary bubble whenever an agent / subagent / workflow-sub authors a NEW message
// between polls. Desk & kitchen agents key off `latest` (their latest assistant text);
// dwarves key off each sub's stable `id` + a `ts`/`last_msg` change token.
function detectMessages(list){
  const now=performance.now();
  const cur={};
  // Track each agent's latest-content token REGARDLESS of working/waiting, so a mere
  // waiting->working flip (which surfaces the agent's OLD last message as it sits back down)
  // does NOT read as a "new message" and flash a stale bubble. A bubble/chip fires only when
  // the content genuinely CHANGES on a WORKING agent, and never while a boss is delivering
  // an instruction (only the boss talks). 'task' kind shows nothing.
  for(const a of list)
    cur[a.id] = (a.latest_kind==='assistant' || a.latest_kind==='tool')
                ? (a.latest_kind+'|'+(a.latest||'')) : '';
  if(msgSeen!==null){
    for(const a of list){ const tok=cur[a.id];
      if(tok && msgSeen[a.id]!==undefined && msgSeen[a.id]!==tok
          && a.status==='working' && !bossActive(a.id)){
        const p=people.find(q=>q.id===a.id);
        if(p){ const isTool=a.latest_kind==='tool';
          p.bubbleTool=isTool;
          p.bubbleText=isTool?toolChip(a.latest):firstWords(a.latest);
          p.bubbleStart=now; p.bubbleUntil=now+BUBBLE_MS;
        }
      }
    }
  }
  msgSeen=cur;
  const alive=new Set();
  const scan=(arr)=>{ (arr||[]).forEach(s=>{ if(!s||!s.id) return; alive.add(s.id);
    const tok=String(s.ts||'')+'|'+(s.last_msg||'');
    if(s.last_msg && subMsgSeen[s.id]!==undefined && subMsgSeen[s.id]!==tok){
      const isTool=s.last_kind==='tool';
      subBubbles[s.id]={text:isTool?toolChip(s.last_msg):firstWords(s.last_msg),
                        start:now, until:now+BUBBLE_MS, tool:isTool};
    }
    subMsgSeen[s.id]=tok;
  }); };
  for(const a of list){ scan(a.subagents); (a.workflows||[]).forEach(w=>scan(w.active)); }
  Object.keys(subMsgSeen).forEach(id=>{ if(!alive.has(id)) delete subMsgSeen[id]; });
  Object.keys(subBubbles).forEach(id=>{ if(subBubbles[id].until < now-BUBBLE_FADE) delete subBubbles[id]; });
}

// when a NEW user instruction lands on a working agent between polls, send a "boss" over to
// that agent's desk to deliver it (a supervisor sprite + a speech bubble with the message).
function detectInstructions(list){
  const now=performance.now();
  const cur={};
  for(const a of list) cur[a.id] = (a.status==='working') ? (a.last_instruction||'') : '';
  if(instrSeen!==null){
    for(const a of list){ const tok=cur[a.id];
      if(tok && instrSeen[a.id]!==undefined && instrSeen[a.id]!==tok)
        bossVisits[a.id]={text:tok, start:now, until:now+BOSS_MS};
    }
  }
  instrSeen=cur;
  Object.keys(bossVisits).forEach(id=>{ if(bossVisits[id].until < now-400) delete bossVisits[id]; });
}

// fire a celebration (+ chime) when an agent transitions working -> waiting between polls
function detectFinishes(list){
  const cur={}; list.forEach(a=>cur[a.id]=a.status);
  if(prevStatus===null){ prevStatus=cur; return; }   // first poll: seed map, no fires
  let anyFinished=false;
  const now=performance.now();
  for(const a of list){
    if(prevStatus[a.id]==='working' && a.status==='waiting'){
      anyFinished=true;
      const p=people.find(q=>q.id===a.id);
      if(p){ p.celebrateUntil=now+2200;
             spawnConfetti(Math.round(p.x), Math.round(p.y)-Math.round(46*SC));
             // the agent's LAST message: it just stood up and left the desk, so
             // detectMessages (working-only) never bubbled it. Pop it here as a parting
             // speech bubble that follows the agent as it walks off to the kitchen.
             if(a.latest_kind==='assistant' && a.latest){
               p.bubbleTool=false; p.bubbleText=firstWords(a.latest);
               p.bubbleStart=now; p.bubbleUntil=now+BUBBLE_MS; }
      }
      else { spawnConfetti(W/2, H*0.2); }
    }
  }
  if(anyFinished) playFinishChime();   // once per poll, even if several finished at once
  prevStatus=cur;
}
function clock(){ document.getElementById('clock').textContent=new Date().toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'}); }
setInterval(clock,1000); clock();
refresh(); setInterval(refresh, 4000);
// ---- dev hot-reload: in --watch mode the server re-execs on file change, minting a
// fresh token; the tab reloads itself when it notices. No-op unless --watch is on. ----
(async function initWatch(){
  try{
    const v=await (await fetch('/api/version')).json();
    if(!v.watch) return;
    let token=v.token;
    setInterval(async()=>{
      try{
        const n=await (await fetch('/api/version')).json();
        if(n.token && n.token!==token){ location.reload(); }
      }catch(e){/* server mid-restart; try again next tick */}
    }, 1200);
  }catch(e){/* no version endpoint -> old server, ignore */}
})();
requestAnimationFrame(tick);
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------------------
# HTTP server
# --------------------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    hours = 24
    demo = False
    project_filter = None
    sources = None  # None -> all sources (cursor + claude)

    def log_message(self, *args):
        pass  # quiet

    def _send(self, code, body, ctype="application/json"):
        if isinstance(body, (dict, list)):
            body = json.dumps(body).encode("utf-8")
        elif isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype + ("; charset=utf-8" if "json" in ctype or "html" in ctype else ""))
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        try:
            if path in ("/", "/index.html"):
                self._send(200, PAGE, "text/html")
                return
            if path == "/api/version":
                # dev hot-reload signal: the page reloads itself when this token changes
                self._send(200, {"token": START_TOKEN, "watch": WATCH_MODE})
                return
            if path == "/api/agents":
                if self.demo:
                    agents = demo_agents()
                else:
                    agents = get_agents(self.hours, full=False,
                                        project_filter=self.project_filter,
                                        sources=self.sources)
                self._send(200, {
                    "hours": self.hours,
                    "scope": self.project_filter or "all projects",
                    "agents": agents,
                })
                return
            if path.startswith("/api/agent/"):
                uuid = unquote(path[len("/api/agent/"):])
                detail = demo_detail(uuid) if self.demo else get_agent_detail(uuid)
                if not detail and not self.demo:
                    detail = demo_detail(uuid)
                if not detail:
                    self._send(404, {"error": "not found"})
                    return
                self._send(200, detail)
                return
            self._send(404, {"error": "not found"})
        except BrokenPipeError:
            pass
        except Exception as exc:  # never crash the office
            try:
                self._send(500, {"error": str(exc)})
            except Exception:
                pass


def _start_watcher(interval=1.0):
    """Dev hot-reload: watch this source file and re-exec the whole process when it
    changes, so a single edit refreshes both the backend and the embedded PAGE. The
    browser tab reloads itself off the new START_TOKEN (see /api/version)."""
    src = os.path.abspath(__file__)
    try:
        last = os.stat(src).st_mtime
    except OSError:
        last = 0.0

    def _watch():
        nonlocal last
        while True:
            time.sleep(interval)
            try:
                m = os.stat(src).st_mtime
            except OSError:
                continue
            if m != last:
                last = m
                print("[watch] change detected -> reloading server...", flush=True)
                # small settle delay so a half-written file doesn't re-exec mid-save
                time.sleep(0.3)
                # mark the re-exec so the reloaded process skips the banner + browser re-open
                # (execv keeps the current environment) -- the open tab reloads itself instead.
                os.environ["AGENT_OFFICE_RELOADED"] = "1"
                os.execv(sys.executable, [sys.executable] + sys.argv)

    threading.Thread(target=_watch, daemon=True).start()
    print(f"[watch] hot-reload on: watching {os.path.basename(src)} for changes", flush=True)


def main():
    ap = argparse.ArgumentParser(description="Game Boy office of your Cursor + Claude Code agents.")
    ap.add_argument("--port", type=int, default=8787)
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--hours", type=float, default=24, help="activity window in hours (default 24)")
    ap.add_argument("--project", "-p", default=None,
                    help="only show one root/project (substring match, e.g. 'my-app'). "
                         "Omit to show ALL projects across every root.")
    ap.add_argument("--list-projects", action="store_true",
                    help="list the projects/roots with active sessions, then exit")
    ap.add_argument("--no-cursor", action="store_true", help="hide Cursor agents")
    ap.add_argument("--no-claude", action="store_true", help="hide Claude Code agents")
    ap.add_argument("--no-workflows", action="store_true",
                    help="hide dynamic workflow tents (the Workflow tool's runs)")
    ap.add_argument("--active-secs", type=float, default=120.0,
                    help="multitask subagent freshness window (seconds). A chat whose own "
                         "turn has ended still shows working (at a desk) if a background "
                         "subagent was written within this many seconds; otherwise it waits "
                         "in the kitchen. Working chats are primarily decided by turn state, "
                         "not recency. Default 120.")
    ap.add_argument("--demo", action="store_true", help="show fake workers (no real data)")
    ap.add_argument("--no-open", action="store_true", help="do not auto-open the browser")
    ap.add_argument("--watch", action="store_true",
                    help="dev hot-reload: restart the server (and auto-reload the "
                         "browser tab) whenever cursor_office.py is edited")
    args = ap.parse_args()

    sources = [name for name, _d, _p in _SOURCES
               if not (name == "cursor" and args.no_cursor)
               and not (name == "claude" and args.no_claude)]
    if not sources:
        ap.error("--no-cursor and --no-claude can't both be set (nothing to show).")

    if args.list_projects:
        rows = list_projects(args.hours, sources=sources)
        print(f"Projects/roots with sessions active in the last {args.hours:g}h:")
        if not rows:
            print("  (none - try a larger --hours window)")
        for pretty, raw, n, src in rows:
            print(f"  {n:>3}  [{src:<6}] {pretty:<24}  ({raw})")
        print("\nUse:  python3 cursor_office.py --project <name>   to scope to one root.")
        return

    global SUBAGENT_ACTIVE_SECONDS, SHOW_WORKFLOWS, WATCH_MODE
    SUBAGENT_ACTIVE_SECONDS = max(15, args.active_secs)
    SHOW_WORKFLOWS = not args.no_workflows
    WATCH_MODE = args.watch
    if WATCH_MODE:
        _start_watcher()

    Handler.hours = args.hours
    Handler.demo = args.demo
    Handler.project_filter = args.project
    Handler.sources = sources

    httpd = ThreadingHTTPServer((args.host, args.port), Handler)
    url = f"http://{args.host}:{args.port}"

    if not args.demo:
        dirs = []
        if "cursor" in sources:
            dirs.append(("Cursor", CURSOR_PROJECTS_DIR))
        if "claude" in sources:
            dirs.append(("Claude Code", CLAUDE_PROJECTS_DIR))
        missing = [(label, d) for label, d in dirs if not os.path.isdir(d)]
        if len(missing) == len(dirs):
            for label, d in missing:
                print(f"[!] {d} not found - is {label} installed for this user?")
            print("    You can still preview the office with:  python3 cursor_office.py --demo")

    # a --watch re-exec re-runs main(): don't reprint the full banner or reopen the browser
    # (the already-open tab reloads itself off the new START_TOKEN). Only the FIRST launch does.
    reloaded = os.environ.get("AGENT_OFFICE_RELOADED") == "1"
    if reloaded:
        print(f"[watch] reloaded -> serving at {url}", flush=True)
    else:
        src_labels = " + ".join(s.capitalize() for s in sources)
        data_dirs = []
        if "cursor" in sources:
            data_dirs.append(CURSOR_PROJECTS_DIR)
        if "claude" in sources:
            data_dirs.append(CLAUDE_PROJECTS_DIR)
        print("=" * 60)
        print("  AGENT OFFICE  (Game Boy edition)")
        print("=" * 60)
        print(f"  Serving at:   {url}")
        print(f"  Window:       last {args.hours:g}h" + ("   [DEMO MODE]" if args.demo else ""))
        print(f"  Sources:      {src_labels}")
        print(f"  Scope:        {args.project or 'ALL projects / roots'}")
        print(f"  Status:       turn-state (office=turn in progress; multitask subagent window {args.active_secs:g}s; stale cap {WORKING_STALE_CAP_SECONDS:g}s)")
        print(f"  Data source:  {', '.join(data_dirs)}")
        print("  Press Ctrl+C to stop.")
        print("=" * 60)

    if not args.no_open and not reloaded:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nbye!")
        httpd.shutdown()


if __name__ == "__main__":
    main()
