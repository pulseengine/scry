#!/usr/bin/env python3
"""check_selfhosted_fork_guard.py: no fork PR reaches a self-hosted runner.

Adapted from ordeal's check of the same name (copy in bazel-file-ops-component). Every `runs-on:` line in
.github/workflows/ that names `self-hosted` must select it only for a
non-PR event or a PR from this repository, and fall back to a hosted
runner otherwise (fail closed):

  ${{ (github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('[...]') || 'ubuntu-latest' }}

The `head.repo.fork && 'ubuntu-latest' || ...` form is rejected: it
selects self-hosted whenever `.fork` is not true, including a null head
repo. A workflow that triggers on `pull_request_target` fails for any
self-hosted job, guarded or not: there `event_name` is never
'pull_request', so the guard would send fork PRs to self-hosted (found
by ordeal#322). The check also fails when it finds no self-hosted job,
so it never passes having checked nothing.
"""
import pathlib
import re
import sys

GUARD = ("${{ (github.event_name != 'pull_request' || "
         "github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('[")
TAIL = "]') || 'ubuntu-latest' }}"
root = pathlib.Path(__file__).resolve().parent.parent
bad, seen = [], []
for wf in sorted((root / ".github" / "workflows").glob("*.y*ml")):
    lines = wf.read_text().splitlines()
    # Conservative: any uncommented mention of the trigger counts.
    prt = any("pull_request_target" in l.split("#", 1)[0] for l in lines)
    for n, line in enumerate(lines, 1):
        m = re.match(r"\s+runs-on:\s*(.*)", line)
        if not m or "self-hosted" not in m.group(1):
            continue
        val = m.group(1).strip()
        where = f"{wf.name}:{n}"
        seen.append(where)
        if prt or not (val.startswith(GUARD) and val.endswith(TAIL)):
            bad.append(where)
for w in seen:
    print(f"{'FAIL' if w in bad else 'ok  '}  {w}")
if not seen:
    sys.exit("FAIL  no self-hosted job found: this check compared nothing")
if bad:
    sys.exit(f"FAIL  {len(bad)} self-hosted job(s) without the fail-closed fork guard, "
             "or in a pull_request_target workflow")
print(f"{len(seen)} self-hosted job(s), each with the fail-closed fork guard")
