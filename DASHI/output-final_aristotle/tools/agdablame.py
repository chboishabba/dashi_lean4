#!/usr/bin/env python3
"""Which upstream Agda modules block the most others.

`AgdaCheck` only attempts a module when every module it imports is attempted
too, so one module the front end cannot read can keep hundreds out.  This script
ranks the modules the front end refuses by how many other modules transitively
depend on them, which is the order in which fixing them pays.

    python3 tools/agdablame.py            # the ranking
    python3 tools/agdablame.py --n 40     # more of it
"""

from __future__ import annotations

import argparse
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import agda2lean as A  # noqa: E402
import agdacheck as C  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=25)
    args = ap.parse_args()

    gate = C.parse_report()
    skipped = C.load_skipped()
    info = {}
    for f in C.unique_corpus(gate):
        m, rs, deps = C.verbatim_reasons(f, gate)
        if not m:
            continue
        if m in skipped:
            rs = rs + [skipped[m] or "does not elaborate"]
        info[m] = (rs, [d for d in deps if not d.startswith(A.PRELUDE_PREFIXES)], f)

    ok = {m: not v[0] for m, v in info.items()}
    for m, (_rs, deps, _f) in info.items():
        if any(d not in info for d in deps):
            ok[m] = False
    changed = True
    while changed:
        changed = False
        for m, (_rs, deps, _f) in info.items():
            if ok[m] and any(not ok.get(d, False) for d in deps):
                ok[m] = False
                changed = True

    rdeps: dict[str, set[str]] = collections.defaultdict(set)
    for m, (_rs, deps, _f) in info.items():
        for d in deps:
            rdeps[d].add(m)

    def downstream(m: str) -> set[str]:
        seen: set[str] = set()
        stack = [m]
        while stack:
            for y in rdeps.get(stack.pop(), ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    blame = [(len(downstream(m)), m, info[m][0][0], info[m][2])
             for m in info if info[m][0]]
    blame.sort(reverse=True)
    print(f"attempted {sum(ok.values())} of {len(info)} modules")
    print(f"the {args.n} refusals that block the most:")
    for n, m, why, f in blame[:args.n]:
        print(f"{n:5d}  {m}\n         {os.path.relpath(f, A.ROOT)}\n         {why[:150]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
