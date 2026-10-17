#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

FRONTIER_NAMES = {
    "proved": "PROVED",
    "typeWeld": "TYPE-WELD",
    "analytic": "ANALYTIC",
    "upstreamDefect": "UPSTREAM-DEFECT",
    "solvedUnformalized": "SOLVED-UNFORMALIZED",
}

RH_WELD_TOKENS = (
    "theorem clayRiemannHypothesis_of_mathlib",
    "theorem mathlibRiemannHypothesis_of_clay",
    "theorem clayRiemannHypothesis_iff_mathlib",
)

RECEIPT_RE = re.compile(
    r"\{\s*problem\s*:=\s*\.(?P<problem>\w+).*?"
    r"upstreamDeclaration\s*:=\s*\"(?P<upstream>[^\"]+)\".*?"
    r"state\s*:=\s*\.(?P<state>\w+).*?"
    r"frontier\s*:=\s*\.(?P<frontier>\w+).*?"
    r"firstUnpaid\s*:=\s*\"(?P<first_unpaid>[^\"]*)\"",
    re.S,
)


def parse_frontier(frontier_text: str, exact_text: str) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for match in RECEIPT_RE.finditer(frontier_text):
        raw_frontier = match.group("frontier")
        if raw_frontier not in FRONTIER_NAMES:
            raise ValueError(f"unknown frontier class: {raw_frontier}")
        problem = match.group("problem")
        rows.append(
            {
                "problem": problem,
                "upstream_declaration": match.group("upstream"),
                "closure_state": match.group("state"),
                "frontier": FRONTIER_NAMES[raw_frontier],
                "first_unpaid": match.group("first_unpaid"),
                "exact_statement_weld": problem == "riemann"
                and all(token in exact_text for token in RH_WELD_TOKENS),
            }
        )

    if len(rows) != 7 or len({row["problem"] for row in rows}) != 7:
        raise ValueError(f"expected seven unique Millennium receipts, got {len(rows)}")

    return {"schema_version": 1, "problems": rows}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "frontier",
        nargs="?",
        default="MillenniumExternal/ExternalTargetFrontier.lean",
    )
    parser.add_argument(
        "exact_surface",
        nargs="?",
        default="MillenniumExternal/ExactTargetSurface.lean",
    )
    args = parser.parse_args()
    data = parse_frontier(
        Path(args.frontier).read_text(encoding="utf-8"),
        Path(args.exact_surface).read_text(encoding="utf-8"),
    )
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
