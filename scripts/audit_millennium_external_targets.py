#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path

EXPECTED = {
    "p_versus_np": {
        "Millennium.ClayPVersusNP",
        "Millennium.ClayPVersusNP.Formulations.NegativeBranch",
        "ProblemStatus.open_problem",
    },
    "riemann_hypothesis": {
        "Millennium.ClayRiemannHypothesis",
        "Millennium.clay_prize_riemann_hypothesis",
        "ProblemStatus.open_problem",
    },
    "navier_stokes": {
        "MillenniumNavierStokes.FeffermanA",
        "MillenniumNavierStokes.FeffermanB",
        "MillenniumNavierStokes.FeffermanC",
        "MillenniumNavierStokes.FeffermanD",
        "ProblemStatus.open_problem",
    },
    "hodge_conjecture": {
        "MillenniumHodge.ClayHodge",
        "ProblemStatus.statement_incomplete",
    },
    "birch_swinnerton_dyer": {
        "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer",
        "MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer",
        "ProblemStatus.open_problem",
    },
    "yang_mills": {
        "MillenniumYangMills.ClayYangMills",
        "ProblemStatus.statement_incomplete",
    },
    "poincare": {
        "MillenniumPoincare.ClayPoincareConjecture",
        "ProblemStatus.solved_problem",
    },
}

ORDER = list(EXPECTED)


def _block(text: str, name: str, next_name: str | None) -> str:
    marker = f"def {name} : ClayProblem where"
    start = text.find(marker)
    if start < 0:
        raise ValueError(f"missing registry entry {name}")
    if next_name is None:
        end = text.find("/-! ## Derived views", start)
    else:
        end = text.find(f"def {next_name} : ClayProblem where", start + len(marker))
    if end < 0:
        end = len(text)
    return text[start:end]


def audit_registry_text(text: str) -> None:
    for index, name in enumerate(ORDER):
        next_name = ORDER[index + 1] if index + 1 < len(ORDER) else None
        block = _block(text, name, next_name)
        for required in EXPECTED[name]:
            if required not in block:
                raise ValueError(f"{name}: missing expected registry token {required!r}")

    # Fail closed against accidental prize promotion of known-incomplete interfaces.
    for name in ("hodge_conjecture", "yang_mills"):
        index = ORDER.index(name)
        next_name = ORDER[index + 1] if index + 1 < len(ORDER) else None
        block = _block(text, name, next_name)
        if "ProblemStatus.open_problem" in block or "ProblemStatus.solved_problem" in block:
            raise ValueError(f"{name}: incomplete upstream target was promoted")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "registry",
        nargs="?",
        default="vendor/LeanMillenniumPrizeProblems/Problems/Registry.lean",
    )
    args = parser.parse_args()
    path = Path(args.registry)
    audit_registry_text(path.read_text(encoding="utf-8"))
    print(f"millennium external target audit: PASS ({path})")


if __name__ == "__main__":
    main()
