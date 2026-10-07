#!/usr/bin/env python3
from pathlib import Path

required = {
    "MillenniumExternal/TerminalCensus.lean": [
        "PNotEqualsNPClayCoreExact.agda",
        "PNotEqualsNPDirectSATLowerBoundExact.agda",
        "Synthesis.RiemannSelectedRHMaxCutFrontier",
        "ExternalClayNS/LiteralABCD.lean",
        "Synthesis.MillenniumBSDUniversalRankWeld",
        "MillenniumHodge.ClayHodge",
        "MillenniumYangMills.ClayYangMills",
    ],
    "MillenniumExternal/ExactTargetSurface.lean": [
        "import Problems.PVersusNP.Millennium",
        "import Problems.RiemannHypothesis.Millennium",
        "import Problems.NavierStokes.Millennium",
        "import Problems.BirchSwinnertonDyer.Millennium",
        "Millennium.ClayPVersusNP.Formulations.NegativeBranch",
        "Millennium.ClayRiemannHypothesis",
        "MillenniumNavierStokes.FeffermanA",
        "MillenniumNavierStokes.FeffermanB",
        "MillenniumNavierStokes.FeffermanC",
        "MillenniumNavierStokes.FeffermanD",
        "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer",
        "ClayRiemannHypothesis.of_mathlib",
        "ClayRiemannHypothesis.mathlib",
        "clayRiemannHypothesis_iff_mathlib",
        "BSDLeanDojoSameObjectWeld",
        "rankExistence_of_dashi",
        "LeanDojoBSDFiniteRank",
        "ClayBirchSwinnertonDyer.of_rank_existence_and_finite_rank",
        "clayBirchSwinnertonDyer_of_dashi",
    ],
    "ExternalClayNS/LeanDojoTargetBridge.lean": [
        "import LiteralABCD",
        "import Problems.NavierStokes.Millennium",
        "LeanDojoCDStatementWeld",
        "c_iff : ClayOptionC ↔ MillenniumNavierStokes.FeffermanC",
        "d_iff : ClayOptionD ↔ MillenniumNavierStokes.FeffermanD",
        "leanDojoFeffermanC_of_statementWeld",
        "leanDojoFeffermanD_of_statementWeld",
        "leanDojoFeffermanCD_of_statementWeld",
    ],
    "MillenniumExternal/ExternalTargetFrontier.lean": [
        ".upstreamIncomplete",
        ".redType",
        "hodge_not_green_exact",
        "yangMills_not_green_exact",
    ],
    "vendor/LeanMillenniumPrizeProblems.VENDOR": [
        "603053dc267cf3efe422f438eb78098c0ececd6f",
        "Apache-2.0",
        "leanprover/lean4:v4.31.0",
    ],
}

for filename, needles in required.items():
    text = Path(filename).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise SystemExit(f"{filename}: missing {needle!r}")

# Exact adapter surfaces must never gain a local escape hatch. The pinned
# upstream tree is audited separately; this guard concerns only DASHI-authored
# adapters.
for filename in (
    "MillenniumExternal/ExactTargetSurface.lean",
    "ExternalClayNS/LeanDojoTargetBridge.lean",
):
    text = Path(filename).read_text(encoding="utf-8")
    for forbidden in ("sorry", "axiom ", "unsafe "):
        if forbidden in text:
            raise SystemExit(f"{filename}: forbidden token {forbidden!r}")

print("millennium external source audit: PASS")
