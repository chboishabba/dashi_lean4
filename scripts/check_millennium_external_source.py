#!/usr/bin/env python3
from pathlib import Path

required = {
    "MillenniumExternal/TerminalCensus.lean": [
        "Millennium.ClayRiemannHypothesis",
        "MillenniumNavierStokes.FeffermanA|B|C|D",
        "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer",
        "MillenniumHodge.ClayHodge",
        "MillenniumYangMills.ClayYangMills",
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

print("millennium external source audit: PASS")
