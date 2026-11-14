#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "Dashi/Biology/QuailEggHistamineGutSnowballExact.lean",
    ROOT / "Dashi/Biology/QuailEggHistamineGutSnowballRegression.lean",
    ROOT / "Dashi/Biology/QuailEggHistamineGutParetoSnowballExact.lean",
    ROOT / "Dashi/Biology/QuailEggHumanOralTransferExact.lean",
    ROOT / "Dashi/Biology/QuailEggHumanOralTransferRegression.lean",
    ROOT / "Dashi/Biology/QuailEggAllergySafetyBoundaryExact.lean",
    ROOT / "Dashi/Biology/QuailEggAllergySafetyBoundaryRegression.lean",
    ROOT / "Dashi/Biology/QuailHistamineMicrobiomeHostBridgeExact.lean",
    ROOT / "Dashi/Biology/QuailHistamineMicrobiomeHostBridgeRegression.lean",
    ROOT / "Dashi/Biology/QuailEggGutTransferRound2Exact.lean",
    ROOT / "Dashi/Biology/QuailEggGutTransferRound2Regression.lean",
    ROOT / "Dashi/Biology/GutMastCellMechanismRouteAtlasExact.lean",
    ROOT / "Dashi/Biology/GutMastCellMechanismRouteAtlasRegression.lean",
    ROOT / "Dashi/Biology/QuailEggOralGIAnimalBridgeExact.lean",
    ROOT / "Dashi/Biology/QuailEggOralGIAnimalBridgeRegression.lean",
    ROOT / "Dashi/Biology/QuailEggIBSTransferLadderExact.lean",
    ROOT / "Dashi/Biology/QuailEggIBSTransferLadderRegression.lean",
    ROOT / "Dashi/Biology/IBSHistamineH1InterventionUpdateExact.lean",
    ROOT / "Dashi/Biology/IBSHistamineH1InterventionUpdateRegression.lean",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.29219/fnr.v62.1084",
    "10.1016/j.fshw.2022.09.028",
    "10.1126/scitranslmed.abj1895",
    "10.1053/j.gastro.2015.12.034",
    "10.3390/nu13041262",
    "10.3389/fmicb.2020.01130",
    "10.1002/fsn3.147",
    "10.1017/S0022215122001219",
    "10.1016/j.jacig.2025.100486",
    "10.1159/000534825",
    "10.3177/jnsv.40.593",
    "10.1053/j.gastro.2025.07.016",
    "10.1038/s41598-018-19309-x",
    "10.1136/gutjnl-2023-331634",
    "10.1111/nmo.70242",
    "canonicalQuailEggIBSExperimentRequirement",
    "canonicalGutAcquisitionFrontier",
    "canonicalQuailHumanOralTransferBoundary",
    "canonicalQuailEggAllergySafetyBoundary",
    "canonicalQuailHistamineMicrobiomeHostBridge",
    "canonicalSameObjectQuailGutExperiment",
    "canonicalGutMastCellMechanismRouteAtlas",
    "canonicalQuailEggIBSTransferLadder",
    "canonicalIBSHistamineH1InterventionBoundary",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing quail/histamine mirror surface: " + ", ".join(missing))
print("quail/histamine gut mirror source surface: OK")
