#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "Dashi/Biology/IBSGutBrainImmuneSystemsHyperfabricExact.lean",
    ROOT / "Dashi/Biology/IBSSystemsIdentificationParetoExact.lean",
    ROOT / "Dashi/Biology/IBSSystemsIdentificationParetoRegression.lean",
    ROOT / "Dashi/Biology/IBSMechanismProbePerturbationAtlasExact.lean",
    ROOT / "Dashi/Biology/IBSMechanismProbePerturbationRegression.lean",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.1186/s40168-022-01450-5",
    "10.1007/s11894-026-01053-2",
    "10.3389/fnins.2026.1832540",
    "10.1016/j.ejim.2024.07.008",
    "10.1016/j.cgh.2026.04.014",
    "10.1053/j.gastro.2024.02.008",
    "canonicalIBSMeasurementAtlas",
    "canonicalMinimumDiscriminatingPanel",
    "canonicalIBSSystemsParetoFrontier",
    "canonicalIBSMechanismProbeAtlas",
    "canonicalIBSProbeParetoFrontier",
    "singleMarkerDoesNotIdentifyWholeSystemState",
    "crossSectionDoesNotIdentifyFeedbackDirection",
    "responseDoesNotIdentifyUniqueMechanism",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS systems-identification mirror surface: " + ", ".join(missing))
print("IBS systems-identification mirror source surface: OK")
