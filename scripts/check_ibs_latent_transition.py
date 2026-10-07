#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "Dashi/Biology/IBSLatentStateTransitionExact.lean",
    ROOT / "Dashi/Biology/IBSLatentStateTransitionRegression.lean",
    ROOT / "Dashi/Biology/IBSTransitionTriggerAtlasExact.lean",
    ROOT / "Dashi/Biology/IBSTransitionTriggerAtlasRegression.lean",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.1016/j.cell.2020.08.007",
    "10.1111/nmo.13514",
    "10.1016/j.cgh.2026.05.008",
    "10.3389/frmbi.2026.1884540",
    "10.3748/wjg.v29.i21.3241",
    "10.1111/nmo.70133",
    "10.1111/nmo.70232",
    "canonicalTemporalStateEvidenceAtlas",
    "canonicalIBSTransitionParetoFrontier",
    "canonicalIBSTemporalPathBoundary",
    "canonicalIBSTransitionTriggerAtlas",
    "canonicalTransitionTriggerParetoFrontier",
    "trajectoryClusterDoesNotValidateAttractor",
    "flareRemissionDifferenceDoesNotProveHysteresis",
    "postInfectiousPersistenceDoesNotValidateAttractor",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS latent-transition mirror surface: " + ", ".join(missing))
print("IBS latent-transition mirror source surface: OK")
