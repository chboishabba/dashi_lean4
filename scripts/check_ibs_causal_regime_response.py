#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "Dashi/Biology/IBSCausalMaintenanceRegimeExact.lean",
    ROOT / "Dashi/Biology/IBSCausalMaintenanceRegimeRegression.lean",
    ROOT / "Dashi/Biology/IBSResponsePredictorAtlasExact.lean",
    ROOT / "Dashi/Biology/IBSResponsePredictorAtlasRegression.lean",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "canonicalCandidateMaintenanceRegimeAtlas",
    "canonicalRegimeDiscriminationPanel",
    "canonicalCausalMaintenanceParetoFrontier",
    "canonicalMaintenanceCausalEstimandObligation",
    "10.5056/jnm15067",
    "10.2196/98352",
    "10.1177/17562848261436121",
    "canonicalIBSResponsePredictorAtlas",
    "canonicalIBSResponsePredictionParetoFrontier",
    "10.1016/j.cgh.2026.04.014",
    "10.1186/s40168-021-01188-6",
    "10.1002/ueg2.70204",
    "10.7759/cureus.109142",
    "predictorDoesNotBecomeMediator",
    "internalPredictionDoesNotBecomeClinicalClassifier",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS causal-regime/response mirror surface: " + ", ".join(missing))
print("IBS causal-regime/response mirror source surface: OK")
