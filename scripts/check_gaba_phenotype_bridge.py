from pathlib import Path

p = Path("Dashi/Biology/GABAPhenotypeBridgeExact.lean")
if not p.exists():
    raise RuntimeError("missing GABAPhenotypeBridgeExact.lean")
text = p.read_text(encoding="utf-8")

required = [
    "structure PromotionValidation",
    "structure RegionalToWholeBrainBridge",
    "structure GroupToIndividualBridge",
    "structure AssociationToCausalBridge",
    "structure SynchronyAttachmentBridge",
    "structure NeurochemicalInflammationBridge",
    "validationSourceMatchesEvidence",
    "structure AssociationEstimandScopeWitness",
    "estimandScopeMatchesAssociation",
    "inductive EvidenceFamily",
    "structure SensoryGABAInteractionCarrier",
    "structure GABARetrievalMemoryBridge",
    "structure ADHDEvidenceGap",
    "causalPromotionEstimandReference",
    "sameGABAEvidenceDifferentContextCanChangeLoad",
    "schmitzEvidenceDoesNotByItselfChangeMemory",
]
for needle in required:
    if needle not in text:
        raise RuntimeError(f"missing bridge surface: {needle}")

for forbidden in [
    "theorem autismCausedByLowGABA",
    "theorem adhdCausedByLowGABA",
    "theorem synchronyMeansInsecureAttachment",
    "theorem gabaCausesNeuroinflammation",
]:
    if forbidden in text:
        raise RuntimeError(f"forbidden promotion present: {forbidden}")

print("Lean GABA phenotype bridge surface checks passed")
