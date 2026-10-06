from pathlib import Path

p = Path("Dashi/Biology/GABAPhenotypeBridgeExact.lean")
assert p.exists(), "missing GABAPhenotypeBridgeExact.lean"
text = p.read_text(encoding="utf-8")

required = [
    "structure PromotionValidation",
    "structure RegionalToWholeBrainBridge",
    "structure GroupToIndividualBridge",
    "structure AssociationToCausalBridge",
    "structure SynchronyAttachmentBridge",
    "structure NeurochemicalInflammationBridge",
    "inductive EvidenceFamily",
    "structure SensoryGABAInteractionCarrier",
    "structure GABARetrievalMemoryBridge",
    "structure ADHDEvidenceGap",
    "causalPromotionRequiresExistingEstimand",
    "sameGABAEvidenceDifferentContextCanChangeLoad",
    "schmitzEvidenceDoesNotByItselfChangeMemory",
]
for needle in required:
    assert needle in text, f"missing bridge surface: {needle}"

for forbidden in [
    "theorem autismCausedByLowGABA",
    "theorem adhdCausedByLowGABA",
    "theorem synchronyMeansInsecureAttachment",
    "theorem gabaCausesNeuroinflammation",
]:
    assert forbidden not in text, f"forbidden promotion present: {forbidden}"

print("Lean GABA phenotype bridge surface checks passed")
