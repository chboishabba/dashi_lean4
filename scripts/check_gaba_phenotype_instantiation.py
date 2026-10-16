from pathlib import Path

p = Path("Dashi/Biology/GABAPhenotypeEvidenceInstantiationExact.lean")
assert p.exists(), "missing GABAPhenotypeEvidenceInstantiationExact.lean"
text = p.read_text(encoding="utf-8")

required = [
    "nguyen2024SynchronyAttachmentAssociation",
    "nguyen2024SynchronyAttachmentBridge",
    "crowley2016NeuroimmuneEvidence",
    "crowley2016NeuroimmuneBridge",
    "schur2016ADHDMetaReceipt",
    "puts2020ADHDStriatalReceipt",
    "harris2021ADHDSensorimotorReceipt",
    "cheng2026ADHDSerumReceipt",
    "canonicalADHDEvidenceHeterogeneityAtlas",
    "adhdEvidenceDoesNotPayGeneralLowGABA",
    "adhdEvidenceDoesNotPayInverseSeverityLaw",
    "canonicalGABAEvidenceInstantiationBoundary",
]
for needle in required:
    assert needle in text, f"missing required instantiation surface: {needle}"

for forbidden in [
    "theorem adhdGeneralLowGABA",
    "theorem higherGABAMeansLowerADHDSeverity",
    "theorem synchronyDefinesAttachment",
    "theorem neuroinflammationDefinesAutism",
]:
    assert forbidden not in text, f"forbidden promotion present: {forbidden}"

print("Lean GABA phenotype evidence-instantiation surface checks passed")
