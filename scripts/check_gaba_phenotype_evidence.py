from pathlib import Path

p = Path("Dashi/Biology/GABAPhenotypeEvidenceExact.lean")
assert p.exists(), "missing GABAPhenotypeEvidenceExact.lean"

text = p.read_text(encoding="utf-8")

required = [
    "structure RegionalGABAEvidence",
    "associationDoesNotImplyCausalSufficiency",
    "regionalGABADifferenceDoesNotImplyWholeBrainDifference",
    "groupMeanDoesNotClassifyIndividual",
    "diagnosisDoesNotDetermineGABALevel",
    "thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression",
    "noAttachmentBridgeFromSynchronyWithoutReceipt",
    "noNeuroinflammationBridgeFromGABAWithoutReceipt",
    "schmitz2017ThoughtSuppression",
    "autismGABAMetaAnalysis2024",
]

for needle in required:
    assert needle in text, f"missing required surface: {needle}"

for forbidden in [
    "theorem autismCausedByLowGABA",
    "theorem adhdCausedByLowGABA",
    "theorem insecureAttachmentByDefinition",
]:
    assert forbidden not in text, f"forbidden causal promotion present: {forbidden}"

print("Lean GABA phenotype evidence surface checks passed")
