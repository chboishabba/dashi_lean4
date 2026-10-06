from pathlib import Path

p = Path("Dashi/Biology/GABAPhenotypeEvidenceExact.lean")
r = Path("Dashi/Biology/GABAPhenotypeEvidenceRegression.lean")
assert p.exists(), "missing GABAPhenotypeEvidenceExact.lean"
assert r.exists(), "missing GABAPhenotypeEvidenceRegression.lean"

text = p.read_text(encoding="utf-8")
regression = r.read_text(encoding="utf-8")

required = [
    "structure AttributedSource",
    "citationImportsProof : Bool",
    "citationCreatesAuthority : Bool",
    "structure RegionalGABAEvidence",
    "associationDoesNotImplyCausalSufficiency",
    "regionalGABADifferenceDoesNotImplyWholeBrainDifference",
    "groupMeanDoesNotClassifyIndividual",
    "diagnosisDoesNotDetermineGABALevel",
    "thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression",
    "noAttachmentBridgeFromSynchronyWithoutReceipt",
    "noNeuroinflammationBridgeFromGABAWithoutReceipt",
    "sensoryAssociationDoesNotUniversalizeAutism",
    "schmitz2017ThoughtSuppression",
    "autismGABAMetaAnalysis2024",
    "puts2017SensorimotorGABA",
    "umesawa2020SensoryHyperResponsiveness",
    "ptsdAnteriorInsulaGABA2014",
    "ptsdMRSReview2022",
    "Taylor W. Schmitz; Marta M. Correia; Catarina S. Ferreira; Andrew P. Prescot; Michael C. Anderson",
    "Alice R. Thomson; Duanghathai Pasanta; Tomoki Arichi; Nicolaas A. Puts",
    "Nicolaas A. J. Puts; Ericka L. Wodka; Ashley D. Harris; Deana Crocetti; Mark Tommerdahl; Stewart H. Mostofsky; Richard A. E. Edden",
    "Yumi Umesawa; Takeshi Atsumi; Mrinmoy Chakrabarty; Reiko Fukatsu; Masakazu Ide",
    "Isabelle M. Rosso; Melissa R. Weiner; David J. Crowley; Marisa M. Silveri; Scott L. Rauch; J. Eric Jensen",
    "Kelley M. Swanberg; Leonardo Campos; Chadi G. Abdallah; Christoph Juchem",
    "10.1016/j.neubiorev.2024.105728",
    "10.1002/aur.1691",
    "10.3389/fnins.2020.00482",
    "10.1002/da.22155",
    "10.1177/24705470221128004",
    "00:00:00,000 --> 00:00:05,620",
    "00:01:26,960 --> 00:01:35,190",
]

for needle in required:
    assert needle in text, f"missing required surface: {needle}"

for needle in [
    "sourceAttributionNonAuthorityRegression",
    "associationCausalityGateRegression",
    "autismCausalSufficiencyGateRegression",
    "adhdCausalSufficiencyGateRegression",
    "sensoryUniversalizationGateRegression",
    "canonicalBoundaryRegression",
]:
    assert needle in regression, f"missing regression proof: {needle}"

for forbidden in [
    "structure LiteratureSource",
    "systematic-review / meta-analysis source registry row",
    "PTSD magnetic-resonance-spectroscopy study source registry row",
    "systematic-review source registry row",
    "Thomas W. Schmitz; Michael C. Correia",
    "theorem autismCausedByLowGABA",
    "theorem adhdCausedByLowGABA",
    "theorem insecureAttachmentByDefinition",
]:
    assert forbidden not in text, f"forbidden or stale promotion/attribution present: {forbidden}"

print("Lean GABA phenotype evidence attribution/promotion/regression surface checks passed")
