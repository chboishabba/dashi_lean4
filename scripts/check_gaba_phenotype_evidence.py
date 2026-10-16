from pathlib import Path
import re

p = Path("Dashi/Biology/GABAPhenotypeEvidenceExact.lean")
r = Path("Dashi/Biology/GABAPhenotypeEvidenceRegression.lean")
if not p.exists():
    raise RuntimeError("missing GABAPhenotypeEvidenceExact.lean")
if not r.exists():
    raise RuntimeError("missing GABAPhenotypeEvidenceRegression.lean")

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
    "00:00:00,000 --> 00:00:05,620",
    "00:01:26,960 --> 00:01:35,190",
]

for needle in required:
    if needle not in text:
        raise RuntimeError(f"missing required surface: {needle}")

# Keep each source's attribution metadata bound to its own declaration. Global
# string-presence checks can pass even when two source records exchange authors
# or DOIs.
source_records = {
    "schmitz2017Source": (
        "Taylor W. Schmitz; Marta M. Correia; Catarina S. Ferreira; Andrew P. Prescot; Michael C. Anderson",
        "10.1038/s41467-017-00956-z",
    ),
    "autismGABAMetaAnalysis2024Source": (
        "Alice R. Thomson; Duanghathai Pasanta; Tomoki Arichi; Nicolaas A. Puts",
        "10.1016/j.neubiorev.2024.105728",
    ),
    "puts2017Source": (
        "Nicolaas A. J. Puts; Ericka L. Wodka; Ashley D. Harris; Deana Crocetti; Mark Tommerdahl; Stewart H. Mostofsky; Richard A. E. Edden",
        "10.1002/aur.1691",
    ),
    "umesawa2020Source": (
        "Yumi Umesawa; Takeshi Atsumi; Mrinmoy Chakrabarty; Reiko Fukatsu; Masakazu Ide",
        "10.3389/fnins.2020.00482",
    ),
    "ptsdGABA2014Source": (
        "Isabelle M. Rosso; Melissa R. Weiner; David J. Crowley; Marisa M. Silveri; Scott L. Rauch; J. Eric Jensen",
        "10.1002/da.22155",
    ),
    "ptsdMRSReview2022Source": (
        "Kelley M. Swanberg; Leonardo Campos; Chadi G. Abdallah; Christoph Juchem",
        "10.1177/24705470221128004",
    ),
}

def declaration_block(name: str) -> str:
    match = re.search(
        rf"(?ms)^def\s+{re.escape(name)}\b.*?(?=^def\s+|^structure\s+|^inductive\s+|\Z)",
        text,
    )
    if not match:
        raise RuntimeError(f"missing source declaration: {name}")
    return match.group(0)

for name, metadata in source_records.items():
    block = declaration_block(name)
    for needle in metadata:
        if needle not in block:
            raise RuntimeError(f"{name} missing expected bound metadata: {needle}")

for needle in [
    "sourceAttributionNonAuthorityRegression",
    "associationCausalityGateRegression",
    "autismCausalSufficiencyGateRegression",
    "adhdCausalSufficiencyGateRegression",
    "sensoryUniversalizationGateRegression",
    "canonicalBoundaryRegression",
]:
    if needle not in regression:
        raise RuntimeError(f"missing regression proof: {needle}")

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
    if forbidden in text:
        raise RuntimeError(f"forbidden or stale promotion/attribution present: {forbidden}")

print("Lean GABA phenotype evidence attribution/promotion/regression surface checks passed")
