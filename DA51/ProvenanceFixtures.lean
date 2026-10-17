import DA51.Provenance

namespace DA51.ProvenanceFixtures

private def base : EvidenceRef :=
  { address := 0xDA51831100800000
    producer := "lean-kernel"
    artifact := "artifact:smith-proof:1"
    kind := .proof }

private def revisionA : EvidenceRevisionRef :=
  { evidence := base
    artifactRevision := "lean:head-a"
    artifactDigest := "sha256:artifact-a"
    statementDigest := "sha256:statement-a"
    demandRef := some "formal-demand:smith:1"
    obligationRef := some "proof-obligation:smith:1" }

private def revisionB : EvidenceRevisionRef :=
  { evidence := base
    artifactRevision := "lean:head-b"
    artifactDigest := "sha256:artifact-b"
    statementDigest := "sha256:statement-b"
    demandRef := some "formal-demand:smith:1"
    obligationRef := some "proof-obligation:smith:1" }

example : revisionA.evidence.address = revisionB.evidence.address := rfl
example : revisionA.statementDigest ≠ revisionB.statementDigest := by decide
example : ¬ revisionA.EstablishesProof := by simp [EvidenceRevisionRef.EstablishesProof]
example : ¬ revisionB.EstablishesProof := by simp [EvidenceRevisionRef.EstablishesProof]

end DA51.ProvenanceFixtures
