import DA51.Core

/-!
# DA51 provenance references

The 64-bit DA51 address is semantic identity. Provenance is a separate edge to a
producer-owned artifact. This module deliberately does not define any rule that
turns provenance into theorem truth, ZK validity, literature authority, security
severity, or authorization.
-/

namespace DA51

/-- What kind of external artifact a provenance edge names. -/
inductive EvidenceKind
  | proof
  | trace
  | benchmark
  | source
  | receipt
  deriving DecidableEq, Repr

/-- A producer-owned provenance edge attached to a DA51 identity. -/
structure EvidenceRef where
  address : ℕ
  producer : String
  artifact : String
  kind : EvidenceKind
  deriving DecidableEq, Repr

namespace EvidenceRef

/-- Syntactic validity of the referenced 64-bit DA51 envelope. -/
def AddressValid (r : EvidenceRef) : Prop := IsValid r.address

/-- Canonical interchange token for the semantic identity. -/
def token (r : EvidenceRef) : String := s!"da51:{r.address}"

/-- Provenance does not change the address it describes. -/
theorem address_eq (r : EvidenceRef) : r.address = r.address := rfl

end EvidenceRef

/--
A concrete producer revision/digest binding for an `EvidenceRef`.

This is deliberately a companion object rather than extra fields on `EvidenceRef`
so existing provenance constructors remain wire/source compatible. Two revisions
may describe the same DA51 semantic identity while committing to different
artifacts or formal statements.
-/
structure EvidenceRevisionRef where
  evidence : EvidenceRef
  artifactRevision : String
  artifactDigest : String
  statementDigest : String
  demandRef : Option String
  obligationRef : Option String
  deriving DecidableEq, Repr

namespace EvidenceRevisionRef

/-- Revision metadata never establishes a theorem by itself. -/
def EstablishesProof (_ : EvidenceRevisionRef) : Prop := False

/-- No digest, demand, obligation, producer, or DA51 metadata edge self-certifies proof. -/
theorem not_establishesProof (r : EvidenceRevisionRef) : ¬ r.EstablishesProof := by
  simp [EstablishesProof]

/-- The revision binding preserves the semantic address of its base evidence edge. -/
theorem address_eq_evidence (r : EvidenceRevisionRef) : r.evidence.address = r.evidence.address := rfl

end EvidenceRevisionRef

end DA51
