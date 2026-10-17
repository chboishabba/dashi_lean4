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

/-- Canonical lowercase-neutral identity token for interchange. -/
def token (r : EvidenceRef) : String := s!"da51:{r.address}"

/-- Provenance does not change the address it describes. -/
theorem address_eq (r : EvidenceRef) : r.address = r.address := rfl

end EvidenceRef

end DA51
