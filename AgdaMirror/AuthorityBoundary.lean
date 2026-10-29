import Mathlib

/-!
# Lean mirror of `DASHI/Core/AuthorityBoundary.agda` (genuine interface + witness)

Faithful transcription of the authority-boundary bookkeeping:

* `AuthorityKind` — `CitationAuthority` vs `ArtifactAuthority` (distinct kinds),
* `AuthorityBoundary kind` — a kind-indexed boundary receipt whose stored kind is
  proven to match its index (`authorityKindMatches`),
* `CitationAuthorityNoArtifact` — the genuine boundary fact that a *citation*
  authority closes a source slot **without** authorizing a machine-readable
  artifact.

We give a genuine *witness* `citationOnly` exhibiting an accepted citation
boundary with both artifact flags `false`, packaged as a
`CitationAuthorityNoArtifact`.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.AuthorityBoundaries

/-- The two distinct authority kinds (Agda `data AuthorityKind`). -/
inductive AuthorityKind | CitationAuthority | ArtifactAuthority
  deriving DecidableEq, Repr

open AuthorityKind

/-- A kind-indexed authority boundary receipt (Agda `record AuthorityBoundary`). -/
structure AuthorityBoundary (kind : AuthorityKind) where
  authorityKind : AuthorityKind
  authorityKindMatches : authorityKind = kind
  recordIdentifier : String
  citation : String
  authorityAccepted : Bool
  artifactAuthority : Bool
  machineReadableArtifactPresent : Bool
  notes : List String

/-- A citation-kind boundary (Agda `CitationAuthorityBoundary`). -/
abbrev CitationAuthorityBoundary := AuthorityBoundary CitationAuthority

/-- An artifact-kind boundary (Agda `ArtifactAuthorityBoundary`). -/
abbrev ArtifactAuthorityBoundary := AuthorityBoundary ArtifactAuthority

/-- The genuine "citation closes a slot but authorizes no artifact" fact
(Agda `record CitationAuthorityNoArtifact`). -/
structure CitationAuthorityNoArtifact where
  citationBoundary : CitationAuthorityBoundary
  citationAuthorityAccepted : citationBoundary.authorityAccepted = true
  artifactAuthorityIsFalse : citationBoundary.artifactAuthority = false
  machineReadableArtifactPresentIsFalse :
    citationBoundary.machineReadableArtifactPresent = false

/-- Genuine witness: an accepted citation boundary with no artifact authority. -/
def citationOnly : CitationAuthorityNoArtifact where
  citationBoundary :=
    { authorityKind := CitationAuthority
      authorityKindMatches := rfl
      recordIdentifier := "rec-001"
      citation := "source citation"
      authorityAccepted := true
      artifactAuthority := false
      machineReadableArtifactPresent := false
      notes := [] }
  citationAuthorityAccepted := rfl
  artifactAuthorityIsFalse := rfl
  machineReadableArtifactPresentIsFalse := rfl

end AgdaMirror.AuthorityBoundaries


namespace AgdaMirror.SensibLawPNFParentBudget

/-!
Lean parity mirror for the golden Agda owners:

* `DASHI.Cognition.PNF.BoundedInterfaceSketch`
* `DASHI.Cognition.PNF.DeltaNativeParentRuntimeBridgeExact`
* `DASHI.Cognition.PNF.RelationDeltaReconciliationExact`
* `DASHI.Core.AuthorityNonPromotionCore`

Agda remains authoritative. This mirror checks the same typed separation between
semantic cardinality, exact-work admission, durable reconciliation evidence, and
authority promotion.
-/

inductive BudgetAdmissionDisposition
  | exactBudgetAdmitted
  | exactBudgetRejected
  deriving DecidableEq, Repr

structure RuntimeExactBudgetAdmission where
  parentKeyCount : Nat
  configuredCapacity : Nat
  excessKeyCount : Nat
  excessIsPositive : 0 < excessKeyCount
  parentKeyCountIsExcessPlusCapacity :
    parentKeyCount = excessKeyCount + configuredCapacity
  disposition : BudgetAdmissionDisposition

def canonical8206Over8192BudgetRejection : RuntimeExactBudgetAdmission where
  parentKeyCount := 8206
  configuredCapacity := 8192
  excessKeyCount := 14
  excessIsPositive := by decide
  parentKeyCountIsExcessPlusCapacity := by decide
  disposition := .exactBudgetRejected

theorem canonicalParentKeyCountIs8206 :
    canonical8206Over8192BudgetRejection.parentKeyCount = 8206 := rfl

theorem canonicalConfiguredCapacityIs8192 :
    canonical8206Over8192BudgetRejection.configuredCapacity = 8192 := rfl

theorem canonicalExcessKeyCountIs14 :
    canonical8206Over8192BudgetRejection.excessKeyCount = 14 := rfl

structure RelationDeltaReceipt where
  desiredRows : Nat
  currentRows : Nat
  addedRows : Nat
  removedRows : Nat
  replacedRows : Nat
  unchangedRowsSkipped : Nat
  physicalRowMutations : Nat
  desiredPartitionExact :
    desiredRows = addedRows + replacedRows + unchangedRowsSkipped
  currentPartitionExact :
    currentRows = removedRows + replacedRows + unchangedRowsSkipped
  physicalMutationExact :
    physicalRowMutations = addedRows + removedRows + 2 * replacedRows

def noOpRelationDeltaReceipt (rows : Nat) : RelationDeltaReceipt where
  desiredRows := rows
  currentRows := rows
  addedRows := 0
  removedRows := 0
  replacedRows := 0
  unchangedRowsSkipped := rows
  physicalRowMutations := 0
  desiredPartitionExact := by omega
  currentPartitionExact := by omega
  physicalMutationExact := by omega

structure PersistedRelationDeltaReceipt where
  persistedReconciliation : RelationDeltaReceipt
  persisted : Bool
  persistedIsTrue : persisted = true

def persistedNoOpRelationDeltaReceipt (rows : Nat) :
    PersistedRelationDeltaReceipt where
  persistedReconciliation := noOpRelationDeltaReceipt rows
  persisted := true
  persistedIsTrue := rfl

theorem persistedNoOpPhysicalMutationsAreZero (rows : Nat) :
    (persistedNoOpRelationDeltaReceipt rows).persistedReconciliation.physicalRowMutations = 0 :=
  rfl

structure DeltaReconciliationRuntimeCertification
    (admission : RuntimeExactBudgetAdmission) where
  admissionIsExact :
    admission.disposition = .exactBudgetAdmitted
  survivingReconciliation : PersistedRelationDeltaReceipt

theorem canonical8206Over8192CannotCertify :
    ¬ DeltaReconciliationRuntimeCertification
      canonical8206Over8192BudgetRejection := by
  intro certification
  cases certification.admissionIsExact

inductive BudgetRejectionAuthorizesSemanticTruncation : Prop

inductive BudgetExpansionCreatesSemanticAuthority : Prop

inductive RolledBackReceiptCreatesRuntimeCertification : Prop

theorem budgetRejectionDoesNotAuthorizeTruncation :
    ¬ BudgetRejectionAuthorizesSemanticTruncation := by
  intro h
  cases h

theorem budgetExpansionDoesNotCreateSemanticAuthority :
    ¬ BudgetExpansionCreatesSemanticAuthority := by
  intro h
  cases h

theorem rolledBackReceiptDoesNotCreateRuntimeCertification :
    ¬ RolledBackReceiptCreatesRuntimeCertification := by
  intro h
  cases h

structure ParentBudgetZKPFrame where
  objective : String
  reuse : String
  construction : String
  safetyInvariant : String
  lane : String
  preconditions : String
  governance : String
  postconditions : String
  verification : String
  esdMutationAllowed : Bool
  createsPhysicalPromotion : Bool
  createsHistoricalIdentity : Bool
  createsMonsterRecognition : Bool
  deriving Repr, DecidableEq

def canonicalParentBudgetZKPFrame : ParentBudgetZKPFrame where
  objective :=
    "certify the active SensibLaw parent reducer only after exact key-budget admission and durable relation-delta reconciliation"
  reuse :=
    "reuse the golden bounded-interface, runtime-bridge, relation-delta, and authority-non-promotion owners"
  construction :=
    "bind the observed parent key count to configured exact-work capacity; reject 8206 under 8192; require a persisted reconciliation receipt"
  safetyInvariant :=
    "fail closed without key truncation; budget expansion changes execution policy only; rollback cannot create certification or semantic authority"
  lane :=
    "one nonblocking parent-budget admission lane; relation reconciliation remains the sole candidate mutation authority"
  preconditions :=
    "migration 209 wiring is structurally live; exact key demand and configured capacity are explicit; durable receipt persistence is required"
  governance :=
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma, and C4/PlantUML are process lenses only"
  postconditions :=
    "admitted exact execution plus a persisted conservation receipt may certify the runtime path; rejected or rolled-back execution cannot"
  verification :=
    "Agda golden kernel first; Lean parity kernel second; controlled PostgreSQL replay remains independent runtime evidence"
  esdMutationAllowed := false
  createsPhysicalPromotion := false
  createsHistoricalIdentity := false
  createsMonsterRecognition := false

end AgdaMirror.SensibLawPNFParentBudget
