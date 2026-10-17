import RequestProject.QuantumMereologyFiniteHermitianCPO

/-!
# Pointer/objectivity comparison boundary (2026)

The finite CPO lane now constructs a mathematical eigenbasis of the selected
product observable once literal self-adjointness is supplied.  That is not yet
an empirical/objective pointer basis.

Chisholm--Palma--Innocenti (APS Open Science 1, 000024, 2026,
DOI 10.1103/75jr-ltct) study quantum Darwinism when the system Hamiltonian and
system-environment interaction do not commute.  Their source claim is retained
only as external scientific attribution: conventional pointer notions separate
in the noncommuting setting, while their spectrum-broadcast-structure (SBS)
notion agrees with the predictability-sieve notion in the commuting case.

This DASHI owner introduces proof-relevant comparison receipts.  It does not
turn the paper into a Lean theorem, does not identify the CPO spectral basis
with either physical criterion, and does not infer commutation from labels.
-/

namespace QuantumMereology
namespace PointerObjectivity2026

/-- The relation between system and interaction Hamiltonians is explicit proof
data rather than inferred from the existence of a preferred basis. -/
inductive HamiltonianRelation where
  | commuting
  | noncommuting
deriving Repr, DecidableEq

/-- Distinct pointer/objectivity criteria kept as separate coordinates. -/
inductive PointerCriterion where
  | selectedCPOSpectral
  | predictabilitySieve
  | spectrumBroadcastStructure
deriving Repr, DecidableEq

/-- A basis selected by one declared criterion.  `Basis` is deliberately
abstract: this carrier may be mathematical, operational or empirical depending
on the authority supplied by an application. -/
structure CriterionBasis (Basis : Type*) where
  criterion : PointerCriterion
  basis : Basis

/-- Same-object weld required before the mathematical selected-CPO basis can be
called the same pointer basis as the dynamical/objectivity criteria. -/
structure SameObjectPointerWeld (Basis : Type*) where
  cpo : CriterionBasis Basis
  predictability : CriterionBasis Basis
  sbs : CriterionBasis Basis
  cpoCriterion : cpo.criterion = .selectedCPOSpectral
  predictabilityCriterion : predictability.criterion = .predictabilitySieve
  sbsCriterion : sbs.criterion = .spectrumBroadcastStructure
  cpoEqPredictability : cpo.basis = predictability.basis
  predictabilityEqSBS : predictability.basis = sbs.basis

/-- With an explicit same-object weld, all three basis coordinates agree.  The
proof comes from the supplied equalities, not from the external citation. -/
theorem cpo_eq_sbs
    {Basis : Type*}
    (W : SameObjectPointerWeld Basis) :
    W.cpo.basis = W.sbs.basis :=
  W.cpoEqPredictability.trans W.predictabilityEqSBS

/-- A commuting-case source application still has to bind the paper's
predictability/SBS statement to one concrete model/basis. -/
structure CommutingCriterionApplication (Basis : Type*) where
  relation : HamiltonianRelation
  relationIsCommuting : relation = .commuting
  predictabilityBasis : Basis
  sbsBasis : Basis
  sourceBackedAgreement : predictabilityBasis = sbsBasis

/-- A noncommuting application records both candidates but deliberately carries
no automatic equality between them. -/
structure NoncommutingCriterionApplication (Basis : Type*) where
  relation : HamiltonianRelation
  relationIsNoncommuting : relation = .noncommuting
  predictabilityBasis : Basis
  sbsBasis : Basis

/-- If a noncommuting concrete model independently pays equality, DASHI may use
it; the equality remains application evidence rather than a consequence of the
noncommuting tag. -/
structure NoncommutingAgreementReceipt {Basis : Type*}
    (A : NoncommutingCriterionApplication Basis) where
  sameBasis : A.predictabilityBasis = A.sbsBasis

structure Boundary where
  commutingSourceReportsCriterionAgreement : Bool := true
  noncommutingSourceKeepsPointerNotionsDistinct : Bool := true
  mathematicalCPOEigenbasisCreatesPhysicalPointerBasis : Bool := false
  noncommutingDynamicsCreatesAutomaticPointerIdentification : Bool := false
  citationCreatesConcreteModelAgreementProof : Bool := false
  sbsObjectivityCreatesPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem commuting_source_reports_criterion_agreement :
    canonicalBoundary.commutingSourceReportsCriterionAgreement = true := rfl

theorem noncommuting_dynamics_does_not_create_automatic_pointer_identification :
    canonicalBoundary.noncommutingDynamicsCreatesAutomaticPointerIdentification = false := rfl

/-- External scientific source claim only. -/
def chisholmPalmaInnocenti2026 : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Diana A. Chisholm; G. Massimo Palma; Luca Innocenti, APS Open Science 1, 000024 (2026), DOI 10.1103/75jr-ltct"
  claim := "Studies quantum Darwinism/objectivity for noncommuting system and interaction Hamiltonians; reports that conventional pointer notions need not coincide there, and that an SBS-based pointer definition is natural in that setting and coincides with the predictability-sieve notion in the commuting case. This citation does not create a DASHI basis equality for any concrete model."

/-- DASHI structural theorem/receipt. -/
def dashiPointerComparisonReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Keeps selected-CPO spectral, predictability-sieve and SBS pointer criteria separately typed. A SameObjectPointerWeld requires literal basis equalities before the mathematical selected-CPO eigenbasis can be identified with a physical/objective pointer basis; noncommuting dynamics alone supplies no such equality."

end PointerObjectivity2026
end QuantumMereology
