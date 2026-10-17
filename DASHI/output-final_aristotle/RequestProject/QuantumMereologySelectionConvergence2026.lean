import RequestProject.QuantumMereologyFiniteSchwingerSelection

/-!
# Cross-objective subsystem-selection convergence

The live quantum-mereology lane already owns the Carroll--Singh-shaped
Schwinger search and finite-domain minimizer existence.  Surrounding work now
supplies genuinely different scientific selection ideas rather than aliases:

* Carroll--Singh (2021): quasiclassical/pointer robustness objective;
* Adil et al. (2026): search for factorisations admitting robust pointer states;
* Andreadakis--Dallas--Zanardi (2024): generalized TPS/operator-algebra
  emergence via long-time algebraic OTOC / minimal scrambling;
* Zanardi--Dallas--Andreadakis (2026): parameter-dependent g-TPS selection by
  a scrambling functional and an induced information-geometric susceptibility.

DASHI therefore does not define "preferred TPS" as one unqualified scalar.
This owner supplies a common comparison surface.  Agreement of two objectives
is proof data; sharing a candidate carrier or Hamiltonian does not manufacture
agreement, uniqueness, locality, geometry, or physical authority.
-/

namespace QuantumMereology
namespace SelectionConvergence2026

inductive ObjectiveKind where
  | carrollSinghSchwinger
  | robustPointerSearch
  | algebraScrambling
  | geometryReconstructionQuality
deriving Repr, DecidableEq

/-- One objective-specific minimization result on a declared common candidate
carrier.  The score and admissibility predicates remain objective-indexed. -/
structure ObjectiveSelection (Candidate : Type*) where
  objective : ObjectiveKind
  admissible : Candidate → Prop
  score : Candidate → ℝ
  selected : Candidate
  selectedAdmissible : admissible selected
  minimizes : ∀ other, admissible other → score selected ≤ score other

/-- Exact convergence of two distinct selection objectives.  `sameSelected` is
an explicit witness and is never inferred merely from sharing a Hamiltonian or
candidate family. -/
structure SelectionConvergence {Candidate : Type*}
    (left right : ObjectiveSelection Candidate) where
  distinctObjective : left.objective ≠ right.objective
  sameSelected : left.selected = right.selected

/-- Exact convergence implies every declared downstream consumer sees the same
selected candidate. -/
theorem converged_consumer_agreement
    {Candidate Answer : Type*}
    {left right : ObjectiveSelection Candidate}
    (W : SelectionConvergence left right)
    (consumer : Candidate → Answer) :
    consumer left.selected = consumer right.selected := by
  rw [W.sameSelected]

/-- Consumer-level convergence is strictly weaker data than same-candidate
convergence and is useful when two nonidentical minimizers are equivalent for a
specific downstream question. -/
structure ConsumerConvergence
    {Candidate Answer : Type*}
    (left right : ObjectiveSelection Candidate)
    (consumer : Candidate → Answer) where
  sameConsumerOutcome : consumer left.selected = consumer right.selected

/-- Strong convergence compiles to consumer convergence for every consumer. -/
def SelectionConvergence.toConsumerConvergence
    {Candidate Answer : Type*}
    {left right : ObjectiveSelection Candidate}
    (W : SelectionConvergence left right)
    (consumer : Candidate → Answer) :
    ConsumerConvergence left right consumer where
  sameConsumerOutcome := converged_consumer_agreement W consumer

/-- Parameter-dependent selection family used to state mereological-transition
experiments without importing the 2026 paper as theorem authority. -/
structure ParametricSelectionFamily (Parameter Candidate : Type*) where
  at : Parameter → ObjectiveSelection Candidate

/-- A local DASHI transition witness says the selected subsystem architecture
changes across two parameter values.  This is not automatically a thermodynamic
or Zanardi m-QPT claim. -/
structure SelectionChangeWitness
    {Parameter Candidate : Type*}
    (F : ParametricSelectionFamily Parameter Candidate) where
  left right : Parameter
  selectedChanges : (F.at left).selected ≠ (F.at right).selected

structure Boundary where
  crossObjectiveAgreementRequiresExplicitWitness : Bool := true
  sharedCandidateCarrierCreatesSamePreferredTPS : Bool := false
  sharedHamiltonianCreatesSamePreferredTPS : Bool := false
  finiteMinimizersCreateCrossObjectiveConvergence : Bool := false
  consumerConvergenceCreatesCandidateIdentity : Bool := false
  parametricSelectionChangeCreatesPhysicalPhaseTransition : Bool := false
  gTPSSourceCreatesCarrollSinghObjectiveEquivalence : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem cross_objective_agreement_requires_explicit_witness :
    canonicalBoundary.crossObjectiveAgreementRequiresExplicitWitness = true := rfl

theorem shared_candidate_carrier_does_not_create_same_preferred_tps :
    canonicalBoundary.sharedCandidateCarrierCreatesSamePreferredTPS = false := rfl

/-- 2024 external scientific source claim only. -/
def andreadakisDallasZanardi2024 : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi, Phys. Rev. A 109, 052424 (2024), DOI 10.1103/PhysRevA.109.052424"
  claim := "Studies the long-time algebraic OTOC relative to operator subalgebras/generalized TPSs and uses minimal long-time scrambling as a subsystem-emergence criterion. This source does not establish equality with the Carroll--Singh Schwinger objective on any DASHI carrier."

/-- 2026 external scientific source claim only. -/
def zanardiDallasAndreadakis2026 : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w"
  claim := "Introduces mereological quantum phase transitions using a variational family of operator algebras defining generalized TPSs, a parameter-dependent Hamiltonian and scrambling-functional minimization, with an induced information-geometric metric/algebra susceptibility. This citation does not create a DASHI operator-algebra implementation or a physical phase-transition theorem."

/-- Existing 2026 robust-pointer source is referenced independently rather than
collapsed into the scrambling objective. -/
def adilEtAl2026SelectionRole : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Arsalan Adil et al., Phys. Rev. D 113, 103535 (2026), DOI 10.1103/vj4x-96fk"
  claim := "Searches, for fixed Hamiltonians, for tensor-product structures admitting robust pointer states and reports multiple quasiclassical factorizations in studied settings. This does not create a universal DASHI nonuniqueness theorem or identify that search objective with Carroll--Singh or algebraic-OTOC minimization."

/-- New DASHI comparison theorem receipt. -/
def dashiSelectionConvergenceReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Provides a common proof-relevant surface for distinct subsystem-selection objectives. Exact cross-objective convergence requires an explicit same-selected-candidate witness; consumer-level convergence is separately typed and weaker; parameter-dependent selection change is not promoted to a physical phase transition."

end SelectionConvergence2026
end QuantumMereology
