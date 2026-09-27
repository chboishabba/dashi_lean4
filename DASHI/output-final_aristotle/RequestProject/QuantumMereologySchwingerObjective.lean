import RequestProject.QuantumMereologySelection
import Mathlib.Data.Fintype.BigOperators

/-!
# Source-exact Carroll--Singh Schwinger objective

External source:
Sean M. Carroll and Ashmeet Singh, Phys. Rev. A 103, 022213 (2021),
DOI 10.1103/PhysRevA.103.022213.

The paper defines:
* linear entropy: S_lin(ρ) = 1 - Tr(ρ²);
* pointer entropy: S_pointer(p) = 1 - Σ_j p_j²;
* robustness/predictability penalties from the second time derivatives at t=0;
* Schwinger penalty for an initial candidate-pointer state as
    max(S̈_lin(0), S̈_pointer(0));
* the factorisation score by averaging that quantity over the d_A candidate
  pointer eigenstate initialisations, then minimizing over factorizations.

This module reconstructs those formulae and the selection grammar. It does NOT
manufacture reduced density matrices, partial traces, time derivatives,
candidate pointer observables, or a proof that a physical minimizer exists or
is unique.
-/

namespace QuantumMereology

open scoped BigOperators

namespace SchwingerObjective

/-- Carroll--Singh linear entropy written as a function of the reduced-state
purity Tr(ρ²). The trace/purity producer is intentionally upstream. -/
def linearEntropyFromPurity (purity : ℝ) : ℝ :=
  1 - purity

/-- Carroll--Singh pointer entropy for a finite pointer-basis probability
distribution. Normalisation/nonnegativity are producer obligations. -/
def pointerEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  1 - ∑ i, (p i) ^ 2

/-- Source-defined second-derivative penalty for one candidate-pointer
initialisation. -/
def penalty (linearEntropyAcceleration pointerEntropyAcceleration : ℝ) : ℝ :=
  max linearEntropyAcceleration pointerEntropyAcceleration

/-- Average the source-defined penalty over a fixed finite family of candidate
pointer eigenstate initialisations. Carroll--Singh fix the subsystem dimensions
while sifting through factorizations. -/
noncomputable def averagePenalty
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (linearEntropyAcceleration pointerEntropyAcceleration : ι → ℝ) : ℝ :=
  (∑ i, penalty (linearEntropyAcceleration i) (pointerEntropyAcceleration i)) /
    (Fintype.card ι : ℝ)

theorem penalty_ge_linear (x y : ℝ) :
    x ≤ penalty x y :=
  le_max_left _ _

theorem penalty_ge_pointer (x y : ℝ) :
    y ≤ penalty x y :=
  le_max_right _ _

/-- Upstream producer obligations for the two source-defined second derivatives.
These fields are intentionally theorem inputs until reduced-state/time-
derivative machinery exists in the repo. -/
structure EntropyAccelerationProducer
    (Candidate PointerInit : Type*) where
  linearEntropyAcceleration : Candidate → PointerInit → ℝ
  pointerEntropyAcceleration : Candidate → PointerInit → ℝ

/-- A source-faithful finite-factorisation search surface with fixed subsystem
dimensions / pointer-initialisation index. -/
structure SearchData
    (W : BareQuantumWorld)
    (PointerInit : Type*)
    [Fintype PointerInit] [Nonempty PointerInit] where
  Candidate : Type
  realizes : Candidate → TensorProductStructure W
  Admissible : Candidate → Prop
  accelerations : EntropyAccelerationProducer Candidate PointerInit

namespace SearchData

variable
  {W : BareQuantumWorld}
  {PointerInit : Type*}
  [Fintype PointerInit] [Nonempty PointerInit]

noncomputable def score
    (D : SearchData W PointerInit)
    (candidate : D.Candidate) : ℝ :=
  averagePenalty
    (D.accelerations.linearEntropyAcceleration candidate)
    (D.accelerations.pointerEntropyAcceleration candidate)

/-- Exact embedding of the source objective into the generic preferred-TPS
selection interface. Each objective coordinate remains the full pointer-state
family; comparison uses the averaged pointwise max required by the source. -/
noncomputable def selectionProblem
    (D : SearchData W PointerInit) :
    PreferredTPSSelectionProblem W where
  Candidate := D.Candidate
  realizes := D.realizes
  Admissible := D.Admissible
  EntanglementGrowthScore := PointerInit → ℝ
  InternalSpreadingScore := PointerInit → ℝ
  entanglementGrowth :=
    D.accelerations.linearEntropyAcceleration
  internalSpreading :=
    D.accelerations.pointerEntropyAcceleration
  NoWorse := fun left right => D.score left ≤ D.score right

/-- The generic combined-objective interface is realized exactly by the
source-defined averaged Schwinger penalty. -/
noncomputable def objectiveRealization
    (D : SearchData W PointerInit) :
    CarrollSinghObjectiveRealization D.selectionProblem where
  CombinedObjective := ℝ
  combine := fun linear pointer =>
    averagePenalty linear pointer
  ObjectiveNoWorse := (· ≤ ·)
  noWorseToCombined := by
    intro left right h
    exact h
  combinedToNoWorse := by
    intro left right h
    exact h

theorem selected_minimizes_schwinger_score
    (D : SearchData W PointerInit)
    (receipt : PreferredTPSSelectionReceipt D.selectionProblem)
    (other : D.Candidate)
    (hOther : D.Admissible other) :
    D.score receipt.selected ≤ D.score other :=
  receipt.selectedOptimal.2 other hOther

end SearchData

structure ProducerBoundary where
  entropyFormulaCreatesReducedDensityMatrix : Bool := false
  entropyFormulaCreatesPartialTrace : Bool := false
  entropyFormulaCreatesTimeDerivative : Bool := false
  entropyFormulaCreatesCandidatePointerObservable : Bool := false
  sourceAlgorithmProvesMinimizerExists : Bool := false
  sourceAlgorithmProvesMinimizerUnique : Bool := false
deriving Repr, DecidableEq

def canonicalProducerBoundary : ProducerBoundary := {}

theorem formula_does_not_create_reduced_state :
    canonicalProducerBoundary.entropyFormulaCreatesReducedDensityMatrix = false := rfl

theorem source_algorithm_does_not_become_local_existence_theorem :
    canonicalProducerBoundary.sourceAlgorithmProvesMinimizerExists = false := rfl

end SchwingerObjective

def carrollSinghSchwingerFormulaClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
  claim := "Defines linear entropy 1-Tr(ρ_A²), pointer entropy 1-Σ p_j², uses their second derivatives at t=0, combines them pointwise by max as Schwinger entropy, averages over candidate-pointer eigenstate initialisations, and minimizes across fixed-dimension factorizations."

def dashiSchwingerObjectiveReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Reconstructs the source Schwinger objective and embeds it in PreferredTPSSelectionProblem while keeping reduced-state, derivative, CPO, existence, uniqueness, and physical-authority payments explicit."

end QuantumMereology
