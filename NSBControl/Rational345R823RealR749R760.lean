import Mathlib.Tactic
import NSBControl.Rational345R823RealNestedOrbit
import NSBControl.Rational345R823RealProductionDifference
import NSBControl.Rational345R823LiteralR760CellMaxCut

/-!
# Literal real R749 -> R760 carrier and R823 decision

This file finishes the finite same-object chain at cutoff four.

* R700 is represented by a literal outer row on the common finite triad
  address and its p/q energy-leg orbit.
* R748 supplies the paired two-difference production cell.
* R749 is exactly `3 * nestedOrbitCell - pairedTwoDifferenceCell`.
* R760 is exactly the p/q swap pair of that R749 cell.

The complete R760 fold is then identified with the already-normalized
`selectedNonlinear` on physical states and packaged as the concrete literal
carrier consumed by the real R823/R830/R831 decision compiler.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823RealR749R760

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823RealHelicalCore
open Rational345R823RealInnerFold
open Rational345R823RealNestedCell
open Rational345R823RealNestedOrbit
open Rational345R823RealProductionIncidence
open Rational345R823RealProductionDifference
open Rational345R823TouchedNormalForm
open Rational345R823LiteralR760CellMaxCut

classical

/-- One unambiguous name for the common `(output,(p,q))` carrier. -/
abbrev Incidence := Rational345R823RealProductionDifference.R760Incidence

/-- R694 spectator row for one outer physical triad incidence.  The finite
carrier is the full radius-four cube with non-resonant/zero-output incidences
zero-masked; this is an exact extension of the physical enumeration by zero
cells and preserves every active multiplicity. -/
def realNestedOuterRow (u : State) (β : Incidence) : ℝ :=
  if isZeroMode (incK β) then 0
  else if Resonates (incP β) (incQ β) (incK β) then
    coherentWork
      (fixedOutputMixed u (incK β))
      (realNestedCell u (incP β) (incQ β))
  else 0

/-- Literal R700 three-energy-leg nested orbit cell. -/
def realNestedOrbitCell (u : State) (β : Incidence) : ℝ :=
  realNestedOuterRow u β +
    realNestedOuterRow u (pEnergyLeg β) +
    realNestedOuterRow u (qEnergyLeg β)

/-- Complete literal R700 cell fold. -/
def realNestedOrbitCellCompleteFold (u : State) : ℝ :=
  ∑ β : Incidence, realNestedOrbitCell u β

/-- Coherent work commutes with a finite sum in the right vector slot. -/
theorem coherentWork_sum_right
    {ι : Type*} [Fintype ι] (left : Vec3) (f : ι → Vec3) :
    coherentWork left (∑ i, f i) = ∑ i, coherentWork left (f i) := by
  change
    2 * pairingRealLinear left (∑ i, f i) =
      ∑ i, 2 * pairingRealLinear left (f i)
  rw [map_sum, Finset.mul_sum]

/-- The complete R694 outer-row fold is exactly the already-defined global
nested pair fold. -/
theorem realNestedOuterRowCompleteFold_eq_globalPairFold
    (u : State) :
    (∑ β : Incidence, realNestedOuterRow u β) =
      realNestedGlobalPairFold u := by
  simp only [Incidence, Rational345R823RealProductionDifference.R760Incidence,
    Fintype.sum_prod_type]
  unfold realNestedOuterRow incK incP incQ
    realNestedGlobalPairFold realNestedOutputWork
  apply Finset.sum_congr rfl
  intro k hkMem
  by_cases hk : isZeroMode k
  · simp [hk]
  · simp only [hk, if_false]
    unfold fixedOutputNested
    rw [coherentWork_sum_right]
    apply Finset.sum_congr rfl
    intro p hpMem
    rw [coherentWork_sum_right]
    apply Finset.sum_congr rfl
    intro q hqMem
    by_cases hres : Resonates p q k
    · simp [hres]
    · simp [hres, coherentWork]

/-- The p-energy-leg contribution is a pure permutation of the complete outer
carrier. -/
theorem sum_realNestedOuterRow_pEnergyLeg (u : State) :
    (∑ β : Incidence, realNestedOuterRow u (pEnergyLeg β)) =
      ∑ β : Incidence, realNestedOuterRow u β :=
  Equiv.sum_comp pEnergyLegEquiv (realNestedOuterRow u)

/-- The q-energy-leg contribution is likewise a complete-carrier permutation. -/
theorem sum_realNestedOuterRow_qEnergyLeg (u : State) :
    (∑ β : Incidence, realNestedOuterRow u (qEnergyLeg β)) =
      ∑ β : Incidence, realNestedOuterRow u β :=
  Equiv.sum_comp qEnergyLegEquiv (realNestedOuterRow u)

/-- Cellwise R700 and the previously exposed complete-fold R700 owner are the
same object after exact finite summation. -/
theorem realNestedOrbitCellCompleteFold_eq_completeFold
    (u : State) :
    realNestedOrbitCellCompleteFold u = realNestedOrbitCompleteFold u := by
  unfold realNestedOrbitCellCompleteFold realNestedOrbitCell
  simp_rw [Finset.sum_add_distrib]
  rw [sum_realNestedOuterRow_pEnergyLeg u,
      sum_realNestedOuterRow_qEnergyLeg u,
      realNestedOuterRowCompleteFold_eq_globalPairFold u]
  rfl

/-- Literal cellwise R700 theorem. -/
theorem realNestedOrbitCellCompleteFold_eq_twelveCoherent
    (u : State) (hu : IsR823PhysicalState u) :
    realNestedOrbitCellCompleteFold u = 12 * globalCoherentWork u := by
  rw [realNestedOrbitCellCompleteFold_eq_completeFold]
  exact realNestedOrbitCompleteFold_eq_twelveCoherent u hu

/-- Exact real R749 local difference-aligned cell. -/
def r749DifferenceAlignedCell (u : State) (β : Incidence) : ℝ :=
  3 * realNestedOrbitCell u β - pairedTwoDifferenceCell u β

/-- Complete real R749 fold. -/
def r749DifferenceAlignedCompleteFold (u : State) : ℝ :=
  ∑ β : Incidence, r749DifferenceAlignedCell u β

/-- D2: literal R749 finite summation gives exactly the scalar R749 normal
form, with no estimate. -/
theorem r749DifferenceAlignedCompleteFold_eq_total
    (u : State) (hu : IsR823PhysicalState u) :
    r749DifferenceAlignedCompleteFold u = r749DifferenceAlignedTotal u := by
  unfold r749DifferenceAlignedCompleteFold r749DifferenceAlignedCell
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [realNestedOrbitCellCompleteFold_eq_twelveCoherent u hu,
      pairedTwoDifferenceCompleteFold_eq_threeProduction u hu]
  unfold r749DifferenceAlignedTotal r745OrbitAlignedNonlinear
  ring

/-- Literal R760 p/q swap-paired residual cell. -/
def r760SwapPairedResidualCell (u : State) (β : Incidence) : ℝ :=
  r749DifferenceAlignedCell u β +
    r749DifferenceAlignedCell u (swapIncidence β)

/-- Complete literal R760 cell fold. -/
def r760SwapPairedResidualCompleteFold (u : State) : ℝ :=
  ∑ β : Incidence, r760SwapPairedResidualCell u β

/-- D3: swap pairing doubles the complete R749 fold because swap is a
permutation of the complete original-multiplicity carrier. -/
theorem r760SwapPairedResidualCompleteFold_eq_twiceR749
    (u : State) :
    r760SwapPairedResidualCompleteFold u =
      2 * r749DifferenceAlignedCompleteFold u := by
  unfold r760SwapPairedResidualCompleteFold r760SwapPairedResidualCell
  rw [Finset.sum_add_distrib]
  have hswap :
      (∑ β : Incidence, r749DifferenceAlignedCell u (swapIncidence β)) =
        ∑ β : Incidence, r749DifferenceAlignedCell u β :=
    Equiv.sum_comp swapEquiv (r749DifferenceAlignedCell u)
  rw [hswap]
  ring

/-- D4: the complete literal R760 fold is the public nonlinear selected rate
on the real physical carrier. -/
theorem r760SwapPairedResidualCompleteFold_eq_selectedNonlinear
    (u : State) (hu : IsR823PhysicalState u) :
    r760SwapPairedResidualCompleteFold u = selectedNonlinear u := by
  rw [r760SwapPairedResidualCompleteFold_eq_twiceR749]
  rw [r749DifferenceAlignedCompleteFold_eq_total u hu]
  exact r760SwapPairedResidualTotal_eq_selectedNonlinear u

/-- The literal R760 complete fold is continuous.  Every mode/index branch is
static and every state-dependent operation is finite polynomial/linear. -/
theorem r760SwapPairedResidualCompleteFold_continuous :
    Continuous r760SwapPairedResidualCompleteFold := by
  unfold r760SwapPairedResidualCompleteFold r760SwapPairedResidualCell
    r749DifferenceAlignedCell realNestedOrbitCell realNestedOuterRow
    pairedTwoDifferenceCell pairedWeightedCell orderedPairPower
    selectedDyadicWeight realNestedCell realNestedHalfCell realFourSignForcing
    fourSignInnerFold fourSignInnerTerm fourSignInner multiplierDifferenceVector
    helicalComponent fixedOutputMixed mixedCell coherentWork hermitianDot
    criticalWeight orderedPower pairingRealLinear
  fun_prop

/-- Concrete one-leaf carrier required by the R823 terminal max-cut. -/
def literalR760CellCarrier : LiteralR760CellCarrier where
  cell := fun u β => r760SwapPairedResidualCell u β
  completeFold_continuous := by
    change Continuous r760SwapPairedResidualCompleteFold
    exact r760SwapPairedResidualCompleteFold_continuous
  completeFold_sameObject := by
    intro u hu
    calc
      (∑ β : Rational345R823LiteralR760CellMaxCut.R760Incidence,
          r760SwapPairedResidualCell u β) = selectedNonlinear u :=
        r760SwapPairedResidualCompleteFold_eq_selectedNonlinear u hu
      _ = r760SwapPairedResidualTotal u :=
        (r760SwapPairedResidualTotal_eq_selectedNonlinear u).symm

/-- The literal real D1-D4 chain reaches the already-written R823/R830/R831
contradiction compiler. -/
theorem literalR760DecisionContradiction :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_literalR760Cell literalR760CellCarrier

/-- Source-level max-cut flags.  Kernel certification is tracked separately. -/
def r823RealR700CellwiseCarrierClosed : Bool := true
def r823RealR749AssemblyClosed : Bool := true
def r823RealR760SwapPairClosed : Bool := true
def r823RealR760CompleteFoldSameObjectClosed : Bool := true
def r823DecisionSourceChainClosed : Bool := true

end Rational345R823RealR749R760
end NSBControl
