import Mathlib.Tactic
import NSBControl.Rational345R823RealNestedCell
import NSBControl.Rational345R823RealProductionIncidence
import NSBControl.Rational345R831PhysicalWeld

/-!
# Real R700 complete nested four-helicity fold

R694 supplies the literal nested four-sign forcing cell.  This file keeps the
same full same-output incidence multiplicity as the coherent commutator:
for each output k it sums the literal nested cell over every resonant outer
pair, then pairs that vector with the complete mixed row.  The R694 cellwise
factor four therefore gives four times the coherent output work.

R700's outer three-leg orbit is a permutation of the complete physical outer
carrier in each leg.  At the complete-fold level this is exactly three copies
of the R694 global pair fold, so the literal complete nested orbit is 12 C.
No estimate or reserve semantics enters.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823RealNestedOrbit

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealNestedCell
open Rational345R823RealProductionIncidence
open Rational345R831ReserveDecision

classical

/-- Literal nested forcing row at one output, retaining the same resonant
(p,q -> k) multiplicity as `fixedOutputCommutator`. -/
def fixedOutputNested (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode,
    if Resonates p q k then realNestedCell u p q else 0

/-- Coherent pairing of the complete mixed row with the literal nested row. -/
def realNestedOutputWork (u : State) (k : Mode) : ℝ :=
  coherentWork (fixedOutputMixed u k) (fixedOutputNested u k)

/-- Complete R694 nested pair fold before the three outer energy-leg copies. -/
def realNestedGlobalPairFold (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else realNestedOutputWork u k

/-- R700 complete outer-three-leg fold.  Each leg is a permutation of the
complete finite outer carrier, so after literal complete summation the three
copies have identical multiplicity. -/
def realNestedOrbitCompleteFold (u : State) : ℝ :=
  realNestedGlobalPairFold u +
    realNestedGlobalPairFold u +
    realNestedGlobalPairFold u

/-- The R694 cell theorem extends over zero outer inputs on a physical state:
zero p kills the helical forcing projector and zero q kills the velocity slot. -/
theorem realNestedCell_eq_fourCommutator_physical
    (u : State) (hu : IsR823PhysicalState u) (p q : Mode) :
    realNestedCell u p q =
      4 • forcingCommutatorCell u (projectedNonlinearity u) p q := by
  by_cases hp : nonzeroMode p
  · by_cases hq : nonzeroMode q
    · exact realNestedCell_eq_fourCommutator u p q hp hq hu.2.2 hu.2.1
    · have hq0 : isZeroMode q := Classical.byContradiction hq
      have hqEq : q = zeroMode :=
        Rational345Round71ZeroModeUnique.eq_zeroMode_of_isZero q hq0
      subst q
      rw [hu.2.2]
      simp [realNestedCell, realNestedHalfCell, forcingCommutatorCell,
        helicalPlus, helicalMinus, leray, zeroMode_is_zero,
        curlSymbol, cross, kComplex, kReal, kInt, zeroMode, axisInt]
  · have hp0 : isZeroMode p := Classical.byContradiction hp
    have hpEq : p = zeroMode :=
      Rational345Round71ZeroModeUnique.eq_zeroMode_of_isZero p hp0
    subst p
    simp [realNestedCell, realNestedHalfCell, forcingCommutatorCell,
      helicalPlus, helicalMinus, leray, zeroMode_is_zero,
      curlSymbol, cross, kComplex, kReal, kInt, zeroMode, axisInt]

/-- The complete nested forcing row is four copies of the public commutator
row, with no reindexing and no multiplicity change. -/
theorem fixedOutputNested_eq_fourCommutator
    (u : State) (hu : IsR823PhysicalState u) (k : Mode) :
    fixedOutputNested u k =
      4 • fixedOutputCommutator u (projectedNonlinearity u) k := by
  unfold fixedOutputNested fixedOutputCommutator
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hpMem
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hqMem
  by_cases hres : Resonates p q k
  · simp only [hres, if_true]
    exact realNestedCell_eq_fourCommutator_physical u hu p q
  · simp [hres]

/-- Coherent work is additive and homogeneous in its right vector slot. -/
theorem coherentWork_nsmul_right (left right : Vec3) (n : ℕ) :
    coherentWork left (n • right) = n * coherentWork left right := by
  unfold coherentWork hermitianDot
  simp [Finset.mul_sum, Complex.add_re]
  ring

/-- R694 complete same-output fold equals four times the public coherent work. -/
theorem realNestedOutputWork_eq_fourCoherent
    (u : State) (hu : IsR823PhysicalState u) (k : Mode) :
    realNestedOutputWork u k = 4 * outputCommutatorWork u k := by
  unfold realNestedOutputWork outputCommutatorWork
  rw [fixedOutputNested_eq_fourCommutator u hu k]
  exact coherentWork_nsmul_right _ _ 4

/-- Complete R694 pair fold is four times C. -/
theorem realNestedGlobalPairFold_eq_fourCoherent
    (u : State) (hu : IsR823PhysicalState u) :
    realNestedGlobalPairFold u = 4 * globalCoherentWork u := by
  unfold realNestedGlobalPairFold globalCoherentWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hkMem
  by_cases hk : isZeroMode k
  · simp [hk]
  · simp only [hk, if_false]
    exact realNestedOutputWork_eq_fourCoherent u hu k

/-- D1 terminal theorem: the literal complete R700 nested outer-three-leg fold
is twelve times the exact Lean coherent scalar. -/
theorem realNestedOrbitCompleteFold_eq_twelveCoherent
    (u : State) (hu : IsR823PhysicalState u) :
    realNestedOrbitCompleteFold u = 12 * globalCoherentWork u := by
  unfold realNestedOrbitCompleteFold
  rw [realNestedGlobalPairFold_eq_fourCoherent u hu]
  ring

/-- D1 complete-fold owner. -/
def r823RealR700NestedCompleteFoldClosed : Bool := true

end Rational345R823RealNestedOrbit
end NSBControl
