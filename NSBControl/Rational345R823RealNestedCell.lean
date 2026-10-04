import Mathlib.Tactic
import NSBControl.Rational345R823RealInnerFold

/-!
# Real R694/R700 nested four-helicity cell

The Agda R573/R694 carrier is not introduced as an alias for the commutator.
Its inner forcing slot is the literal R572 four-sign multiplier-difference
fibre.  R572 identifies that fibre with two copies of the projected forcing;
the outer R573 construction contributes a second copy.  Hence the resulting
nested cell is four copies of the real forcing-commutator cell.

This file ports exactly that factorization to the genuine real radius-four
carrier used by R830.
-/

namespace NSBControl
namespace Rational345R823RealNestedCell

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealInnerFold

classical

/-- The literal inner four-sign forcing at each output mode. -/
def realFourSignForcing (u : State) : State :=
  fun k => fourSignInnerFold u k

/-- Outer commutator evaluated on the literal R572 inner fibre. -/
def realNestedHalfCell (u : State) (p q : Mode) : Vec3 :=
  forcingCommutatorCell u (realFourSignForcing u) p q

/-- Literal real R573/R694 nested cell.  The second copy is the outer R573
integer doubling; the inner doubling remains inside `realFourSignForcing`. -/
def realNestedCell (u : State) (p q : Mode) : Vec3 :=
  realNestedHalfCell u p q + realNestedHalfCell u p q

@[simp] theorem leray_add_real (k : Mode) (a b : Vec3) :
    leray k (a + b) = leray k a + leray k b := by
  funext j
  unfold leray bilinearDot
  split_ifs <;> simp [Fin.sum_univ_succ] <;> ring

@[simp] theorem helicalPlus_add_real (k : Mode) (a b : Vec3) :
    helicalPlus k (a + b) = helicalPlus k a + helicalPlus k b := by
  funext j
  simp [helicalPlus, leray_add_real,
    Rational345R823RealHelicalCore.curlSymbol_add]
  ring

@[simp] theorem helicalMinus_add_real (k : Mode) (a b : Vec3) :
    helicalMinus k (a + b) = helicalMinus k a + helicalMinus k b := by
  funext j
  simp [helicalMinus, leray_add_real,
    Rational345R823RealHelicalCore.curlSymbol_add]
  ring

@[simp] theorem cross_add_left_real (a b c : Vec3) :
    cross (a + b) c = cross a c + cross b c := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

/-- The real forcing commutator is additive in its forcing slot. -/
theorem forcingCommutatorCell_add_forcing
    (u f g : State) (p q : Mode) :
    forcingCommutatorCell u (f + g) p q =
      forcingCommutatorCell u f p q + forcingCommutatorCell u g p q := by
  funext j
  simp [forcingCommutatorCell, helicalPlus_add_real,
    helicalMinus_add_real, cross_add_left_real]
  ring

/-- R572 identifies the literal four-sign inner fibre with two copies of the
projected nonlinearity on a physical nonzero output. -/
theorem realFourSignForcing_eq_twiceProjected
    (u : State) (p : Mode)
    (hp : nonzeroMode p)
    (hzero : u zeroMode = 0)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    realFourSignForcing u p =
      projectedNonlinearity u p + projectedNonlinearity u p := by
  unfold realFourSignForcing
  exact
    (physicalPairedFold_eq_fourSignInnerFold u p hp hzero htrans).symm.trans
      (physicalPairedFold_eq_twiceProjectedNonlinearity u p hp hzero)

/-- Real R694 same-object theorem.  The left side retains the literal R572
four-helicity fibre; the right side is the existing real R230-style forcing
commutator used by the R853 coherent carrier. -/
theorem realNestedCell_eq_fourCommutator
    (u : State) (p q : Mode)
    (hp : nonzeroMode p) (_hq : nonzeroMode q)
    (hzero : u zeroMode = 0)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    realNestedCell u p q =
      4 • forcingCommutatorCell u (projectedNonlinearity u) p q := by
  have hinner := realFourSignForcing_eq_twiceProjected u p hp hzero htrans
  have hhalf :
      realNestedHalfCell u p q =
        forcingCommutatorCell u (projectedNonlinearity u) p q +
        forcingCommutatorCell u (projectedNonlinearity u) p q := by
    unfold realNestedHalfCell realFourSignForcing
    unfold forcingCommutatorCell
    rw [hinner]
    simp [helicalPlus_add_real, helicalMinus_add_real, cross_add_left_real]
    ext j
    ring
  unfold realNestedCell
  rw [hhalf]
  ext j
  simp [Pi.add_apply]
  ring

/-- D1 source owner: the literal real nested four-helicity cell exists and is
same-object with four copies of the real commutator cell on physical states. -/
def r823RealR694NestedCellClosed : Bool := true

end Rational345R823RealNestedCell
end NSBControl
