import Mathlib.Tactic
import NSBControl.Rational345Round71ZeroModeUnique

/-!
# Real R744 critical-production incidence carrier

The Agda R38/R744 ordered power is the real Hermitian test of one literal
ordered Galerkin interaction.  The public real radius-four model already has
exactly that interaction as `projectedOrderedBilinear`.

This file exposes the same incidence scalar on the genuine real carrier and
proves that summing the ordered powers at one output gives the actual modal
pairing used by `criticalProduction`.  Consequently the complete dyadically
weighted incidence fold is exactly one half of the public critical production.

The final theorem prunes zero input modes on zero-mean states, aligning the
ambient Lean sum with Agda's nonzero physical-incidence carrier.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823RealProductionIncidence

open Rational345RealRadius4
open Rational345Round71ZeroMode

classical

/-- Real part of the Hermitian pairing with a fixed output coefficient, bundled
as a real-linear map so finite sums commute with testing automatically. -/
def pairingRealLinear (test : Vec3) : Vec3 →ₗ[ℝ] ℝ where
  toFun := fun v => (hermitianDot test v).re
  map_add' := by
    intro a b
    simp [hermitianDot, Finset.mul_sum, Complex.add_re]
    ring
  map_smul' := by
    intro c v
    simp [hermitianDot, Finset.mul_sum, Complex.mul_re]
    ring

/-- Literal real R38 ordered power for one `(p,q -> k)` incidence. -/
def orderedPower (u : State) (p q k : Mode) : ℝ :=
  pairingRealLinear (u k) (projectedOrderedBilinear u u p q k)

/-- Complete ordered-power fibre at one output. -/
def fixedOutputOrderedPower (u : State) (k : Mode) : ℝ :=
  ∑ p : Mode, ∑ q : Mode, orderedPower u p q k

/-- Vector-valued ambient ordered fibre. -/
def fixedOutputOrderedVector (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode, projectedOrderedBilinear u u p q k

/-- The ambient ordered vector fibre is the public projected nonlinearity. -/
theorem fixedOutputOrderedVector_eq_projectedNonlinearity
    (u : State) (k : Mode) :
    fixedOutputOrderedVector u k = projectedNonlinearity u k := by
  unfold fixedOutputOrderedVector projectedNonlinearity projectedBilinear
  by_cases hk : isZeroMode k
  · rw [if_pos hk]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    unfold projectedOrderedBilinear
    by_cases hres : Resonates p q k
    · simp [hres, leray, hk]
    · simp [hres]
  · rw [if_neg hk]

/-- Fixed-output R38 incidence summation equals the actual modal production
pairing. -/
theorem fixedOutputOrderedPower_eq_pairing
    (u : State) (k : Mode) :
    fixedOutputOrderedPower u k =
      (hermitianDot (u k) (projectedNonlinearity u k)).re := by
  unfold fixedOutputOrderedPower orderedPower
  change
    (∑ p : Mode, ∑ q : Mode,
      pairingRealLinear (u k) (projectedOrderedBilinear u u p q k)) = _
  rw [← map_sum]
  simp_rw [← map_sum]
  change pairingRealLinear (u k) (fixedOutputOrderedVector u k) = _
  rw [fixedOutputOrderedVector_eq_projectedNonlinearity]
  rfl

/-- R744's zero-safe dyadic incidence scalar.  The public `criticalWeight`
already carries the cutoff-four critical dyadic multiplier. -/
def weightedProductionIncidence (u : State) (p q k : Mode) : ℝ :=
  if isZeroMode k then 0
  else criticalWeight k * orderedPower u p q k

def weightedProductionIncidenceTotal (u : State) : ℝ :=
  ∑ k : Mode, ∑ p : Mode, ∑ q : Mode,
    weightedProductionIncidence u p q k

/-- Complete R744 incidence normalization: critical production is twice the
weighted ordered-power fold. -/
theorem criticalProduction_eq_twice_weightedIncidence (u : State) :
    criticalProduction u = 2 * weightedProductionIncidenceTotal u := by
  unfold criticalProduction weightedProductionIncidenceTotal modalProduction
    weightedProductionIncidence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hkMem
  by_cases hk : isZeroMode k
  · simp [hk]
  · simp only [hk, if_false]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl]
    · change
        2 * criticalWeight k *
            (hermitianDot (u k) (projectedNonlinearity u k)).re =
          ∑ p : Mode, ∑ q : Mode,
            2 * (criticalWeight k * orderedPower u p q k)
      rw [← fixedOutputOrderedPower_eq_pairing]
      unfold fixedOutputOrderedPower
      simp only [Finset.mul_sum]
      ring
    · intro p hp
      rfl

/-- Physical nonzero-input R744 incidence scalar. -/
def physicalWeightedProductionIncidence
    (u : State) (p q k : Mode) : ℝ :=
  if nonzeroMode p ∧ nonzeroMode q ∧ nonzeroMode k ∧ Resonates p q k then
    criticalWeight k * orderedPower u p q k
  else 0

def physicalWeightedProductionIncidenceTotal (u : State) : ℝ :=
  ∑ k : Mode, ∑ p : Mode, ∑ q : Mode,
    physicalWeightedProductionIncidence u p q k

/-- On a zero-mean state, deleting zero-input/nonresonant incidences does not
change the complete weighted production fold. -/
theorem weightedIncidence_eq_physicalWeightedIncidence
    (u : State) (hzero : u zeroMode = 0) :
    weightedProductionIncidenceTotal u =
      physicalWeightedProductionIncidenceTotal u := by
  unfold weightedProductionIncidenceTotal physicalWeightedProductionIncidenceTotal
  apply Finset.sum_congr rfl
  intro k hkMem
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro q hqMem
  unfold weightedProductionIncidence physicalWeightedProductionIncidence
  by_cases hk0 : isZeroMode k
  · simp [hk0]
  · by_cases hp0 : isZeroMode p
    · have hup : u p = 0 := value_zero_of_isZero u hzero p hp0
      simp [hk0, hp0, orderedPower, pairingRealLinear,
        projectedOrderedBilinear, hup]
  · by_cases hq0 : isZeroMode q
    · have huq : u q = 0 := value_zero_of_isZero u hzero q hq0
      simp [hk0, hp0, hq0, orderedPower, pairingRealLinear,
        projectedOrderedBilinear, huq]
  · by_cases hres : Resonates p q k
    · simp [hk0, hp0, hq0, hres]
    · simp [hk0, hp0, hq0, hres, orderedPower,
        projectedOrderedBilinear]

/-- Real R744 incidence carrier is now explicit on the R830 state space. -/
def r823RealR744ProductionIncidenceClosed : Bool := true

end Rational345R823RealProductionIncidence
end NSBControl
