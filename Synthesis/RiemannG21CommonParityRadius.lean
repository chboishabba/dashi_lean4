import Mathlib.Tactic
import Synthesis.RiemannG21EvenFiniteMinorExists

/-!
# Common G21 finite radius for both parity blocks

The odd and even support-only gates are both monotone small-radius conditions.
Therefore positive odd/even normalized gaps admit one common sample radius
`0<r<=1` satisfying both:

  P_odd(R) r^2 < 900 gap_odd,
  P_even(R) r^2 < 54 gap_even.

This is required by the actual four-sample symmetric carrier: independently
chosen odd/even radii would not prove transversality of one common sampled
vector.
-/

namespace Synthesis

/-- One unit-scale radius satisfying both parity gates. -/
theorem exists_unit_commonParityRadiusGate
    {R oddGap evenGap : ℝ}
    (hR : 0 <= R) (hOdd : 0 < oddGap) (hEven : 0 < evenGap) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      g21OddSupportPolynomial R*r^2 < 900*oddGap ∧
      g21EvenSupportPolynomial R*r^2 < 54*evenGap := by
  have hot : 0 < (900:ℝ)*oddGap := by positivity
  have het : 0 < (54:ℝ)*evenGap := by positivity
  obtain ⟨co,hco,hcoGate⟩ := exists_pos_mul_lt hot (g21OddSupportPolynomial R)
  obtain ⟨ce,hce,hceGate⟩ := exists_pos_mul_lt het (g21EvenSupportPolynomial R)
  let r : ℝ := min (min co ce) 1
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min hco hce) zero_lt_one
  have hr1 : r <= 1 := min_le_right _ _
  have hrco : r <= co := (min_le_left _ _).trans (min_le_left _ _)
  have hrce : r <= ce := (min_le_left _ _).trans (min_le_right _ _)
  have hr2r : r^2 <= r := by nlinarith
  have hr2co : r^2 <= co := hr2r.trans hrco
  have hr2ce : r^2 <= ce := hr2r.trans hrce
  have hoPoly : 0 <= g21OddSupportPolynomial R := g21OddSupportPolynomial_nonneg R
  have hePoly : 0 <= g21EvenSupportPolynomial R := g21EvenSupportPolynomial_nonneg R
  have ho := (mul_le_mul_of_nonneg_left hr2co hoPoly).trans_lt hcoGate
  have he := (mul_le_mul_of_nonneg_left hr2ce hePoly).trans_lt hceGate
  exact ⟨r,hr,hr1,ho,he⟩

end Synthesis
