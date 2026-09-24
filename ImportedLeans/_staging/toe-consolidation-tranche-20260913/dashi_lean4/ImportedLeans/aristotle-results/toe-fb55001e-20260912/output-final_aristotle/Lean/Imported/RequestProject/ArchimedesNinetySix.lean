import Mathlib
import RequestProject.Archimedes369

/-!
# Archimedes' own bound: `223/71 < π < 22/7`

`RequestProject/Archimedes369.lean` proves the sandwich `bₙ < π < aₙ` and the doubling ladder
`a₂ₙ = 2aₙbₙ/(aₙ+bₙ)`, `b₂ₙ = √(a₂ₙbₙ)`.  This file climbs the ladder the way Archimedes did:
starting from the hexagon, where `b₆ = 3` and `a₆ = 2√3` are known exactly, four doublings give
the ninety-six-gon, and rational bounds carried along the way produce

  `223/71 < π < 22/7`.

Nothing here uses a numerical value of `π`: the only inputs are the two recursions, the exact
hexagon values, and rational arithmetic.  The mechanism is interval propagation
(`bounds_two_mul`): a rational lower and upper bound for each of `aₙ`, `bₙ` is pushed through the
harmonic and geometric means, whose monotonicity is `harm_mono_lower` and `harm_mono_upper`.
-/

namespace Archimedes369

open Real

section Monotonicity

/-- The harmonic mean is monotone: raising the arguments raises it. -/
lemma harm_mono_lower {a b aL bL : ℝ} (haL : 0 < aL) (hbL : 0 < bL)
    (ha : aL ≤ a) (hb : bL ≤ b) :
    2 * aL * bL / (aL + bL) ≤ 2 * a * b / (a + b) := by
  have ha0 : 0 < a := lt_of_lt_of_le haL ha
  have hb0 : 0 < b := lt_of_lt_of_le hbL hb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg haL.le ha0.le) (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg hbL.le hb0.le) (sub_nonneg.mpr ha)]

lemma harm_mono_upper {a b aU bU : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ aU) (hb : b ≤ bU) :
    2 * a * b / (a + b) ≤ 2 * aU * bU / (aU + bU) := by
  have haU : 0 < aU := lt_of_lt_of_le ha0 ha
  have hbU : 0 < bU := lt_of_lt_of_le hb0 hb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg ha0.le haU.le) (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg hb0.le hbU.le) (sub_nonneg.mpr ha)]

end Monotonicity

section Interval

/-- One rung of the ladder, with rational bounds carried along: from bounds on `aₙ` and `bₙ`,
bounds on `a₂ₙ` and `b₂ₙ`.  The hypotheses `k1`–`k6` are pure arithmetic and are discharged by
`norm_num` at each concrete step. -/
lemma bounds_two_mul {n : ℕ} (hn : 3 ≤ n) {aL aU bL bU aL' aU' bL' bU' : ℝ}
    (haL : 0 < aL) (hbL : 0 < bL)
    (h1 : aL ≤ upper n) (h2 : upper n ≤ aU) (h3 : bL ≤ lower n) (h4 : lower n ≤ bU)
    (k1 : aL' ≤ 2 * aL * bL / (aL + bL)) (k2 : 2 * aU * bU / (aU + bU) ≤ aU')
    (k3 : 0 ≤ bL') (k4 : bL' ^ 2 ≤ aL' * bL) (k5 : aU' * bU ≤ bU' ^ 2) (k6 : 0 ≤ bU') :
    aL' ≤ upper (2 * n) ∧ upper (2 * n) ≤ aU' ∧
      bL' ≤ lower (2 * n) ∧ lower (2 * n) ≤ bU' := by
  have hu0 : 0 < upper n := upper_pos hn
  have hl0 : 0 < lower n := lower_pos hn
  have hup : upper (2 * n) = 2 * upper n * lower n / (upper n + lower n) := upper_two_mul hn
  have haL' : aL' ≤ upper (2 * n) := by
    rw [hup]; exact le_trans k1 (harm_mono_lower haL hbL h1 h3)
  have haU' : upper (2 * n) ≤ aU' := by
    rw [hup]; exact le_trans (harm_mono_upper hu0 hl0 h2 h4) k2
  have hu2 : 0 < upper (2 * n) := upper_pos (by omega)
  have haU'0 : 0 ≤ aU' := le_trans hu2.le haU'
  refine ⟨haL', haU', ?_, ?_⟩
  · rw [lower_two_mul hn]
    have hkey : bL' ^ 2 ≤ upper (2 * n) * lower n :=
      le_trans k4 (mul_le_mul haL' h3 hbL.le hu2.le)
    calc bL' = √(bL' ^ 2) := (Real.sqrt_sq k3).symm
      _ ≤ √(upper (2 * n) * lower n) := Real.sqrt_le_sqrt hkey
  · rw [lower_two_mul hn]
    have hkey : upper (2 * n) * lower n ≤ bU' ^ 2 :=
      le_trans (mul_le_mul haU' h4 hl0.le haU'0) k5
    calc √(upper (2 * n) * lower n) ≤ √(bU' ^ 2) := Real.sqrt_le_sqrt hkey
      _ = bU' := Real.sqrt_sq k6

end Interval

section Ladder

/-- The hexagon, exactly: `b₆ = 3` and `a₆ = 2√3 = 3.4641016…`. -/
lemma bounds_six : (3.4641016 : ℝ) ≤ upper 6 ∧ upper 6 ≤ 3.4641017 ∧
    (3 : ℝ) ≤ lower 6 ∧ lower 6 ≤ 3 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : (0:ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hlo : (1.7320508 : ℝ) < √3 := by nlinarith
  have hhi : √3 < 1.73205085 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [upper_six]; linarith
  · rw [upper_six]; linarith
  · rw [lower_six]
  · rw [lower_six]

lemma bounds_twelve : (3.2153903 : ℝ) ≤ upper 12 ∧ upper 12 ≤ 3.2153904 ∧
    (3.1058285 : ℝ) ≤ lower 12 ∧ lower 12 ≤ 3.1058286 := by
  obtain ⟨h1, h2, h3, h4⟩ := bounds_six
  have := bounds_two_mul (n := 6) (by norm_num) (aL := 3.4641016) (bL := 3)
    (by norm_num) (by norm_num) h1 h2 h3 h4
    (aL' := 3.2153903) (aU' := 3.2153904) (bL' := 3.1058285) (bU' := 3.1058286)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [show (2 * 6 : ℕ) = 12 from rfl] at this

lemma bounds_twentyfour : (3.1596599 : ℝ) ≤ upper 24 ∧ upper 24 ≤ 3.1596601 ∧
    (3.1326285 : ℝ) ≤ lower 24 ∧ lower 24 ≤ 3.1326288 := by
  obtain ⟨h1, h2, h3, h4⟩ := bounds_twelve
  have := bounds_two_mul (n := 12) (by norm_num) (aL := 3.2153903) (bL := 3.1058285)
    (by norm_num) (by norm_num) h1 h2 h3 h4
    (aL' := 3.1596599) (aU' := 3.1596601) (bL' := 3.1326285) (bU' := 3.1326288)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [show (2 * 12 : ℕ) = 24 from rfl] at this

lemma bounds_fortyeight : (3.1460861 : ℝ) ≤ upper 48 ∧ upper 48 ≤ 3.1460864 ∧
    (3.1393500 : ℝ) ≤ lower 48 ∧ lower 48 ≤ 3.1393504 := by
  obtain ⟨h1, h2, h3, h4⟩ := bounds_twentyfour
  have := bounds_two_mul (n := 24) (by norm_num) (aL := 3.1596599) (bL := 3.1326285)
    (by norm_num) (by norm_num) h1 h2 h3 h4
    (aL' := 3.1460861) (aU' := 3.1460864) (bL' := 3.1393500) (bU' := 3.1393504)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [show (2 * 24 : ℕ) = 48 from rfl] at this

/-- The ninety-six-gon, where Archimedes stopped. -/
lemma bounds_ninetysix : (3.1427144 : ℝ) ≤ upper 96 ∧ upper 96 ≤ 3.1427148 ∧
    (3.1410317 : ℝ) ≤ lower 96 ∧ lower 96 ≤ 3.1410322 := by
  obtain ⟨h1, h2, h3, h4⟩ := bounds_fortyeight
  have := bounds_two_mul (n := 48) (by norm_num) (aL := 3.1460861) (bL := 3.1393500)
    (by norm_num) (by norm_num) h1 h2 h3 h4
    (aL' := 3.1427144) (aU' := 3.1427148) (bL' := 3.1410317) (bU' := 3.1410322)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [show (2 * 48 : ℕ) = 96 from rfl] at this

/-- **Archimedes' theorem**: the ninety-six-gon gives `223/71 < π < 22/7`, proved from the
hexagon and four doublings, with no numerical value of `π` as an input. -/
theorem archimedes_bounds : (223 : ℝ) / 71 < π ∧ π < 22 / 7 := by
  obtain ⟨-, hau, hbl, -⟩ := bounds_ninetysix
  constructor
  · have h := lower_lt_pi (n := 96) (by norm_num)
    nlinarith
  · have h := pi_lt_upper (n := 96) (by norm_num)
    nlinarith

end Ladder

end Archimedes369
