import Mathlib

/-!
# Archimedes on the circle: 3, 6, 9 and the approximation of `π`

The circle of the previous sections is the unit circle.  This file puts Archimedes' figures on
it: for each `n ≥ 3` the regular `n`-gon inscribed in the unit circle and the regular `n`-gon
circumscribed about it.  Writing `b n = n sin (π / n)` and `a n = n tan (π / n)` for their
*half*-perimeters, Archimedes' theorem is the sandwich

  `b n < π < a n`,

together with the doubling ladder that lets one refine it: the circumscribed half-perimeter
doubles by a harmonic mean and the inscribed one by a geometric mean.

The trinity `3, 6, 9` sits at the start of the ladder:

* the hexagon is the exact anchor, `b 6 = 3` and `a 6 = 2√3`, hence `3 < π < 2√3`;
* doubling `6 ↦ 12 ↦ 24 ↦ …` is Archimedes' own ladder, and `b 12 = 3(√6 − √2)`;
* the square gives `b 4 = 2√2`, `a 4 = 4`;
* the nine-gon is the odd one out: `sin (π / 9)` is a root of the trisection cubic
  `3s − 4s³ = √3/2` and is not constructible, so `9` cannot be reached from `3` or `6` by the
  ladder.  We still bracket it: `3.077 < b 9 < 3.079`.

Main results:

* `lower_lt_pi`, `pi_lt_upper` — Archimedes' sandwich.
* `upper_two_mul`, `lower_two_mul` — the harmonic/geometric doubling recursions.
* `lower_lt_lower_two_mul`, `upper_two_mul_lt_upper` — the ladder is monotone.
* `tendsto_lower`, `tendsto_upper` — both sides converge to `π`.
* `lower_three`, `lower_four`, `lower_six`, `lower_twelve` and their `upper` companions.
* `hexagon_bounds`, `twelve_gon_bounds` — the numerical output of the first two rungs.
* `sin_pi_div_nine_cubic`, `lower_nine_bounds` — the nine-gon.
-/

namespace Archimedes369

open Real Filter Topology

/-- Half the perimeter of the regular `n`-gon **inscribed** in the unit circle. -/
noncomputable def lower (n : ℕ) : ℝ := n * sin (π / n)

/-- Half the perimeter of the regular `n`-gon **circumscribed** about the unit circle. -/
noncomputable def upper (n : ℕ) : ℝ := n * tan (π / n)

/-- The area of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def inArea (n : ℕ) : ℝ := (n / 2) * sin (2 * π / n)

section Basic

variable {n : ℕ}

lemma three_le_cast (hn : 3 ≤ n) : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn

lemma cast_pos (hn : 3 ≤ n) : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le (by norm_num) (three_le_cast hn)

lemma pi_div_pos (hn : 3 ≤ n) : 0 < π / n := div_pos pi_pos (cast_pos hn)

lemma pi_div_lt_pi_div_two (hn : 3 ≤ n) : π / n < π / 2 := by
  have h3 := three_le_cast hn
  exact div_lt_div_of_pos_left pi_pos (by norm_num) (by linarith)

lemma cos_pi_div_pos (hn : 3 ≤ n) : 0 < cos (π / n) :=
  cos_pos_of_mem_Ioo ⟨by linarith [pi_div_pos hn, pi_pos], pi_div_lt_pi_div_two hn⟩

lemma sin_pi_div_pos (hn : 3 ≤ n) : 0 < sin (π / n) :=
  sin_pos_of_pos_of_lt_pi (pi_div_pos hn) (lt_trans (pi_div_lt_pi_div_two hn) (by linarith [pi_pos]))

/-- Archimedes' lower bound: the inscribed half-perimeter is below `π`. -/
theorem lower_lt_pi (hn : 3 ≤ n) : lower n < π := by
  have hpos := cast_pos hn
  have h := Real.sin_lt (x := π / n) (pi_div_pos hn)
  calc lower n < (n:ℝ) * (π / n) := by unfold lower; nlinarith
    _ = π := by field_simp

/-- Archimedes' upper bound: the circumscribed half-perimeter is above `π`. -/
theorem pi_lt_upper (hn : 3 ≤ n) : π < upper n := by
  have hpos := cast_pos hn
  have h := Real.lt_tan (pi_div_pos hn) (pi_div_lt_pi_div_two hn)
  calc π = (n:ℝ) * (π / n) := by field_simp
    _ < upper n := by unfold upper; nlinarith

theorem lower_lt_upper (hn : 3 ≤ n) : lower n < upper n :=
  lt_trans (lower_lt_pi hn) (pi_lt_upper hn)

theorem lower_pos (hn : 3 ≤ n) : 0 < lower n :=
  mul_pos (cast_pos hn) (sin_pi_div_pos hn)

theorem upper_pos (hn : 3 ≤ n) : 0 < upper n := lt_trans pi_pos (pi_lt_upper hn)

/-- The inscribed area is also below `π`, and equals `lower n * cos (π / n)`. -/
theorem inArea_eq (n : ℕ) : inArea n = lower n * cos (π / n) := by
  have h : (2:ℝ) * π / n = 2 * (π / n) := by ring
  unfold inArea lower
  rw [h, Real.sin_two_mul]; ring

theorem inArea_lt_pi (hn : 3 ≤ n) : inArea n < π := by
  have h1 := lower_lt_pi hn
  have h2 := lower_pos hn
  have h3 : cos (π / n) ≤ 1 := Real.cos_le_one _
  have h4 := cos_pi_div_pos hn
  rw [inArea_eq n]
  nlinarith

end Basic

section Doubling

variable {n : ℕ}

/-- Doubling the number of sides: the circumscribed half-perimeter is the **harmonic mean**
of the previous two. -/
theorem upper_two_mul (hn : 3 ≤ n) :
    upper (2 * n) = 2 * upper n * lower n / (upper n + lower n) := by
  have hpos := cast_pos hn
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hx : π / ((2 * n : ℕ) : ℝ) = π / (2 * n) := by rw [hcast]
  have h2x : π / (n : ℝ) = 2 * (π / (2 * n)) := by field_simp
  have hxpos : 0 < π / (2 * (n:ℝ)) := by positivity
  have hxlt : π / (2 * (n:ℝ)) < π / 2 := by
    apply div_lt_div_of_pos_left pi_pos (by norm_num)
    have := three_le_cast hn; linarith
  have hc : cos (π / (2 * (n:ℝ))) ≠ 0 :=
    ne_of_gt (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxlt⟩)
  have hc2 : cos (2 * (π / (2 * (n:ℝ)))) ≠ 0 := by
    rw [← h2x]; exact ne_of_gt (cos_pi_div_pos hn)
  have hden : upper n + lower n ≠ 0 := ne_of_gt (add_pos (upper_pos hn) (lower_pos hn))
  rw [eq_div_iff hden]
  unfold upper lower
  rw [hcast, hx, h2x, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_two_mul,
    Real.cos_two_mul] at *
  field_simp
  ring

/-- Doubling the number of sides: the inscribed half-perimeter is the **geometric mean** of
the new circumscribed one and the old inscribed one. -/
theorem lower_two_mul (hn : 3 ≤ n) :
    lower (2 * n) = √(upper (2 * n) * lower n) := by
  have hpos := cast_pos hn
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h2x : π / (n : ℝ) = 2 * (π / (2 * n)) := by field_simp
  have hxpos : 0 < π / (2 * (n:ℝ)) := by positivity
  have hxlt : π / (2 * (n:ℝ)) < π / 2 := by
    apply div_lt_div_of_pos_left pi_pos (by norm_num)
    have := three_le_cast hn; linarith
  have hc : 0 < cos (π / (2 * (n:ℝ))) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxlt⟩
  have hs : 0 < sin (π / (2 * (n:ℝ))) :=
    sin_pos_of_pos_of_lt_pi hxpos (lt_trans hxlt (by linarith [pi_pos]))
  have key : upper (2 * n) * lower n = (lower (2 * n)) ^ 2 := by
    unfold upper lower
    rw [hcast, h2x, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  rw [key, Real.sqrt_sq]
  unfold lower
  rw [hcast]
  exact mul_nonneg (by positivity) hs.le

theorem lower_lt_lower_two_mul (hn : 3 ≤ n) : lower n < lower (2 * n) := by
  have h3 : 3 ≤ 2 * n := by omega
  have hb : 0 < lower n := lower_pos hn
  have hkey : lower n < upper (2 * n) :=
    lt_trans (lower_lt_pi hn) (pi_lt_upper h3)
  rw [lower_two_mul hn]
  have : lower n = √(lower n * lower n) := by
    rw [Real.sqrt_mul_self hb.le]
  conv_lhs => rw [this]
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith

theorem upper_two_mul_lt_upper (hn : 3 ≤ n) : upper (2 * n) < upper n := by
  have ha := upper_pos hn
  have hb := lower_pos hn
  have hlt := lower_lt_upper hn
  rw [upper_two_mul hn, div_lt_iff₀ (by positivity)]
  nlinarith

end Doubling

section Limits

theorem tendsto_pi_div : Tendsto (fun n : ℕ => π / n) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat π

lemma tendsto_sinc : Tendsto (fun n : ℕ => Real.sinc (π / n)) atTop (𝓝 1) := by
  have := (Real.continuous_sinc.tendsto 0).comp tendsto_pi_div
  simpa [Real.sinc_zero] using this

lemma tendsto_cos_pi_div : Tendsto (fun n : ℕ => cos (π / n)) atTop (𝓝 1) := by
  have := (Real.continuous_cos.tendsto 0).comp tendsto_pi_div
  simpa using this

/-- The inscribed half-perimeters converge to `π`. -/
theorem tendsto_lower : Tendsto (fun n : ℕ => lower n) atTop (𝓝 π) := by
  have h2 : Tendsto (fun n : ℕ => π * Real.sinc (π / n)) atTop (𝓝 (π * 1)) :=
    tendsto_sinc.const_mul π
  rw [mul_one] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.sinc_of_ne_zero (by positivity)]
  unfold lower
  field_simp

/-- The circumscribed half-perimeters converge to `π`. -/
theorem tendsto_upper : Tendsto (fun n : ℕ => upper n) atTop (𝓝 π) := by
  have h2 : Tendsto (fun n : ℕ => (π * Real.sinc (π / n)) / cos (π / n)) atTop
      (𝓝 ((π * 1) / 1)) :=
    (tendsto_sinc.const_mul π).div tendsto_cos_pi_div one_ne_zero
  rw [mul_one, div_one] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (0:ℝ) < n := cast_pos hn
  have hc := (cos_pi_div_pos hn).ne'
  rw [Real.sinc_of_ne_zero (by positivity)]
  unfold upper
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- The inscribed areas converge to `π`. -/
theorem tendsto_inArea : Tendsto (fun n : ℕ => inArea n) atTop (𝓝 π) := by
  have h2 : Tendsto (fun n : ℕ => lower n * cos (π / n)) atTop (𝓝 (π * 1)) :=
    tendsto_lower.mul tendsto_cos_pi_div
  rw [mul_one] at h2
  exact h2.congr fun n => (inArea_eq n).symm

end Limits

section Values

theorem lower_three : lower 3 = 3 * √3 / 2 := by
  unfold lower; norm_num [Real.sin_pi_div_three]; ring

theorem upper_three : upper 3 = 3 * √3 := by
  unfold upper; norm_num [Real.tan_pi_div_three]

/-- The **square**: half its inscribed perimeter is `2√2 = 2.828…`. -/
theorem lower_four : lower 4 = 2 * √2 := by
  unfold lower; norm_num [Real.sin_pi_div_four]; ring

theorem upper_four : upper 4 = 4 := by
  unfold upper; norm_num [Real.tan_pi_div_four]

/-- The **hexagon** is the exact anchor of the whole ladder: half its inscribed perimeter is
exactly `3`.  (Its side equals the radius — this is why Archimedes started here.) -/
theorem lower_six : lower 6 = 3 := by
  unfold lower; norm_num [Real.sin_pi_div_six]

theorem upper_six : upper 6 = 2 * √3 := by
  unfold upper
  norm_num [Real.tan_pi_div_six]
  have h : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3 : (0:ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  nlinarith [h]

theorem sin_pi_div_twelve : sin (π / 12) = (√6 - √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  rw [h, Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_three,
    Real.sin_pi_div_four]
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h6]; ring

theorem cos_pi_div_twelve : cos (π / 12) = (√6 + √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  rw [h, Real.cos_sub, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_three,
    Real.sin_pi_div_four]
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h6]; ring

theorem tan_pi_div_twelve : tan (π / 12) = 2 - √3 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2p : (0:ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h3p : (0:ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hden : √6 + √2 ≠ 0 := by rw [h6]; positivity
  have hsimp : ((√6 - √2) / 4) / ((√6 + √2) / 4) = (√6 - √2) / (√6 + √2) := by
    field_simp
  rw [Real.tan_eq_sin_div_cos, sin_pi_div_twelve, cos_pi_div_twelve, hsimp, div_eq_iff hden, h6]
  nlinarith [h2, h3]

/-- The first rung of Archimedes' ladder above the hexagon: the twelve-gon. -/
theorem lower_twelve : lower 12 = 3 * (√6 - √2) := by
  unfold lower; norm_num [sin_pi_div_twelve]; ring

theorem upper_twelve : upper 12 = 24 - 12 * √3 := by
  unfold upper; norm_num [tan_pi_div_twelve]; ring

/-- The hexagon rung: `3 < π < 2√3`, i.e. `3 < π < 3.4641…`.  The lower bound is exactly the
first member of the trinity. -/
theorem hexagon_bounds : 3 < π ∧ π < 2 * √3 := by
  constructor
  · have := lower_lt_pi (n := 6) (by norm_num)
    rwa [lower_six] at this
  · have := pi_lt_upper (n := 6) (by norm_num)
    rwa [upper_six] at this

/-- The twelve-gon rung: `3(√6 − √2) < π < 24 − 12√3`, i.e. `3.1058… < π < 3.2153…`. -/
theorem twelve_gon_bounds : 3 * (√6 - √2) < π ∧ π < 24 - 12 * √3 := by
  constructor
  · have := lower_lt_pi (n := 12) (by norm_num)
    rwa [lower_twelve] at this
  · have := pi_lt_upper (n := 12) (by norm_num)
    rwa [upper_twelve] at this

end Values

section Nine

/-- The nine-gon is a trisection of the equilateral triangle: `s = sin (π / 9)` satisfies the
trisection cubic `3s − 4s³ = √3/2`.  This cubic is irreducible over `ℚ(√3)`, which is why the
regular nine-gon is not constructible and why `9` is not on Archimedes' doubling ladder. -/
theorem sin_pi_div_nine_cubic : 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 = √3 / 2 := by
  have h : π / 3 = 3 * (π / 9) := by ring
  have h3 := Real.sin_three_mul (π / 9)
  rw [← h, Real.sin_pi_div_three] at h3
  linarith

theorem sin_pi_div_nine_bounds : 0.3419 < sin (π / 9) ∧ sin (π / 9) < 0.3421 := by
  set s := sin (π / 9) with hsdef
  have hpi : π < 4 := Real.pi_lt_four
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hs1 : s < 1 / 2 := lt_of_lt_of_le (Real.sin_lt (by positivity)) (by linarith)
  have hcube := sin_pi_div_nine_cubic
  rw [← hsdef] at hcube
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : (0:ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h3l : 1.7320508 < √3 := by nlinarith
  have h3u : √3 < 1.7320509 := by nlinarith
  constructor
  · nlinarith [sq_nonneg (s - 0.3419), sq_nonneg (s + 0.3419), sq_nonneg s]
  · nlinarith [sq_nonneg (s - 0.3421), sq_nonneg (s + 0.3421), sq_nonneg s]

/-- The nine-gon rung, numerically: `3.077 < b₉ < 3.079`. -/
theorem lower_nine_bounds : 3.077 < lower 9 ∧ lower 9 < 3.079 := by
  have h := sin_pi_div_nine_bounds
  have hl : lower 9 = 9 * sin (π / 9) := by unfold lower; norm_num
  rw [hl]
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

end Nine

end Archimedes369
