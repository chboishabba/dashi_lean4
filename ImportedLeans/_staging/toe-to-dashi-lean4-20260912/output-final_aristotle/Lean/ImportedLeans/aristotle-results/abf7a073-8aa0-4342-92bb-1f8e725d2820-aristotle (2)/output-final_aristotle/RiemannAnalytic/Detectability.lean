/-
Zero coordinates and the detectability radius.

This file makes two things literal.

*Zero coordinates.*  A hypothetical zero `ρ` of the completed zeta function with
`Re ρ > 1/2` is described by its transverse offset `α = Re ρ - 1/2 > 0` and its
ordinate `γ = Im ρ`; the associated grid coordinate is `z_ρ = γ - iα`, which is
literally `-i(ρ - 1/2)`.  The reflected zero `1 - ρ` has the opposite offset and
the opposite ordinate.

*Detectability radius.*  Suppose the analytic route produces, for a hypothetical
off-line zero, a transverse defect `D` obeying a quadratic floor
`c·L⁴·α² ≤ D` and an upper bound `D ≤ E` coming from the accumulated error
terms.  Then the offset is confined to the explicit tube

  `|α| ≤ √(E / (c L⁴))`,

and if the relative error `E / L⁴` tends to `0` the tube shrinks to the critical
line.  These are unconditional implications: the analytic inputs `hfloor` and
`hbound` are hypotheses, not assumptions about zeta, and nothing here asserts
the Riemann Hypothesis.
-/
import RiemannAnalytic.LiteralStatement

namespace RiemannAnalytic

open Complex Filter Topology

/-! ### Coordinates of a hypothetical zero -/

/-- The transverse offset of a point from the critical line. -/
noncomputable def zeroOffset (ρ : ℂ) : ℝ := ρ.re - 1 / 2

/-- The grid coordinate of a point: `z_ρ = -i(ρ - 1/2)`. -/
noncomputable def zeroCoord (ρ : ℂ) : ℂ := -Complex.I * (ρ - 1 / 2)

/-- The grid coordinate is `γ - iα`. -/
theorem zeroCoord_eq (ρ : ℂ) :
    zeroCoord ρ = ((ρ.im : ℝ) : ℂ) - Complex.I * ((zeroOffset ρ : ℝ) : ℂ) := by
  unfold zeroCoord zeroOffset
  apply Complex.ext <;> simp

theorem zeroCoord_re (ρ : ℂ) : (zeroCoord ρ).re = ρ.im := by
  unfold zeroCoord; simp

theorem zeroCoord_im (ρ : ℂ) : (zeroCoord ρ).im = -zeroOffset ρ := by
  unfold zeroCoord zeroOffset; simp

/-- A zero strictly to the right of the critical line has positive offset. -/
theorem offLineZero_offset_pos {ρ : ℂ} (h : 1 / 2 < ρ.re) : 0 < zeroOffset ρ := by
  unfold zeroOffset; linarith

/-- The reflected zero `1 - ρ` has the opposite transverse offset. -/
theorem reflect_offset (ρ : ℂ) : zeroOffset (1 - ρ) = -zeroOffset ρ := by
  unfold zeroOffset; simp; ring

/-- The reflected zero `1 - ρ` has the opposite ordinate. -/
theorem reflect_ordinate (ρ : ℂ) : (1 - ρ).im = -ρ.im := by simp

/-- The grid coordinate of the reflected zero is the negative of the original
grid coordinate. -/
theorem reflect_zeroCoord (ρ : ℂ) : zeroCoord (1 - ρ) = -zeroCoord ρ := by
  unfold zeroCoord
  ring_nf

/-- The transverse offset of a zero of `Λ` is confined to `(-1/2, 1/2)`. -/
theorem zeroOffset_abs_lt {ρ : ℂ} (h : completedRiemannZeta ρ = 0) :
    |zeroOffset ρ| < 1 / 2 := by
  obtain ⟨h0, h1⟩ := completedZeta_zero_mem_strip h
  unfold zeroOffset
  rw [abs_lt]
  constructor <;> linarith

/-! ### The detectability radius -/

/-- The **detectability radius** attached to a quadratic defect floor with
constant `c` at scale `L` and total error budget `E`: the largest transverse
offset that the error budget can still hide. -/
noncomputable def detectRadius (c L E : ℝ) : ℝ := Real.sqrt (E / (c * L ^ 4))

/-- **Quadratic detectability.**  If a transverse defect `D` obeys the quadratic
floor `c L⁴ α² ≤ D` and is bounded above by the error budget `E`, then the
offset lies inside the detectability radius. -/
theorem abs_offset_le_detectRadius {c L E D α : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hfloor : c * L ^ 4 * α ^ 2 ≤ D) (hbound : D ≤ E) :
    |α| ≤ detectRadius c L E := by
  have hpos : 0 < c * L ^ 4 := by positivity
  have hsq : α ^ 2 ≤ E / (c * L ^ 4) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hfloor, hbound]
  unfold detectRadius
  calc |α| = Real.sqrt (α ^ 2) := (Real.sqrt_sq_eq_abs α).symm
    _ ≤ Real.sqrt (E / (c * L ^ 4)) := Real.sqrt_le_sqrt hsq

/-- **Detectability at a zero.**  If the defect floor and the error bound hold
for a hypothetical zero of `Λ` in the coordinates above, then the zero lies in
the tube of radius `detectRadius c L E` around the critical line. -/
theorem zero_in_detectability_tube {c L E D : ℝ} (hc : 0 < c) (hL : 0 < L) {ρ : ℂ}
    (hfloor : c * L ^ 4 * zeroOffset ρ ^ 2 ≤ D) (hbound : D ≤ E) :
    |ρ.re - 1 / 2| ≤ detectRadius c L E :=
  abs_offset_le_detectRadius hc hL hfloor hbound

/-- If the relative error budget `E(T)/L(T)⁴` tends to zero, the detectability
radius tends to zero: the tube shrinks onto the critical line. -/
theorem detectRadius_tendsto_zero (c : ℝ) (L E : ℝ → ℝ)
    (h : Tendsto (fun T => E T / (c * L T ^ 4)) atTop (𝓝 0)) :
    Tendsto (fun T => detectRadius c (L T) (E T)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [detectRadius, Function.comp] using this

/-- If the detectability radius is zero and the defect floor and error bound
hold, the zero lies exactly on the critical line. -/
theorem zero_on_critical_line_of_detectRadius_zero {c L E D : ℝ} (hc : 0 < c) (hL : 0 < L)
    {ρ : ℂ} (hfloor : c * L ^ 4 * zeroOffset ρ ^ 2 ≤ D) (hbound : D ≤ E)
    (hzero : detectRadius c L E = 0) :
    ρ.re = 1 / 2 := by
  have h := zero_in_detectability_tube hc hL hfloor hbound
  rw [hzero] at h
  have := abs_nonneg (ρ.re - 1 / 2)
  have habs : |ρ.re - 1 / 2| = 0 := le_antisymm h this
  have := abs_eq_zero.1 habs
  linarith

/-! ### Splitting the literal statement by height -/

/-- **Height split.**  The literal Riemann Hypothesis follows from the absence
of right-half-plane zeros of `Λ` above a threshold height together with their
absence below it.  This is the shape in which an eventual analytic argument
(valid for large ordinates) has to be combined with a bounded-height closure. -/
theorem riemannHypothesis_of_height_split (T₀ : ℝ)
    (hhigh : ∀ s : ℂ, completedRiemannZeta s = 0 → T₀ ≤ |s.im| → s.re ≤ 1 / 2)
    (hlow : ∀ s : ℂ, completedRiemannZeta s = 0 → |s.im| < T₀ → s.re ≤ 1 / 2) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_no_completed_zero_right]
  intro s hs
  rcases le_or_gt T₀ |s.im| with h | h
  · exact hhigh s hs h
  · exact hlow s hs h

end RiemannAnalytic
