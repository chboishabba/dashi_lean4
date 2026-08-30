/-
# Row A1a — the split radius is not fine-tuned

The near/far split radius used by the shell budget is `r = 2/5`.  This file
shows that nothing depends on that exact value: with the *radius-dependent* far
denominator floor coming from Jordan's inequality,

    |p_μ| ≥ r  ⟹  p̂_μ² ≥ 16 r²,

the far per-orbit bound at radius `r` is `1/(16 r²)` for a unit numerator, and
the resulting total split cost

    splitCostGeneral r = r⁴ · 15 · (2/5) + (1/16 − r⁴) · 15/(16 r²)

stays strictly below the shell budget `11/12` for *every* radius in
`[1/4, 1/2]`.  At `r = 2/5` one has `16 r² = 64/25`, so this cost coincides with
`ShellBudget.splitCost (2/5) = 236679/640000 = 0.3698…`.
-/
import RequestProject.YangMills.ShellBudget

namespace YangMills

/-! ## 1. Radius-dependent far floor -/

/-- Jordan's inequality at an arbitrary radius: an axis at distance at least `r`
from the origin floors its own contribution to `p̂²` by `16 r²`. -/
theorem phat_sq_ge_of_radius {x r : ℝ} (hr : 0 ≤ r) (h : r ≤ |x|) (h' : |x| ≤ 1 / 2) :
    16 * r ^ 2 ≤ (phat x) ^ 2 := by
  have habs : 2 * |x| ≤ |sinAtom x| := by
    rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
    · have h0 : (0:ℝ) ≤ x := by rw [hx] at h; linarith
      have h1 : x ≤ 1 / 2 := by rw [hx] at h'; linarith
      have hj := two_mul_le_sinAtom h0 h1
      rw [abs_of_nonneg (sinAtom_nonneg h0 h1), hx]
      linarith
    · have hx' : |x| = -x := hx
      have h0 : (0:ℝ) ≤ -x := by rw [hx'] at h; linarith
      have h1 : -x ≤ 1 / 2 := by rw [hx'] at h'; linarith
      have hj := two_mul_le_sinAtom h0 h1
      have hnn : 0 ≤ sinAtom (-x) := sinAtom_nonneg h0 h1
      rw [sinAtom_neg] at hj hnn
      rw [abs_of_nonpos (by linarith : sinAtom x ≤ 0), hx']
      linarith
  have hrx : 2 * r ≤ 2 * |x| := by linarith
  have hlow : 2 * r ≤ |sinAtom x| := le_trans hrx habs
  have hsq : (2 * r) ^ 2 ≤ |sinAtom x| ^ 2 := by nlinarith [abs_nonneg (sinAtom x)]
  rw [phat_sq_eq, ← sq_abs (sinAtom x)]
  nlinarith [abs_nonneg (sinAtom x)]

/-- The far denominator floor at an arbitrary radius. -/
theorem phatSq_floor_far_radius {p : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hBZ : InBZ p) (hfar : FarRegion r p) : 16 * r ^ 2 ≤ phatSq p := by
  obtain ⟨μ, hμ⟩ := hfar
  exact le_trans (phat_sq_ge_of_radius hr hμ (hBZ μ)) (phat_sq_le_phatSq p μ)

/-- The far per-orbit quotient bound at an arbitrary radius, unit numerator. -/
theorem far_quotient_bound_radius {p : Fin 4 → ℝ} {N r : ℝ} (hr : 0 < r)
    (hBZ : InBZ p) (hfar : FarRegion r p) (hN : |N| ≤ 1) :
    |N / phatSq p| ≤ 1 / (16 * r ^ 2) := by
  have hfloor : 16 * r ^ 2 ≤ phatSq p := phatSq_floor_far_radius hr.le hBZ hfar
  have hpos : (0:ℝ) < phatSq p := lt_of_lt_of_le (by positivity) hfloor
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  nlinarith [hN, hfloor, abs_nonneg N]

/-- **The radius-dependent floor is attained at the zone boundary.**  At
`|x| = 1/2` one has `p̂² = 4 = 16 · (1/2)²`, so `phat_sq_ge_of_radius` is sharp
there and no larger constant than `16 r²` is available in general. -/
theorem phat_sq_eq_at_zone_boundary : (phat (1 / 2)) ^ 2 = 16 * (1 / 2 : ℝ) ^ 2 := by
  have h : sinAtom (1 / 2) = 1 := by
    rw [sinAtom, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [phat_sq_eq, h]
  norm_num

/-! ## 2. The split cost as a function of the radius -/

/-- The near/far split cost at radius `r`, with the near per-orbit bound `2/5`
and the radius-dependent far per-orbit bound `1/(16 r²)`. -/
noncomputable def splitCostGeneral (r : ℝ) : ℝ :=
  r ^ 4 * (15 * (2 / 5)) + (1 / 16 - r ^ 4) * (15 / (16 * r ^ 2))

/-- The auxiliary cubic that controls the split cost. -/
lemma splitCost_cubic_neg {t : ℝ} (h1 : 1 / 16 ≤ t) (h2 : t ≤ 1 / 4) :
    96 * t ^ 3 - 15 * t ^ 2 - (44 / 3) * t + 15 / 16 < 0 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 1/16) (by linarith : (0:ℝ) ≤ 1/4 - t),
    sq_nonneg t, sq_nonneg (t - 1/16),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ t - 1/16)
      (by linarith : (0:ℝ) ≤ t - 1/16)) (by linarith : (0:ℝ) ≤ 1/4 - t)]

/-- **The split radius is not fine-tuned.**  For every radius in `[1/4, 1/2]`
the split cost stays strictly inside the shell budget `11/12`. -/
theorem splitCostGeneral_lt_budget {r : ℝ} (h1 : 1 / 4 ≤ r) (h2 : r ≤ 1 / 2) :
    splitCostGeneral r < shellBudgetSU2 := by
  have hr : (0:ℝ) < r := by linarith
  have hcube := splitCost_cubic_neg (t := r ^ 2) (by nlinarith) (by nlinarith)
  have hden : (0:ℝ) < 16 * r ^ 2 := by positivity
  unfold splitCostGeneral shellBudgetSU2
  rw [← sub_pos]
  have hkey : 11 / 12 - (r ^ 4 * (15 * (2 / 5)) + (1 / 16 - r ^ 4) * (15 / (16 * r ^ 2)))
      = -(96 * (r ^ 2) ^ 3 - 15 * (r ^ 2) ^ 2 - (44 / 3) * (r ^ 2) + 15 / 16)
        / (16 * r ^ 2) := by
    field_simp
    ring
  rw [hkey]
  exact div_pos (by linarith) hden

/-- At the working radius `r = 2/5` the radius-dependent floor `16 r² = 64/25`
coincides with the fixed floor used in `ShellBudget`, so the two split costs
agree: `236679/640000 = 0.3698…`. -/
theorem splitCostGeneral_two_fifths :
    splitCostGeneral (2 / 5) = splitCost (2 / 5) := by
  unfold splitCost combinedOfPerOrbit perOrbitNearBound perOrbitFarBound
  unfold splitCostGeneral
  norm_num

end YangMills
