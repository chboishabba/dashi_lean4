/-
# The two-regime envelope, and why a minimum-gap hypothesis is not needed

A transverse decay estimate of the shape `|Φ(x)| ≤ K₁ / |x|` is singular at
`x = 0`, so summing it over a family of points forces an artificial hypothesis
"all points are at least `δ` apart".  The fix is to prove the *two-regime*
envelope

    |Φ(x)| ≤ min (K₀, K₁ / |x|),

which is bounded everywhere, and then to sum using **local counts** instead of a
uniform separation.

This file does both, in general form.

* `Spine.TwoRegime.norm_fourier_le_L1` and
  `Spine.TwoRegime.freq_mul_norm_fourier_le` — the two regimes for a Fourier
  transform: the `L¹` bound of `f`, and the integration-by-parts bound
  `2π|ξ| ‖𝓕 f ξ‖ ≤ ‖f'‖₁`.
* `Spine.TwoRegime.norm_fourier_le_envelope` — their combination: for `ξ ≠ 0`,
  `‖𝓕 f ξ‖ ≤ min (‖f‖₁, ‖f'‖₁ / (2π|ξ|))`.
* `Spine.TwoRegime.sum_envelope_le` — the summation theorem with **no separation
  hypothesis**: if a finite set of points has at most `N` members in each unit
  window `⌊|x|⌋ = m` and all lie in `|x| < M`, then the envelope sums to at most
  `N·K₀ + N·K₁·∑_{m=1}^{M-1} 1/m`.
* `Spine.TwoRegime.single_regime_unbounded` — the honest reason the first regime
  is needed: `K₁/|x|` alone is unbounded near `0`, so the one-regime estimate
  cannot be summed without assuming a gap.

Nothing here is a statement about the zeros of any `L`-function; these are
general facts about Fourier transforms and about summing an envelope.
-/
import Mathlib

open MeasureTheory Real Complex Finset
open scoped FourierTransform

namespace Spine
namespace TwoRegime

/-! ## Regime 1: the `L¹` bound -/

/-- The uniform bound: `‖𝓕 f ξ‖ ≤ ‖f‖₁`. -/
theorem norm_fourier_le_L1 (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  show ‖VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f ξ‖ ≤ _
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-! ## Regime 2: the integration-by-parts bound -/

/-- The decay bound: `2π|ξ| ‖𝓕 f ξ‖ ≤ ‖f'‖₁`. -/
theorem freq_mul_norm_fourier_le {f : ℝ → ℂ} (hf : Integrable f) (hd : Differentiable ℝ f)
    (hf' : Integrable (deriv f)) (ξ : ℝ) :
    2 * π * |ξ| * ‖𝓕 f ξ‖ ≤ ∫ x, ‖deriv f x‖ := by
  have h := congrFun (Real.fourier_deriv hf hd hf') ξ
  have h2 : ‖𝓕 (deriv f) ξ‖ ≤ ∫ x, ‖deriv f x‖ := norm_fourier_le_L1 _ _
  rw [h, smul_eq_mul, norm_mul] at h2
  have hn : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
    simp [abs_of_nonneg Real.pi_nonneg]
  rw [hn] at h2
  exact h2

/-- **The two-regime envelope.**  Away from the origin both regimes apply, so the
transform is bounded by their minimum — an estimate that stays finite as `ξ → 0`,
unlike `K₁/|ξ|` alone. -/
theorem norm_fourier_le_envelope {f : ℝ → ℂ} (hf : Integrable f) (hd : Differentiable ℝ f)
    (hf' : Integrable (deriv f)) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ min (∫ x, ‖f x‖) ((∫ x, ‖deriv f x‖) / (2 * π * |ξ|)) := by
  refine le_min (norm_fourier_le_L1 _ _) ?_
  have hpos : 0 < 2 * π * |ξ| := by
    have : 0 < |ξ| := abs_pos.mpr hξ
    have := Real.pi_pos
    positivity
  rw [le_div_iff₀ hpos]
  have := freq_mul_norm_fourier_le hf hd hf' ξ
  linarith [this]

/-! ## Summing the envelope with local counts only -/

/-- The two-regime envelope as a function. -/
noncomputable def envelope (K₀ K₁ x : ℝ) : ℝ := min K₀ (K₁ / |x|)

theorem envelope_le_left (K₀ K₁ x : ℝ) : envelope K₀ K₁ x ≤ K₀ := min_le_left _ _

theorem envelope_le_right (K₀ K₁ x : ℝ) : envelope K₀ K₁ x ≤ K₁ / |x| := min_le_right _ _

theorem envelope_nonneg {K₀ K₁ x : ℝ} (h₀ : 0 ≤ K₀) (h₁ : 0 ≤ K₁) : 0 ≤ envelope K₀ K₁ x :=
  le_min h₀ (by positivity)

/-- **The honest reason the first regime is needed.**  The one-regime estimate
`K₁/|x|` is unbounded near the origin, so summing it over points that may cluster
requires a minimum-gap hypothesis. -/
theorem single_regime_unbounded {K₁ : ℝ} (hK₁ : 0 < K₁) (C : ℝ) :
    ∃ x : ℝ, x ≠ 0 ∧ C < K₁ / |x| := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0 / K₁)
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  refine ⟨1 / (n + 1), by positivity, ?_⟩
  have habs : |1 / ((n : ℝ) + 1)| = 1 / (n + 1) := abs_of_pos (by positivity)
  have hdiv : K₁ / (1 / ((n : ℝ) + 1)) = K₁ * ((n : ℝ) + 1) := by field_simp
  rw [habs, hdiv]
  have hC : C ≤ max C 0 := le_max_left _ _
  have : max C 0 / K₁ < n + 1 := by linarith
  have : max C 0 < K₁ * (n + 1) := by
    rw [div_lt_iff₀ hK₁] at this; linarith [this]
  calc C ≤ max C 0 := hC
  _ < K₁ * (n + 1) := this
  _ = K₁ * ((n : ℝ) + 1) := rfl

/-- **The summation theorem, with no separation hypothesis.**  If each unit
window `⌊|x|⌋ = m` contains at most `N` of the points and all points satisfy
`|x| < M`, the two-regime envelope sums to at most
`N·K₀ + N·K₁·∑_{m=1}^{M-1} 1/m`.  Nothing about the minimal distance between
points is assumed. -/
theorem sum_envelope_le {K₀ K₁ : ℝ} (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (S : Finset ℝ) (N M : ℕ)
    (hM : ∀ x ∈ S, |x| < M)
    (hcount : ∀ m : ℕ, ((S.filter (fun x => ⌊|x|⌋₊ = m)).card : ℝ) ≤ N) :
    ∑ x ∈ S, envelope K₀ K₁ x ≤ N * K₀ + N * K₁ * ∑ m ∈ Finset.Ico 1 M, (1 : ℝ) / m := by
  classical
  have hmaps : ∀ x ∈ S, ⌊|x|⌋₊ ∈ Finset.range M := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.floor_lt (abs_nonneg x) |>.mpr (hM x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- bound each fibre
  have hfib : ∀ m ∈ Finset.range M,
      ∑ x ∈ S.filter (fun x => ⌊|x|⌋₊ = m), envelope K₀ K₁ x
        ≤ (N : ℝ) * (if m = 0 then K₀ else K₁ / m) := by
    intro m _
    have hb : ∀ x ∈ S.filter (fun x => ⌊|x|⌋₊ = m),
        envelope K₀ K₁ x ≤ (if m = 0 then K₀ else K₁ / m) := by
      intro x hx
      by_cases hm : m = 0
      · subst hm; simp only [if_true]; exact envelope_le_left _ _ _
      · simp only [if_neg hm]
        have hfl : ⌊|x|⌋₊ = m := (Finset.mem_filter.mp hx).2
        have hmle : (m : ℝ) ≤ |x| := by
          rw [← hfl]; exact Nat.floor_le (abs_nonneg x)
        have hmpos : (0 : ℝ) < m := by
          have : 0 < m := Nat.pos_of_ne_zero hm
          exact_mod_cast this
        refine le_trans (envelope_le_right _ _ _) ?_
        exact div_le_div_of_nonneg_left hK₁ hmpos hmle
    calc ∑ x ∈ S.filter (fun x => ⌊|x|⌋₊ = m), envelope K₀ K₁ x
        ≤ ∑ _x ∈ S.filter (fun x => ⌊|x|⌋₊ = m), (if m = 0 then K₀ else K₁ / m) :=
          Finset.sum_le_sum hb
      _ = ((S.filter (fun x => ⌊|x|⌋₊ = m)).card : ℝ) * (if m = 0 then K₀ else K₁ / m) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (if m = 0 then K₀ else K₁ / m) := by
          have hnn : (0 : ℝ) ≤ (if m = 0 then K₀ else K₁ / m) := by
            by_cases hm : m = 0
            · simp [hm, hK₀]
            · simp only [if_neg hm]; positivity
          exact mul_le_mul_of_nonneg_right (hcount m) hnn
  refine le_trans (Finset.sum_le_sum hfib) ?_
  -- split off the `m = 0` term
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0; simp
    positivity
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hMpos]
    have hrest : ∑ m ∈ Finset.Ico 1 M, (N : ℝ) * (if m = 0 then K₀ else K₁ / m)
        = (N : ℝ) * K₁ * ∑ m ∈ Finset.Ico 1 M, (1 : ℝ) / m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : m ≠ 0 := by
        have := (Finset.mem_Ico.mp hm).1; omega
      simp only [if_neg hm0]
      ring
    rw [hrest]
    simp

end TwoRegime
end Spine
