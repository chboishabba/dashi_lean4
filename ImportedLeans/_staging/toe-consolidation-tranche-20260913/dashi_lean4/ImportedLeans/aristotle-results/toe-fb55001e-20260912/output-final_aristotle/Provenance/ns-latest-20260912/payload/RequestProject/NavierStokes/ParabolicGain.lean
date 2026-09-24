/-
# The three-dimensional parabolic `L^{10/3}` gain

`DeGiorgiRecurrence.lean` extracts the recurrence `Y_{n+1} ≤ C bⁿ Y_n^{1+2/5}`
from an energy/embedding input of the form

  `∫ ((w−k)²)^{5/3} ≤ C_S · (energy)^{5/3}`,

which is the `L^{10/3}` gain of the parabolic Sobolev embedding.  That input is
a hypothesis there.  This file proves the analytic inequality behind it, in
three dimensions, from Mathlib's Gagliardo–Nirenberg–Sobolev theorem.

* `ClayNS.sobolevConstE3` — the Gagliardo–Nirenberg–Sobolev constant of
  `ℝ³ = E3` at exponent `p = 2`, so `p' = 6`.
* `ClayNS.sobolev_L6_le` — `‖v‖_{L⁶} ≤ C‖∇v‖_{L²}` for `C¹` compactly supported
  `v : E3 → ℝ`.
* `ClayNS.interpolation_L10over3` — the Hölder interpolation
  `∫|v|^{10/3} ≤ (∫|v|⁶)^{1/3}(∫v²)^{2/3}` (conjugate pair `(3, 3/2)`).
* `ClayNS.parabolic_L10over3_gain` — the two combined:

  `∫_{ℝ³}|v|^{10/3} ≤ C²·(∫|∇v|²)·(∫v²)^{2/3}`.

* `ClayNS.parabolic_L10over3_gain_time` — the space-time form actually consumed
  by a De Giorgi iteration: with `sup_t ∫v(t)² ≤ S` on the time interval,

  `∫_a^b∫|v|^{10/3} ≤ C²·S^{2/3}·∫_a^b∫|∇v|²`,

  i.e. the `L^{10/3}` norm is controlled by the *parabolic energy* — the
  supremum of the `L²` mass times the dissipation.  This is exactly the gain
  whose exponent produces `α = 2/5` in the De Giorgi recurrence.

What remains between this and the hypothesis `hEmb` of
`ClayNS.deGiorgi_dyadic_recurrence` is the localized Caccioppoli bound
`sup_t ∫ (q−k_n)_+²Φ + ∫∫Φ|∇(q−k_n)_+|² ≲ 4ⁿ Y_n` for the increment density,
i.e. the level-set energy inequality for the Navier–Stokes carrier.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.DeGiorgiRecurrence
import RequestProject.NavierStokes.ClayPeriodic
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

open MeasureTheory ENNReal Module Set

open scoped NNReal

noncomputable section

namespace ClayNS

/-- The Gagliardo–Nirenberg–Sobolev constant for `E3 = ℝ³` at exponent `p = 2`
(so the target exponent is `p' = 6`). -/
def sobolevConstE3 : ℝ := (SNormLESNormFDerivOfEqConst ℝ (volume : Measure E3) 2 : ℝ)

lemma sobolevConstE3_nonneg : 0 ≤ sobolevConstE3 := NNReal.coe_nonneg _

/-- **Sobolev in three dimensions.**  `‖v‖_{L⁶(ℝ³)} ≤ C‖∇v‖_{L²(ℝ³)}` for
continuously differentiable compactly supported `v`. -/
theorem sobolev_L6_le (v : E3 → ℝ) (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v) :
    (∫ x, |v x| ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ sobolevConstE3 * (∫ x, ‖fderiv ℝ v x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hfr : finrank ℝ E3 = 3 := by simp [E3]
  have hkey := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (μ := (volume : Measure E3))
    (F := ℝ) hv hs (p := 2) (p' := 6) (by norm_num) (by rw [hfr]; norm_num)
    (by rw [hfr]; norm_num)
  push_cast at hkey
  have h1 : MemLp v 6 volume := (hv.continuous).memLp_of_hasCompactSupport (μ := volume) hs
  have h2 : MemLp (fderiv ℝ v) 2 volume :=
    (hv.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (μ := volume)
      (hs.fderiv (𝕜 := ℝ))
  rw [h1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    h2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hkey
  simp only [ENNReal.toReal_ofNat] at hkey
  set C : ℝ≥0 := SNormLESNormFDerivOfEqConst ℝ (volume : Measure E3) 2 with hC
  rw [show ((C : ℝ≥0∞)) = ENNReal.ofReal ((C : ℝ)) from (ENNReal.ofReal_coe_nnreal).symm,
    ← ENNReal.ofReal_mul (by positivity)] at hkey
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hkey
  simpa [Real.norm_eq_abs, one_div, sobolevConstE3, hC, Real.rpow_two] using h3

/-- **Hölder interpolation.**  `∫|v|^{10/3} ≤ (∫|v|⁶)^{1/3}(∫v²)^{2/3}`, from the
conjugate pair `(3, 3/2)` applied to `v²·|v|^{4/3}`. -/
theorem interpolation_L10over3 (v : E3 → ℝ) (hv : Continuous v) (hs : HasCompactSupport v) :
    (∫ x, |v x| ^ (10 / 3 : ℝ))
      ≤ (∫ x, |v x| ^ (6 : ℝ)) ^ (1 / 3 : ℝ) * (∫ x, (v x) ^ 2) ^ (2 / 3 : ℝ) := by
  have hconj : (3 : ℝ).HolderConjugate (3 / 2) := by constructor <;> norm_num
  set f : E3 → ℝ := fun x => (v x) ^ 2 with hf
  set g : E3 → ℝ := fun x => |v x| ^ (4 / 3 : ℝ) with hg
  have hfc : Continuous f := hv.pow 2
  have hgc : Continuous g := (continuous_abs.comp hv).rpow_const fun _ => Or.inr (by norm_num)
  have hfs : HasCompactSupport f := hs.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hgs : HasCompactSupport g := hs.comp_left (g := fun y : ℝ => |y| ^ (4 / 3 : ℝ)) (by simp)
  have hfm : MemLp f (ENNReal.ofReal (3 : ℝ)) volume := hfc.memLp_of_hasCompactSupport hfs
  have hgm : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := hgc.memLp_of_hasCompactSupport hgs
  have hfnn : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hgnn : 0 ≤ᵐ[volume] g :=
    Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hkey := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure E3))
    hconj hfnn hgnn hfm hgm
  have habs2 : ∀ x, (v x) ^ 2 = |v x| ^ (2 : ℝ) := fun x => by rw [Real.rpow_two, sq_abs]
  have e1 : ∀ x, f x * g x = |v x| ^ (10 / 3 : ℝ) := by
    intro x
    simp only [hf, hg]
    rw [habs2 x, ← Real.rpow_add' (abs_nonneg _) (by norm_num)]
    norm_num
  have e2 : ∀ x, f x ^ (3 : ℝ) = |v x| ^ (6 : ℝ) := by
    intro x
    simp only [hf]
    rw [habs2 x, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have e3 : ∀ x, g x ^ (3 / 2 : ℝ) = (v x) ^ 2 := by
    intro x
    simp only [hg]
    rw [← Real.rpow_mul (abs_nonneg _), habs2 x]
    norm_num
  simp only [e1, e2, e3] at hkey
  norm_num at hkey
  convert hkey using 3
  norm_num

/-- **The three-dimensional `L^{10/3}` gain.**

`∫_{ℝ³}|v|^{10/3} ≤ C²·(∫|∇v|²)·(∫v²)^{2/3}`. -/
theorem parabolic_L10over3_gain (v : E3 → ℝ) (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v) :
    (∫ x, |v x| ^ (10 / 3 : ℝ))
      ≤ sobolevConstE3 ^ 2 * (∫ x, ‖fderiv ℝ v x‖ ^ 2) * (∫ x, (v x) ^ 2) ^ (2 / 3 : ℝ) := by
  set X : ℝ := ∫ x, |v x| ^ (6 : ℝ) with hX
  set Y : ℝ := ∫ x, ‖fderiv ℝ v x‖ ^ 2 with hY
  have hX0 : 0 ≤ X := integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hY0 : 0 ≤ Y := integral_nonneg fun x => sq_nonneg _
  have hsob := sobolev_L6_le v hv hs
  -- square the Sobolev inequality
  have hsq : X ^ (1 / 3 : ℝ) ≤ sobolevConstE3 ^ 2 * Y := by
    have hlhs : X ^ (1 / 3 : ℝ) = (X ^ (1 / 6 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (X ^ (1 / 6 : ℝ)) 2, ← Real.rpow_mul hX0]
      norm_num
    have hrhs : (sobolevConstE3 * Y ^ (1 / 2 : ℝ)) ^ 2 = sobolevConstE3 ^ 2 * Y := by
      rw [mul_pow, ← Real.rpow_natCast (Y ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hY0]
      norm_num
    rw [hlhs, ← hrhs, sq, sq]
    exact mul_self_le_mul_self (Real.rpow_nonneg hX0 _) hsob
  have hZ0 : 0 ≤ (∫ x, (v x) ^ 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _
  calc (∫ x, |v x| ^ (10 / 3 : ℝ))
      ≤ X ^ (1 / 3 : ℝ) * (∫ x, (v x) ^ 2) ^ (2 / 3 : ℝ) :=
        interpolation_L10over3 v hv.continuous hs
    _ ≤ (sobolevConstE3 ^ 2 * Y) * (∫ x, (v x) ^ 2) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hsq hZ0

/-- **The space-time form.**  With the `L²` mass bounded by `S` on the time
interval, the parabolic `L^{10/3}` norm is controlled by `S^{2/3}` times the
total dissipation.  This is the shape of the energy/embedding input of the De
Giorgi recurrence. -/
theorem parabolic_L10over3_gain_time (V : ℝ → E3 → ℝ) {a b S : ℝ} (hab : a ≤ b)
    (hV : ∀ t, ContDiff ℝ 1 (V t)) (hs : ∀ t, HasCompactSupport (V t))
    (hS : ∀ t ∈ Icc a b, (∫ x, (V t x) ^ 2) ≤ S)
    (hint1 : IntervalIntegrable (fun t => ∫ x, |V t x| ^ (10 / 3 : ℝ)) volume a b)
    (hint2 : IntervalIntegrable (fun t => ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) volume a b) :
    (∫ t in a..b, ∫ x, |V t x| ^ (10 / 3 : ℝ))
      ≤ sobolevConstE3 ^ 2 * S ^ (2 / 3 : ℝ)
        * ∫ t in a..b, ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2 := by
  have hmono : ∀ t ∈ Icc a b,
      (∫ x, |V t x| ^ (10 / 3 : ℝ))
        ≤ (sobolevConstE3 ^ 2 * S ^ (2 / 3 : ℝ)) * (∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) := by
    intro t ht
    have hg := parabolic_L10over3_gain (V t) (hV t) (hs t)
    have hL2 : 0 ≤ ∫ x, (V t x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hSt : (∫ x, (V t x) ^ 2) ^ (2 / 3 : ℝ) ≤ S ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow hL2 (hS t ht) (by norm_num)
    have hY0 : 0 ≤ ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hcoef : 0 ≤ sobolevConstE3 ^ 2 * (∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) := by positivity
    refine hg.trans ?_
    calc sobolevConstE3 ^ 2 * (∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) * (∫ x, (V t x) ^ 2) ^ (2 / 3 : ℝ)
        ≤ sobolevConstE3 ^ 2 * (∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) * S ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hSt hcoef
      _ = (sobolevConstE3 ^ 2 * S ^ (2 / 3 : ℝ)) * (∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) := by ring
  have hmain := intervalIntegral.integral_mono_on hab hint1 (hint2.const_mul _) hmono
  rwa [intervalIntegral.integral_const_mul] at hmain

/-- **The embedding input of the De Giorgi recurrence.**  If the level-set
truncation `v` obeys the Caccioppoli bound `K` in *both* slots — the supremum in
time of the spatial `L²` mass and the total dissipation — then

`∫∫|v|^{10/3} ≤ C²·K^{5/3}`.

With `K = 4ⁿ Y_n` this is exactly the hypothesis `hEmb` of
`ClayNS.deGiorgi_dyadic_recurrence`, with `C_S = sobolevConstE3²`.  The only
remaining input on the C side is therefore the localized Caccioppoli bound
itself for the increment density. -/
theorem parabolic_gain_of_caccioppoli (V : ℝ → E3 → ℝ) {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hV : ∀ t, ContDiff ℝ 1 (V t)) (hs : ∀ t, HasCompactSupport (V t))
    (hSup : ∀ t ∈ Icc a b, (∫ x, (V t x) ^ 2) ≤ K)
    (hDiss : (∫ t in a..b, ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) ≤ K)
    (hint1 : IntervalIntegrable (fun t => ∫ x, |V t x| ^ (10 / 3 : ℝ)) volume a b)
    (hint2 : IntervalIntegrable (fun t => ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) volume a b) :
    (∫ t in a..b, ∫ x, |V t x| ^ (10 / 3 : ℝ)) ≤ sobolevConstE3 ^ 2 * K ^ (5 / 3 : ℝ) := by
  have hmain := parabolic_L10over3_gain_time V hab hV hs hSup hint1 hint2
  have hcoef : 0 ≤ sobolevConstE3 ^ 2 * K ^ (2 / 3 : ℝ) := by
    have : 0 ≤ K ^ (2 / 3 : ℝ) := Real.rpow_nonneg hK _
    positivity
  have hstep : sobolevConstE3 ^ 2 * K ^ (2 / 3 : ℝ)
      * (∫ t in a..b, ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2)
      ≤ sobolevConstE3 ^ 2 * K ^ (2 / 3 : ℝ) * K :=
    mul_le_mul_of_nonneg_left hDiss hcoef
  have hpow : K ^ (2 / 3 : ℝ) * K = K ^ (5 / 3 : ℝ) := by
    nth_rewrite 2 [← Real.rpow_one K]
    rw [← Real.rpow_add' hK (by norm_num)]
    norm_num
  calc (∫ t in a..b, ∫ x, |V t x| ^ (10 / 3 : ℝ))
      ≤ sobolevConstE3 ^ 2 * K ^ (2 / 3 : ℝ)
          * (∫ t in a..b, ∫ x, ‖fderiv ℝ (V t) x‖ ^ 2) := hmain
    _ ≤ sobolevConstE3 ^ 2 * K ^ (2 / 3 : ℝ) * K := hstep
    _ = sobolevConstE3 ^ 2 * K ^ (5 / 3 : ℝ) := by rw [mul_assoc, hpow]

end ClayNS
