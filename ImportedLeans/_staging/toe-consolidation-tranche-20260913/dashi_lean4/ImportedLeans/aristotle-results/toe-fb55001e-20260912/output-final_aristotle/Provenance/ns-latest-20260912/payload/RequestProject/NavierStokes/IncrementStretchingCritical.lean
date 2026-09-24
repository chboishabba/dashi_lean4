/-
# The increment stretching term at the critical exponent, and why it is not enough

For the quadratic De Giorgi entropy `β_k(q) = v_k²`, `v_k = (q−k)_+`, one has
`β_k'(q) = 2v_k`, and the surviving interior source of the localized increment
inequality is the stretching contribution

  `𝒮_k = 2 ∬ Φ v_k (δ_h U)ᵀ S(U) δ_h U`.

Under the KNSŠ normalization `‖U‖_∞ ≤ 1` one has `q = ½|δ_hU|² ≤ 2`, hence
`|(δ_hU)ᵀ S δ_hU| ≤ |S||δ_hU|² = 2q|S| ≤ 4|S|`, so

  `|𝒮_k| ≤ 8 ∬_{A_k} Φ |S| v_k`.                                   (pointwise)

The **exact critical Hölder triple** in `3+1` parabolic dimensions is

  `1/(5/2) + 1/(10/3) + 1/(10/3) = 1`,

giving

  `|𝒮_k| ≤ 8 ‖S‖_{L^{5/2}(Q_k)} ‖v_k‖_{L^{10/3}(Q_k)} |A_k|^{3/10}`.   (C-S)

This file proves both, `critical_holder_triple` /
`increment_stretching_critical_estimate` being the general measure-theoretic
form of (C-S) and `incrStretch_truncation_abs_le` the pointwise input in the
project's increment carrier.

**And then it proves the negative half.**  Feeding `‖v_k‖_{10/3} ≲ K_k^{1/2}`
and Chebyshev into (C-S) and applying Young produces a source of size
`Y_k^{3/5}` — *sublinear* in the truncation energy.  A recurrence
`Y_{n+1} ≤ C bⁿ Y_n^θ` with `θ < 1` does **not** force decay:
`sublinear_recurrence_no_decay` exhibits, for every `C > 0`, `b ≥ 1` and
`θ ∈ [0,1)`, a strictly positive constant sequence satisfying it.  (Contrast
`deGiorgi_fast_convergence`, which does close for `θ = 1 + α`.)  So a generic
critical-`L^{5/2}` bound on the strain, with no smallness and no extra
level-set factor, cannot generate the De Giorgi recurrence: the cut is

  *pressure is no longer C's critical obstruction; the linear-in-truncation
  stretching source is.*

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLocalEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

namespace ClayNS

/-! ## The parabolic critical Hölder triple `(5/2, 10/3, 10/3)` -/

instance holderTriple_five_halves : ENNReal.HolderTriple (5 / 2) (10 / 3) (10 / 7) := by
  constructor
  rw [show ((5:ℝ≥0∞)/2)⁻¹ = 2/5 by rw [ENNReal.inv_div] <;> simp,
      show ((10:ℝ≥0∞)/3)⁻¹ = 3/10 by rw [ENNReal.inv_div] <;> simp,
      show ((10:ℝ≥0∞)/7)⁻¹ = 7/10 by rw [ENNReal.inv_div] <;> simp,
      show (2:ℝ≥0∞)/5 = 4/10 by rw [ENNReal.div_eq_div_iff] <;> norm_num,
      ENNReal.div_add_div_same]
  norm_num

instance holderTriple_ten_thirds : ENNReal.HolderTriple (10 / 3) (10 / 7) 1 := by
  constructor
  rw [show ((10:ℝ≥0∞)/3)⁻¹ = 3/10 by rw [ENNReal.inv_div] <;> simp,
      show ((10:ℝ≥0∞)/7)⁻¹ = 7/10 by rw [ENNReal.inv_div] <;> simp,
      ENNReal.div_add_div_same]
  rw [show (3:ℝ≥0∞) + 7 = 10 by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]
  simp

variable {α : Type*} [MeasurableSpace α]

/-- **The critical Hölder triple.**  On any measure space, for the exponent
triple `1/(5/2) + 1/(10/3) + 1/(10/3) = 1`,

`∫_A |S · v| ≤ ‖S‖_{5/2} ‖v‖_{10/3} μ(A)^{3/10}`.

This is the exponent arithmetic behind (C-S): `5/2` is the parabolic critical
exponent for a potential in `3+1` dimensions, exactly dual to the `L^{10/3}`
gain. -/
theorem critical_holder_triple (μ : Measure α) {S v : α → ℝ} {A : Set α}
    (hA : MeasurableSet A) (hS : AEStronglyMeasurable S μ) (hv : AEStronglyMeasurable v μ) :
    (∫⁻ x in A, ‖S x‖ₑ * ‖v x‖ₑ ∂μ)
      ≤ eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ * μ A ^ (3 / 10 : ℝ) := by
  classical
  set g : α → ℝ := A.indicator (fun _ => (1 : ℝ)) with hg
  have hgmeas : AEStronglyMeasurable g μ :=
    (aestronglyMeasurable_const.indicator hA)
  -- the product `S · v`
  have hSv : eLpNorm (fun x => S x * v x) (10 / 7) μ
      ≤ eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ := by
    have := eLpNorm_smul_le_mul_eLpNorm (p := 5 / 2) (q := 10 / 3) (r := 10 / 7)
      (f := v) (φ := S) hv hS
    simpa [Pi.smul_apply, smul_eq_mul] using this
  -- and its product with the indicator
  have hprod : eLpNorm (fun x => g x * (S x * v x)) 1 μ
      ≤ eLpNorm g (10 / 3) μ * eLpNorm (fun x => S x * v x) (10 / 7) μ := by
    have := eLpNorm_smul_le_mul_eLpNorm (p := 10 / 3) (q := 10 / 7) (r := 1)
      (f := fun x => S x * v x) (φ := g) (hS.mul hv) hgmeas
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have hgnorm : eLpNorm g (10 / 3) μ = μ A ^ (3 / 10 : ℝ) := by
    have hne : ((10:ℝ≥0∞)/3) ≠ ∞ := by simp [ENNReal.div_eq_top]
    rw [hg, eLpNorm_indicator_const hA (by norm_num) hne,
      show ((10:ℝ≥0∞)/3).toReal = 10 / 3 by simp [ENNReal.toReal_div]]
    norm_num
  have hlhs : (∫⁻ x in A, ‖S x‖ₑ * ‖v x‖ₑ ∂μ) = eLpNorm (fun x => g x * (S x * v x)) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · simp [hg, Set.indicator_of_mem hx, enorm_mul]
    · simp [hg, Set.indicator_of_notMem hx]
  calc (∫⁻ x in A, ‖S x‖ₑ * ‖v x‖ₑ ∂μ)
      = eLpNorm (fun x => g x * (S x * v x)) 1 μ := hlhs
    _ ≤ eLpNorm g (10 / 3) μ * eLpNorm (fun x => S x * v x) (10 / 7) μ := hprod
    _ ≤ μ A ^ (3 / 10 : ℝ) * (eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ) := by
        rw [hgnorm]; gcongr
    _ = eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ * μ A ^ (3 / 10 : ℝ) := by ring

/-- **`IncrementStretchingCriticalEstimate` (C-S).**  Any source whose
integrand is pointwise dominated by `8|S||v|` on the level set `A` obeys the
critical estimate

`|𝒮| ≤ 8 ‖S‖_{L^{5/2}} ‖v‖_{L^{10/3}} |A|^{3/10}`. -/
theorem increment_stretching_critical_estimate (μ : Measure α) {Str S v : α → ℝ} {A : Set α}
    (hA : MeasurableSet A) (hS : AEStronglyMeasurable S μ) (hv : AEStronglyMeasurable v μ)
    (hbound : ∀ x, |Str x| ≤ 8 * (|S x| * |v x|)) :
    (∫⁻ x in A, ‖Str x‖ₑ ∂μ)
      ≤ 8 * (eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ * μ A ^ (3 / 10 : ℝ)) := by
  have hpt : ∀ x, ‖Str x‖ₑ ≤ 8 * (‖S x‖ₑ * ‖v x‖ₑ) := by
    intro x
    have h := hbound x
    have h1 : ‖Str x‖ₑ ≤ ENNReal.ofReal (8 * (|S x| * |v x|)) := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal h
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (abs_nonneg _),
      Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    simp
  calc (∫⁻ x in A, ‖Str x‖ₑ ∂μ)
      ≤ ∫⁻ x in A, 8 * (‖S x‖ₑ * ‖v x‖ₑ) ∂μ := lintegral_mono hpt
    _ = 8 * ∫⁻ x in A, ‖S x‖ₑ * ‖v x‖ₑ ∂μ := by rw [lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 8 * (eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ * μ A ^ (3 / 10 : ℝ)) := by
        gcongr
        exact critical_holder_triple μ hA hS hv

/-! ## The pointwise input: the KNSŠ normalization gives the factor `8` -/

/-- **The truncated, localized stretching integrand.**  With `0 ≤ Φ ≤ 1`, a
nonnegative truncation `v_k`, the KNSŠ normalization `q ≤ 2` and a pointwise
strain magnitude `Sn` (i.e. `|δ_hU ᵀ S δ_hU| ≤ Sn·2q`), the integrand of `𝒮_k`
obeys `|2Φ v_k · stretching| ≤ 8 Sn v_k`.  This is the pointwise half of
(C-S). -/
theorem incrStretch_truncation_abs_le {Phi vk Sn q Str : ℝ} (hPhi0 : 0 ≤ Phi) (hPhi1 : Phi ≤ 1)
    (hvk : 0 ≤ vk) (hSn : 0 ≤ Sn) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hStr : |Str| ≤ Sn * (2 * q)) :
    |2 * Phi * vk * Str| ≤ 8 * (Sn * vk) := by
  have h1 : |2 * Phi * vk * Str| = (2 * Phi * vk) * |Str| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Phi * vk)]
  rw [h1]
  have h2 : (2 * Phi * vk) * |Str| ≤ (2 * Phi * vk) * (Sn * (2 * q)) :=
    mul_le_mul_of_nonneg_left hStr (by positivity)
  refine h2.trans ?_
  have h3 : Sn * (2 * q) ≤ Sn * 4 := by nlinarith
  nlinarith [mul_nonneg hSn hvk, mul_nonneg (mul_nonneg hSn hvk) hq0]

/-- The strain-magnitude hypothesis of `incrStretch_truncation_abs_le` is
supplied by the project's entrywise bound: with `|∂_i u_a| ≤ K` one has
`|δ_hu·(δ_hu·∇)u| ≤ 3K·(2q)`. -/
theorem incrStretch_abs_le_quad (h : E3) (V : STime → E3) (z : STime) (K : ℝ)
    (hK : ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) z| ≤ K) :
    |incrStretch h V z| ≤ (3 * K) * (2 * incrQuad h V z) := by
  have h1 := incrStretch_abs_le h V z K hK
  rwa [sum_sq_incrComp] at h1

/-! ## The negative half: a sublinear source cannot drive a De Giorgi cascade -/

/-- **Sublinear recurrences do not decay.**  For every `C > 0`, `b ≥ 1` and
exponent `θ ∈ [0,1)` there is a strictly positive constant sequence with
`Y_{n+1} ≤ C bⁿ Y_n^θ` which does not tend to `0`.  Hence the `Y_k^{3/5}`
source produced by (C-S) + Chebyshev + Young is *not* enough to run the De
Giorgi iteration: an extra level-set factor (or scale-uniform smallness of the
critical strain norm) is genuinely required. -/
theorem sublinear_recurrence_no_decay {C b theta : ℝ} (hC : 0 < C) (hb : 1 ≤ b)
    (hth1 : theta < 1) :
    ∃ Y : ℕ → ℝ, (∀ n, 0 < Y n) ∧ (∀ n, Y (n + 1) ≤ C * b ^ n * (Y n) ^ theta) ∧
      ¬ Tendsto Y atTop (𝓝 0) := by
  set L : ℝ := min 1 (C ^ (1 / (1 - theta))) with hL
  have hCpow : 0 < C ^ (1 / (1 - theta)) := Real.rpow_pos_of_pos hC _
  have hLpos : 0 < L := lt_min one_pos hCpow
  have hkey : L ^ (1 - theta) ≤ C := by
    have hmono : L ^ (1 - theta) ≤ (C ^ (1 / (1 - theta))) ^ (1 - theta) :=
      Real.rpow_le_rpow (le_of_lt hLpos) (min_le_right _ _) (by linarith)
    have hcalc : (C ^ (1 / (1 - theta))) ^ (1 - theta) = C := by
      rw [← Real.rpow_mul (le_of_lt hC), one_div,
        inv_mul_cancel₀ (by linarith : (1 : ℝ) - theta ≠ 0), Real.rpow_one]
    rw [hcalc] at hmono
    exact hmono
  refine ⟨fun _ => L, fun _ => hLpos, fun n => ?_, ?_⟩
  · have hstep : L ≤ C * L ^ theta := by
      have hsplit : L ^ (1 - theta) * L ^ theta = L := by
        rw [← Real.rpow_add hLpos]; simp
      have hpow : 0 < L ^ theta := Real.rpow_pos_of_pos hLpos _
      calc L = L ^ (1 - theta) * L ^ theta := hsplit.symm
        _ ≤ C * L ^ theta := mul_le_mul_of_nonneg_right hkey (le_of_lt hpow)
    have hbn : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb
    have hpow : 0 < L ^ theta := Real.rpow_pos_of_pos hLpos _
    calc L ≤ C * L ^ theta := hstep
      _ ≤ C * b ^ n * L ^ theta := by nlinarith [mul_pos hC hpow]
  · intro hcon
    have hconst : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := tendsto_const_nhds
    have := tendsto_nhds_unique hcon hconst
    exact absurd this.symm (ne_of_gt hLpos)

/-- The instance actually produced by the critical estimate: exponent `3/5`. -/
theorem critical_strain_recurrence_insufficient {C b : ℝ} (hC : 0 < C) (hb : 1 ≤ b) :
    ∃ Y : ℕ → ℝ, (∀ n, 0 < Y n) ∧ (∀ n, Y (n + 1) ≤ C * b ^ n * (Y n) ^ (3 / 5 : ℝ)) ∧
      ¬ Tendsto Y atTop (𝓝 0) :=
  sublinear_recurrence_no_decay hC hb (by norm_num)

end ClayNS
