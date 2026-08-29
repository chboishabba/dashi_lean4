/-
A quantitative envelope for the complex-`Φ` mixed interference kernel.

`KernelChannels.lean` identifies the two interference channels of a pair of
hypothetical zeros with the complex kernel `Φ = PhiExt (φ²)` and proves the
horizontal decay `|Φ(w)| ≤ M / |Re w|`.  Here that decay is summed over a
frequency-separated family of zeros: if the ordinate differences of the other
zeros from the target satisfy `δ|k| ≤ |Re w_k|` (a `δ`-separation condition,
with `k` enumerating the family) and their transverse offsets stay within the
critical strip so that `|Im w_k| ≤ 1`, then

  `∑_{k ≠ 0} (Im Φ(w_k))² ≤ 4 M² / δ²`,

with `M = ∫ |(φ²)'(u)| e^{|u|} du` an explicit constant depending only on the
taper.  This is a genuinely quantitative envelope, not merely a summability
statement: the bound is uniform in the family and explicit in `δ` and `M`.
-/
import RiemannAnalytic.KernelChannels
import RiemannAnalytic.GridTail

namespace RiemannAnalytic

open MeasureTheory Complex

/-! ### The uniform kernel mass -/

/-- The `L¹` mass of the derivative of the squared taper against `e^{|u|}`:
the uniform constant in the horizontal decay of the kernel on the strip
`|Im| ≤ 1`. -/
noncomputable def kernelMass (φ : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, |deriv (fun t => φ t ^ 2) u| * Real.exp |u|

theorem kernelMass_nonneg (φ : ℝ → ℝ) : 0 ≤ kernelMass φ :=
  integral_nonneg fun u => by positivity

/-- The absolute derivative of a `C¹` taper against any continuous weight is
integrable. -/
theorem C1Taper.integrable_absDeriv_mul {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun u => |deriv φ u| * g u) := by
  refine (hφ.contDeriv.abs.mul hg).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun x hx => ?_
  have hR : R < |x| := by
    rcases lt_or_ge R |x| with h | h
    · exact h
    · exact absurd (Set.mem_Icc.2 ⟨by cases abs_le.1 h with | intro h1 _ => linarith,
        by cases abs_le.1 h with | intro _ h2 => linarith⟩) hx
  simp [hφ.derivSupp x hR]

/-- On the strip `|y| ≤ 1` the twisted derivative mass of the squared taper is
bounded by `kernelMass`. -/
theorem derivMass_sq_le_kernelMass {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {y : ℝ}
    (hy : |y| ≤ 1) :
    ∫ u : ℝ, |deriv (fun t => φ t ^ 2) u| * Real.exp (y * u) ≤ kernelMass φ := by
  have hint₁ : Integrable fun u : ℝ => |deriv (fun t => φ t ^ 2) u| * Real.exp (y * u) :=
    hφ.sq.integrable_absDeriv_mul (by fun_prop)
  have hint₂ : Integrable fun u : ℝ => |deriv (fun t => φ t ^ 2) u| * Real.exp |u| :=
    hφ.sq.integrable_absDeriv_mul (by fun_prop)
  refine integral_mono hint₁ hint₂ fun u => ?_
  have hexp : Real.exp (y * u) ≤ Real.exp |u| := by
    refine Real.exp_le_exp.2 ?_
    calc y * u ≤ |y * u| := le_abs_self _
      _ = |y| * |u| := abs_mul y u
      _ ≤ 1 * |u| := by
          have : (0 : ℝ) ≤ |u| := abs_nonneg u
          nlinarith
      _ = |u| := one_mul _
  exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)

/-- **Uniform horizontal decay of the kernel on the strip `|Im| ≤ 1`.** -/
theorem abs_im_PhiKernel_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {w : ℂ}
    (hw : w.re ≠ 0) (hy : |w.im| ≤ 1) :
    |(PhiExt (fun t => φ t ^ 2) w).im| ≤ kernelMass φ / |w.re| := by
  refine le_trans (abs_PhiKernel_im_le_of_re hφ hw) ?_
  have hpos : 0 < |w.re| := abs_pos.2 hw
  have hnum := derivMass_sq_le_kernelMass hφ hy
  gcongr

/-! ### The two-sided inverse-square lattice sum -/

theorem summable_int_inv_sq : Summable fun k : ℤ => (1 : ℝ) / ((k : ℝ)) ^ 2 := by
  have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  refine Summable.of_nat_of_neg ?_ ?_
  · exact hnat.congr fun n => by push_cast; ring_nf
  · exact hnat.congr fun n => by push_cast; ring_nf

/-- Splitting a two-sided sum into its two halves. -/
theorem tsum_int_le_of_halves {f : ℤ → ℝ} (hpos : Summable fun n : ℕ => f (n : ℤ))
    (hneg : Summable fun n : ℕ => f (-((n : ℤ) + 1)))
    (hA : ∑' n : ℕ, f (n : ℤ) ≤ 2) (hB : ∑' n : ℕ, f (-((n : ℤ) + 1)) ≤ 2) :
    ∑' k : ℤ, f k ≤ 4 := by
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  linarith

theorem tsum_nat_inv_sq_le : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ)) ^ 2 ≤ 2 := by
  have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsplit := hnat.sum_add_tsum_nat_add 2
  have htail : ∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
    have h := tsum_inv_sq_shift_le 1 (le_refl 1)
    have hcongr : ∀ n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ 2
        = (1 : ℝ) / ((n : ℝ) + 1 + 1) ^ 2 := by
      intro n; push_cast; ring_nf
    rw [tsum_congr hcongr]
    simpa using h
  have hhead : ∑ i ∈ Finset.range 2, (1 : ℝ) / ((i : ℝ)) ^ 2 = 1 := by norm_num
  linarith [hsplit, htail, hhead]

theorem tsum_nat_inv_sq_shift_le : ∑' n : ℕ, (1 : ℝ) / (((n : ℝ)) + 1) ^ 2 ≤ 2 := by
  have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum2 := hnat.sum_add_tsum_nat_add 1
  have hconv : ∑' n : ℕ, (1 : ℝ) / (((n : ℝ)) + 1) ^ 2
      = ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
    refine tsum_congr fun n => ?_
    push_cast; ring_nf
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range 1, (1 : ℝ) / ((i : ℝ)) ^ 2 := by positivity
  rw [hconv]
  linarith [hsum2, tsum_nat_inv_sq_le, hnn]

/-- The two-sided inverse-square lattice sum (with the `k = 0` term read as `0`
by the convention `1/0 = 0`) is at most `4`. -/
theorem tsum_int_inv_sq_le : ∑' k : ℤ, (1 : ℝ) / ((k : ℝ)) ^ 2 ≤ 4 := by
  have hnat : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hshift : Summable fun n : ℕ => (1 : ℝ) / (((n : ℝ)) + 1) ^ 2 := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).2 hnat
    exact h.congr fun n => by push_cast; ring_nf
  refine tsum_int_le_of_halves (f := fun k : ℤ => (1 : ℝ) / ((k : ℝ)) ^ 2) ?_ ?_ ?_ ?_
  · exact hnat.congr fun n => by push_cast; ring_nf
  · exact hshift.congr fun n => by push_cast; ring_nf
  · simpa using tsum_nat_inv_sq_le
  · have hcongr : ∀ n : ℕ, (1 : ℝ) / (((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2
        = (1 : ℝ) / (((n : ℝ)) + 1) ^ 2 := by
      intro n; push_cast; ring_nf
    rw [tsum_congr hcongr]
    exact tsum_nat_inv_sq_shift_le

/-! ### The interference envelope -/

/-- **Quantitative mixed-interference envelope.**

Let `w : ℤ → ℂ` be the family of coordinate differences between a target zero
and the other zeros, enumerated so that the ordinate differences are
`δ`-separated (`δ|k| ≤ |Re w k|`) and the transverse differences stay bounded
(`|Im w k| ≤ 1`).  Then the total mixed interference of the target with the rest
of the family is at most `4 M² / δ²`, where `M = kernelMass φ`. -/
theorem mixedInterference_envelope {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {δ : ℝ}
    (hδ : 0 < δ) (w : ℤ → ℂ)
    (hre : ∀ k : ℤ, δ * |(k : ℝ)| ≤ |(w k).re|)
    (him : ∀ k : ℤ, |(w k).im| ≤ 1) :
    ∑' k : ℤ, (if k = 0 then 0 else (PhiExt (fun t => φ t ^ 2) (w k)).im ^ 2)
      ≤ 4 * kernelMass φ ^ 2 / δ ^ 2 := by
  set M := kernelMass φ with hM
  have hM0 : 0 ≤ M := kernelMass_nonneg φ
  set G : ℤ → ℝ := fun k => M ^ 2 / δ ^ 2 * ((1 : ℝ) / ((k : ℝ)) ^ 2) with hG
  have hGsummable : Summable G := summable_int_inv_sq.mul_left _
  have hpt : ∀ k : ℤ,
      (if k = 0 then 0 else (PhiExt (fun t => φ t ^ 2) (w k)).im ^ 2) ≤ G k := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hG]
    · have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hk
      have hkabs : 0 < |(k : ℝ)| := abs_pos.2 hkR
      have hsep := hre k
      have hrepos : 0 < |(w k).re| := lt_of_lt_of_le (by positivity) hsep
      have hwre : (w k).re ≠ 0 := by
        intro h0
        rw [h0] at hrepos
        simp at hrepos
      have hbound := abs_im_PhiKernel_le hφ hwre (him k)
      have hstep : |(PhiExt (fun t => φ t ^ 2) (w k)).im| ≤ M / (δ * |(k : ℝ)|) := by
        refine hbound.trans ?_
        have hpos : (0 : ℝ) < δ * |(k : ℝ)| := by positivity
        gcongr
      have hsq : (PhiExt (fun t => φ t ^ 2) (w k)).im ^ 2 ≤ (M / (δ * |(k : ℝ)|)) ^ 2 := by
        have h1 : |(PhiExt (fun t => φ t ^ 2) (w k)).im| ^ 2
            = (PhiExt (fun t => φ t ^ 2) (w k)).im ^ 2 := sq_abs _
        nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w k)).im, hstep,
          div_nonneg hM0 (le_of_lt (show (0:ℝ) < δ * |(k : ℝ)| by positivity))]
      have hval : (M / (δ * |(k : ℝ)|)) ^ 2 = G k := by
        rw [hG, div_pow, mul_pow, sq_abs]
        field_simp
      rw [if_neg hk]
      linarith [hsq, hval.symm.le, hval.le]
  have hnn : ∀ k : ℤ,
      0 ≤ (if k = 0 then 0 else (PhiExt (fun t => φ t ^ 2) (w k)).im ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      positivity
  have hFsummable := hGsummable.of_nonneg_of_le hnn hpt
  have hle := Summable.tsum_le_tsum hpt hFsummable hGsummable
  have hGval : ∑' k : ℤ, G k ≤ 4 * M ^ 2 / δ ^ 2 := by
    rw [hG, tsum_mul_left]
    have h := tsum_int_inv_sq_le
    have hc : 0 ≤ M ^ 2 / δ ^ 2 := by positivity
    calc M ^ 2 / δ ^ 2 * ∑' k : ℤ, (1 : ℝ) / ((k : ℝ)) ^ 2
        ≤ M ^ 2 / δ ^ 2 * 4 := mul_le_mul_of_nonneg_left h hc
      _ = 4 * M ^ 2 / δ ^ 2 := by ring
  linarith

end RiemannAnalytic
