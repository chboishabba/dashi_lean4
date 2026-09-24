/-
Quantitative lattice-tail control on the centred grid, and the resulting
*explicit* finite-window retention bound.

`ImaginaryChannel.lean` proves that the whole centred grid carries transverse
energy exactly `(L/2)·taperExcess φ α`, and deduces retention in an existential
form.  Here the window is made explicit: horizontal decay of the complex
extension of a `C¹` taper gives

  `|φ̂(kh - iα)| ≤ C_φ(α) / (|k| h)`,

hence the one-sided lattice tail beyond a window of length `m` obeys

  `∑_{k > m} (Im φ̂(kh - iα))² ≤ C_φ(α)² / (h² m)`,

and therefore the retained window energy satisfies the explicit lower bound

  `∑_{k = 1}^{m} (Im φ̂(kh - iα))² ≥ (L/4)·taperExcess φ α - C_φ(α)²/(h² m)`.

Everything is elementary but genuinely quantitative: the constant `C_φ(α)` is
the `L¹` mass of the twisted derivative of the taper.
-/
import RiemannAnalytic.ImaginaryChannel

namespace RiemannAnalytic

open MeasureTheory Complex Finset

/-! ### An elementary tail estimate for `∑ k⁻²` -/

/-- Partial sums of the shifted inverse-square series telescope. -/
theorem sum_range_inv_sq_shift_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + m + 1) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((n : ℝ) + m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  induction n with
  | zero => simp
  | succ n ih =>
      have hn0 : (0 : ℝ) < (n : ℝ) + m := by positivity
      have hn1 : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
      have hstep : (1 : ℝ) / ((n : ℝ) + m + 1) ^ 2
          ≤ 1 / ((n : ℝ) + m) - 1 / ((n : ℝ) + m + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hn0) (ne_of_gt hn1), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      have hcast : ((n : ℝ) + 1) + m = ((n : ℝ) + m) + 1 := by ring
      rw [Finset.sum_range_succ]
      push_cast
      rw [hcast]
      linarith [ih, hstep]

/-- The shifted inverse-square tail is bounded by `1/m`. -/
theorem tsum_inv_sq_shift_le (m : ℕ) (hm : 1 ≤ m) :
    ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + m + 1) ^ 2 ≤ 1 / (m : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun n => ?_
  have h := sum_range_inv_sq_shift_le m hm n
  have hn : (0 : ℝ) ≤ 1 / ((n : ℝ) + m) := by positivity
  linarith

/-! ### Horizontal decay of the centred grid samples -/

/-- The `L¹` mass of the twisted derivative of the taper: the constant in the
horizontal decay estimate. -/
noncomputable def derivMass (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ u : ℝ, |deriv φ u| * Real.exp (-α * u)

theorem derivMass_nonneg (φ : ℝ → ℝ) (α : ℝ) : 0 ≤ derivMass φ α :=
  integral_nonneg fun u => by positivity

/-- **Horizontal decay of the centred grid samples.** -/
theorem norm_gridSample_mul_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {h : ℝ} (hh : 0 < h)
    (α : ℝ) (k : ℤ) :
    ‖gridSample φ h α k‖ * (|(k : ℝ)| * h) ≤ derivMass φ α := by
  have hz := norm_PhiExt_mul_abs_re_le hφ (((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ))
  have hre : ((( k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)).re = (k : ℝ) * h := by simp
  have him : ((( k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)).im = -α := by simp
  rw [hre, him, abs_mul, abs_of_pos hh] at hz
  exact hz

/-- The transverse energy of a nonzero grid sample decays like `k⁻²`. -/
theorem transverseEnergy_le_inv_sq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {h : ℝ}
    (hh : 0 < h) (α : ℝ) {k : ℤ} (hk : k ≠ 0) :
    transverseEnergy φ h α k ≤ derivMass φ α ^ 2 / (h ^ 2 * (k : ℝ) ^ 2) := by
  have hkabs : (0 : ℝ) < |(k : ℝ)| := by
    have : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hk
    exact abs_pos.2 this
  have hdec := norm_gridSample_mul_le hφ hh α k
  have hnn : 0 ≤ ‖gridSample φ h α k‖ := norm_nonneg _
  have hbound : ‖gridSample φ h α k‖ ≤ derivMass φ α / (|(k : ℝ)| * h) := by
    rw [le_div_iff₀ (by positivity)]
    exact hdec
  have him : transverseEnergy φ h α k ≤ ‖gridSample φ h α k‖ ^ 2 := by
    have := Complex.abs_im_le_norm (gridSample φ h α k)
    have h2 : (gridSample φ h α k).im ^ 2 ≤ ‖gridSample φ h α k‖ ^ 2 := by
      nlinarith [abs_nonneg (gridSample φ h α k).im, sq_abs (gridSample φ h α k).im]
    simpa [transverseEnergy] using h2
  have hsq : ‖gridSample φ h α k‖ ^ 2 ≤ (derivMass φ α / (|(k : ℝ)| * h)) ^ 2 :=
    pow_le_pow_left₀ hnn hbound 2
  have hval : (derivMass φ α / (|(k : ℝ)| * h)) ^ 2
      = derivMass φ α ^ 2 / (h ^ 2 * (k : ℝ) ^ 2) := by
    rw [div_pow, mul_pow, sq_abs]
    ring_nf
  linarith [him, hsq, hval.symm.le, hval.le]

/-! ### The explicit lattice tail bound -/

/-- **Explicit one-sided lattice tail bound.**  Beyond a window of length
`m ≥ 1` the positive-lattice transverse tail is at most
`C_φ(α)² / (h² m)`. -/
theorem transverseEnergy_tail_le {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) {h : ℝ}
    (hh : 0 < h) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∑' n : ℕ, transverseEnergy φ h α ((n : ℤ) + (m : ℤ) + 1)
      ≤ derivMass φ α ^ 2 / (h ^ 2 * m) := by
  have hpt : ∀ n : ℕ, transverseEnergy φ h α ((n : ℤ) + (m : ℤ) + 1)
      ≤ derivMass φ α ^ 2 / h ^ 2 * ((1 : ℝ) / ((n : ℝ) + m + 1) ^ 2) := by
    intro n
    have hk : ((n : ℤ) + (m : ℤ) + 1) ≠ 0 := by positivity
    have hb := transverseEnergy_le_inv_sq hφ hh α hk
    have hcast : (((n : ℤ) + (m : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + m + 1 := by push_cast; ring
    rw [hcast] at hb
    have hval : derivMass φ α ^ 2 / (h ^ 2 * ((n : ℝ) + m + 1) ^ 2)
        = derivMass φ α ^ 2 / h ^ 2 * ((1 : ℝ) / ((n : ℝ) + m + 1) ^ 2) := by
      field_simp
    linarith [hb, hval.symm.le, hval.le]
  have hsummable : Summable fun n : ℕ =>
      derivMass φ α ^ 2 / h ^ 2 * ((1 : ℝ) / ((n : ℝ) + m + 1) ^ 2) := by
    have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + m + 1) ^ 2 := by
      have hp : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
        simpa using (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2
          (Real.summable_one_div_nat_pow.2 (by norm_num))
      refine hp.of_nonneg_of_le (fun n => by positivity) fun n => ?_
      have h1 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + m + 1) ^ 2 := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
    exact hbase.mul_left _
  have hnn : ∀ n : ℕ, 0 ≤ transverseEnergy φ h α ((n : ℤ) + (m : ℤ) + 1) := fun n => by
    simp only [transverseEnergy]
    positivity
  have hle := Summable.tsum_le_tsum hpt (hsummable.of_nonneg_of_le hnn hpt) hsummable
  have hcalc : ∑' n : ℕ, derivMass φ α ^ 2 / h ^ 2 * ((1 : ℝ) / ((n : ℝ) + m + 1) ^ 2)
      ≤ derivMass φ α ^ 2 / h ^ 2 * (1 / (m : ℝ)) := by
    rw [tsum_mul_left]
    have hc : 0 ≤ derivMass φ α ^ 2 / h ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (tsum_inv_sq_shift_le m hm) hc
  have hfinal : derivMass φ α ^ 2 / h ^ 2 * (1 / (m : ℝ))
      = derivMass φ α ^ 2 / (h ^ 2 * m) := by
    field_simp
  linarith [hle, hcalc, hfinal.symm.le, hfinal.le]

/-! ### Explicit finite-window retention -/

/-- **Explicit retained-window lower bound.**

For a `C¹` real even taper supported in `[-R, R]` with `2R ≤ L`, grid spacing
`h = 2π/L`, and any window length `m ≥ 1`, the finite one-sided window
`1 ≤ k ≤ m` of the centred grid retains transverse energy at least

  `(L/4)·taperExcess φ α - C_φ(α)²/(h² m)`. -/
theorem transverseEnergy_window_lower {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ ∑ n ∈ range m, transverseEnergy φ (2 * Real.pi / L) α ((n : ℤ) + 1) := by
  classical
  set hs := 2 * Real.pi / L with hhs
  have hh : 0 < hs := by rw [hhs]; positivity
  have hsum : Summable (transverseEnergy φ hs α) := summable_transverseEnergy hφ hev hL α
  set c : ℕ → ℝ := fun n => transverseEnergy φ hs α ((n : ℤ) + 1) with hc
  have hnat : Summable fun n : ℕ => transverseEnergy φ hs α (n : ℤ) :=
    hsum.comp_injective fun x y hxy => by exact_mod_cast hxy
  have hcsum : Summable c := by
    have : Summable fun n : ℕ => (fun j : ℕ => transverseEnergy φ hs α (j : ℤ)) (n + 1) :=
      (summable_nat_add_iff 1).2 hnat
    simpa [hc] using this
  have hsplit := (hcsum.sum_add_tsum_nat_add m).symm
  have hkey : ∀ n : ℕ, c (n + m) = transverseEnergy φ hs α ((n : ℤ) + (m : ℤ) + 1) := by
    intro n
    simp only [hc]
    push_cast
    ring_nf
  have htail : ∑' n : ℕ, c (n + m) ≤ derivMass φ α ^ 2 / (hs ^ 2 * m) := by
    rw [tsum_congr hkey]
    exact transverseEnergy_tail_le hφ hh α hm
  have htwo := transverseEnergy_twoSided φ hev hs α hsum
  have hexact := transverseEnergy_tsum hφ hev hL h2R α
  have htotal : (2 : ℝ) * ∑' n : ℕ, c n = L / 2 * taperExcess φ α := by
    rw [← hexact, htwo]
  linarith [hsplit, htail, htotal]

/-- **Explicit retention criterion.**  In the source regime `a ≥ 3L/8`, the
retained window energy is at least `(9/512)L⁴α²` minus the explicit tail, so any
window long enough to make the tail smaller than that floor retains strictly
positive transverse energy. -/
theorem transverseEnergy_window_pos {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ)
    {m : ℕ} (hm : 1 ≤ m)
    (hbig : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) < 9 / 512 * L ^ 4 * α ^ 2) :
    0 < ∑ n ∈ range m, transverseEnergy φ (2 * Real.pi / L) α ((n : ℤ) + 1) := by
  have hlow := transverseEnergy_window_lower hφ hev hL h2R α hm
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hexc := taperExcess_ge_plateau_quadratic hφ.toCompactTaper ha0 hplat α
  have hcube : (3 * L / 8) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by positivity) ha 3
  have hkey : 9 / 128 * L ^ 3 * α ^ 2 ≤ taperExcess φ α := by
    have hstep : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 ≤ 4 / 3 * a ^ 3 * α ^ 2 := by
      nlinarith [sq_nonneg α, hcube]
    have hval : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 = 9 / 128 * L ^ 3 * α ^ 2 := by ring
    linarith
  have hmul := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ L / 4 by positivity)
  have hval2 : L / 4 * (9 / 128 * L ^ 3 * α ^ 2) = 9 / 512 * L ^ 4 * α ^ 2 := by ring
  have hfloor : 9 / 512 * L ^ 4 * α ^ 2 ≤ L / 4 * taperExcess φ α := by
    linarith [hmul, hval2.symm.le, hval2.le]
  linarith

end RiemannAnalytic
