/-
The **finite** symmetric window retains the transverse surplus.

`GramSurplus.lean` shows that the transverse surplus of a pair block is `2m²`
times the gap `H² - |S|²` between the Hermitian and bilinear channels, and
computes that gap exactly over the *whole* centred lattice.  The matrix that the
prime side actually controls is finite, so the surplus has to survive
truncation to a finite window.

Here the window is taken **symmetric about the target ordinate**,
`-m ≤ k ≤ m`, which is available in the source geometry by choosing the height
`T = γ_ρ - m·(2π/L)`.  For such a window the conjugation symmetry
`φ̂(-kh - iα) = conj φ̂(kh - iα)` of a real even taper makes the cross Gram
entry vanish *identically*:

  `∑_{|k| ≤ m} Re φ̂_k · Im φ̂_k = 0`,

so the finite Gram determinant is **exactly the product** of the two retained
energies,

  `Gram_m = (∑_{|k| ≤ m} (Re φ̂_k)²) · (∑_{|k| ≤ m} (Im φ̂_k)²)`,

with no Cauchy--Schwarz loss at all.  There is therefore no non-parallelism
hypothesis to discharge in the finite window either.

Both factors are then bounded below explicitly:

* the transverse factor by `2((L/4) taperExcess - C_φ(α)²/(h²m))`, from the
  quantitative lattice tail of `GridTail.lean`;
* the longitudinal factor by the single central sample `φ̂(-iα)² ≥ (2a)²`, for a
  nonnegative taper with a plateau of half-width `a`.

The result is an explicit floor for the finite-window transverse surplus.
-/
import RiemannAnalytic.GramSurplus
import RiemannAnalytic.TransverseKernel

namespace RiemannAnalytic

open MeasureTheory Complex Finset

/-! ### Symmetric sums over an integer window -/

/-- A sum over the symmetric window `[-m, m]` splits into the central term and
the `±k` pairs. -/
theorem sum_Icc_symm (g : ℤ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), g k
      = g 0 + ∑ n ∈ range m, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hset : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)
          = insert ((m : ℤ) + 1) (insert (-((m : ℤ) + 1)) (Finset.Icc (-(m : ℤ)) (m : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
        omega
      have hmem₁ : ((m : ℤ) + 1) ∉ insert (-((m : ℤ) + 1)) (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hmem₂ : (-((m : ℤ) + 1)) ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hmem₁, Finset.sum_insert hmem₂, ih,
        Finset.sum_range_succ]
      ring

/-! ### The three window Gram entries -/

/-- Longitudinal energy retained by the symmetric window. -/
noncomputable def windowRe (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (gridSample φ h α k).re ^ 2

/-- Transverse energy retained by the symmetric window. -/
noncomputable def windowIm (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (gridSample φ h α k).im ^ 2

/-- Cross Gram entry of the symmetric window. -/
noncomputable def windowCross (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (gridSample φ h α k).re * (gridSample φ h α k).im

/-- Gram determinant of the symmetric window. -/
noncomputable def windowGram (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : ℝ :=
  windowRe φ h α m * windowIm φ h α m - windowCross φ h α m ^ 2

theorem windowIm_nonneg (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : 0 ≤ windowIm φ h α m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem windowRe_nonneg (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : 0 ≤ windowRe φ h α m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The cross Gram entry of a symmetric window vanishes.**  This is the
non-parallelism input: for a real even taper the real and imaginary parts of the
evaluation vector over a window centred at the target ordinate are exactly
orthogonal. -/
theorem windowCross_eq_zero (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (m : ℕ) :
    windowCross φ h α m = 0 := by
  unfold windowCross
  rw [sum_Icc_symm (fun k => (gridSample φ h α k).re * (gridSample φ h α k).im) m]
  have hzero : (gridSample φ h α 0).re * (gridSample φ h α 0).im = 0 := by
    rw [gridSample_zero_im φ hev h α, mul_zero]
  have hpair : ∀ n : ℕ,
      (gridSample φ h α ((n : ℤ) + 1)).re * (gridSample φ h α ((n : ℤ) + 1)).im
        + (gridSample φ h α (-((n : ℤ) + 1))).re * (gridSample φ h α (-((n : ℤ) + 1))).im
        = 0 := by
    intro n
    rw [gridSample_neg_eq_conj φ hev h α ((n : ℤ) + 1)]
    simp
  rw [hzero, Finset.sum_congr rfl fun n _ => hpair n]
  simp

/-- **The finite symmetric-window Gram determinant is the exact product of the
two retained energies.** -/
theorem windowGram_eq_product (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (m : ℕ) :
    windowGram φ h α m = windowRe φ h α m * windowIm φ h α m := by
  unfold windowGram
  rw [windowCross_eq_zero φ hev h α m]
  ring

/-- The retained transverse energy of the symmetric window is twice the one-sided
window energy of `GridTail.lean`. -/
theorem windowIm_eq_two_mul (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (m : ℕ) :
    windowIm φ h α m = 2 * ∑ n ∈ range m, transverseEnergy φ h α ((n : ℤ) + 1) := by
  unfold windowIm
  rw [sum_Icc_symm (fun k => (gridSample φ h α k).im ^ 2) m]
  have hzero : (gridSample φ h α 0).im ^ 2 = 0 := by
    rw [gridSample_zero_im φ hev h α]; ring
  have hpair : ∀ n : ℕ,
      (gridSample φ h α ((n : ℤ) + 1)).im ^ 2 + (gridSample φ h α (-((n : ℤ) + 1))).im ^ 2
        = 2 * transverseEnergy φ h α ((n : ℤ) + 1) := by
    intro n
    rw [gridSample_im_sq_neg φ hev h α ((n : ℤ) + 1)]
    simp [transverseEnergy]
    ring
  rw [hzero, Finset.sum_congr rfl fun n _ => hpair n, ← Finset.mul_sum]
  ring

/-- The longitudinal factor dominates the central sample. -/
theorem windowRe_ge_center (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) :
    (gridSample φ h α 0).re ^ 2 ≤ windowRe φ h α m := by
  unfold windowRe
  rw [sum_Icc_symm (fun k => (gridSample φ h α k).re ^ 2) m]
  have hnn : (0 : ℝ) ≤ ∑ n ∈ range m,
      ((gridSample φ h α ((n : ℤ) + 1)).re ^ 2 + (gridSample φ h α (-((n : ℤ) + 1))).re ^ 2) :=
    Finset.sum_nonneg fun n _ => by positivity
  linarith

/-! ### The central sample of a nonnegative taper with a plateau -/

/-- The central grid sample is the real exponential moment of the taper. -/
theorem gridSample_zero_re (φ : ℝ → ℝ) (h α : ℝ) :
    (gridSample φ h α 0).re = ∫ t : ℝ, φ t * Real.exp (-(α * t)) := by
  have hval : gridSample φ h α 0 = PhiExt φ (-(2 * (α / 2) : ℝ) * Complex.I) := by
    unfold gridSample
    congr 1
    push_cast
    simp [Complex.ext_iff]
    ring
  rw [hval, PhiExt_ofReal_neg_two_mul_I]
  simp only [Complex.ofReal_re]
  refine congrArg _ (funext fun t => ?_)
  congr 2
  ring

/-- **The central sample of a nonnegative taper with a plateau is at least the
plateau width.** -/
theorem gridSample_zero_re_ge_plateau {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hnn : ∀ t, 0 ≤ φ t) {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (h α : ℝ) :
    2 * a ≤ (gridSample φ h α 0).re := by
  rw [gridSample_zero_re]
  have hint : Integrable fun t : ℝ => φ t * Real.exp (-(α * t)) :=
    hφ.integrable_mul (by fun_prop)
  have hptnn : ∀ t : ℝ, 0 ≤ φ t * Real.exp (-(α * t)) := fun t => by
    have := hnn t
    positivity
  have hrestrict : ∫ t in Set.Icc (-a) a, φ t * Real.exp (-(α * t))
      ≤ ∫ t : ℝ, φ t * Real.exp (-(α * t)) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hptnn)
  have hplateau : ∫ t in Set.Icc (-a) a, φ t * Real.exp (-(α * t))
      = ∫ t in Set.Icc (-a) a, Real.exp (-(α * t)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [hplat t (abs_le.2 ⟨ht.1, ht.2⟩), one_mul]
  have hlin : ∫ t in Set.Icc (-a) a, (1 - α * t) ≤ ∫ t in Set.Icc (-a) a, Real.exp (-(α * t)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun t _ => ?_
    · exact (by fun_prop : Continuous fun t : ℝ => 1 - α * t).continuousOn.integrableOn_compact
        isCompact_Icc
    · exact (by fun_prop : Continuous fun t : ℝ =>
        Real.exp (-(α * t))).continuousOn.integrableOn_compact isCompact_Icc
    · have := Real.add_one_le_exp (-(α * t))
      linarith
  have hcalc : ∫ t in Set.Icc (-a) a, (1 - α * t) = 2 * a := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-a : ℝ) ≤ a)]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_id).const_mul α)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_id]
    simp
    ring
  linarith [hrestrict, hplateau.le, hplateau.ge, hlin, hcalc.le, hcalc.ge]

/-! ### The explicit finite-window surplus floor -/

/-- **Explicit floor for the finite symmetric-window Gram determinant.**

For a `C¹`, nonnegative, real even taper supported in `[-R, R]` with `2R ≤ L`,
a plateau of half-width `a`, grid spacing `h = 2π/L`, and any window
half-length `m ≥ 1`,

  `Gram_m ≥ 4a² · 2((L/4)·taperExcess φ α - C_φ(α)²/(h² m))`.

Both factors are explicit; the second is positive as soon as the window is long
enough, by `transverseEnergy_window_pos`. -/
theorem windowGram_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    4 * a ^ 2 * (2 * (L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)))
      ≤ windowGram φ (2 * Real.pi / L) α m := by
  set h := 2 * Real.pi / L with hh
  have hprod := windowGram_eq_product φ hev h α m
  have hRe : 4 * a ^ 2 ≤ windowRe φ h α m := by
    have hc := gridSample_zero_re_ge_plateau hφ.toCompactTaper hnn ha hplat h α
    have hsq : (2 * a) ^ 2 ≤ (gridSample φ h α 0).re ^ 2 := by
      have h0 : (0 : ℝ) ≤ 2 * a := by linarith
      nlinarith
    have := windowRe_ge_center φ h α m
    nlinarith
  have hIm : 2 * (L / 4 * taperExcess φ α
      - derivMass φ α ^ 2 / (h ^ 2 * m)) ≤ windowIm φ h α m := by
    rw [windowIm_eq_two_mul φ hev h α m]
    have := transverseEnergy_window_lower hφ hev hL h2R α hm
    linarith
  have hImnn : 0 ≤ windowIm φ h α m := windowIm_nonneg φ h α m
  have hann : (0 : ℝ) ≤ 4 * a ^ 2 := by positivity
  rw [hprod]
  nlinarith [hRe, hIm, hImnn, hann]

/-- **Explicit quadratic floor in the source regime.**

With plateau half-width `a ≥ 3L/8` (the source regime `8w ≤ L`), the finite
symmetric-window Gram determinant obeys

  `Gram_m ≥ (9/16) L² · 2((9/512) L⁴ α² - C_φ(α)²/(h² m))`,

hence the finite-window transverse surplus `8m'² Gram_m` of the pair block is
bounded below by an explicit multiple of `L⁶ α²` once the window is long enough
to absorb the lattice tail. -/
theorem windowGram_source_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    9 / 16 * L ^ 2 * (2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)))
      ≤ windowGram φ (2 * Real.pi / L) α m := by
  set h := 2 * Real.pi / L with hh
  have ha0 : 0 ≤ a := by linarith
  have hprod := windowGram_eq_product φ hev h α m
  have hRe : 9 / 16 * L ^ 2 ≤ windowRe φ h α m := by
    have hc := gridSample_zero_re_ge_plateau hφ.toCompactTaper hnn ha0 hplat h α
    have h0 : (0 : ℝ) ≤ 2 * a := by linarith
    have hsq : (2 * a) ^ 2 ≤ (gridSample φ h α 0).re ^ 2 := by nlinarith
    have hcenter := windowRe_ge_center φ h α m
    nlinarith
  have hIm : 2 * (9 / 512 * L ^ 4 * α ^ 2
      - derivMass φ α ^ 2 / (h ^ 2 * m)) ≤ windowIm φ h α m := by
    rw [windowIm_eq_two_mul φ hev h α m]
    have hwin := transverseEnergy_window_lower hφ hev hL h2R α hm
    have hexc := taperExcess_ge_plateau_quadratic hφ.toCompactTaper ha0 hplat α
    have hcube : (3 * L / 8) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by positivity) ha 3
    have hkey : 9 / 128 * L ^ 3 * α ^ 2 ≤ taperExcess φ α := by
      have hstep : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 ≤ 4 / 3 * a ^ 3 * α ^ 2 := by
        nlinarith [sq_nonneg α, hcube]
      have hval : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 = 9 / 128 * L ^ 3 * α ^ 2 := by ring
      linarith
    have hfloor : 9 / 512 * L ^ 4 * α ^ 2 ≤ L / 4 * taperExcess φ α := by
      nlinarith [hkey, hL.le]
    linarith
  have hImnn : 0 ≤ windowIm φ h α m := windowIm_nonneg φ h α m
  rw [hprod]
  nlinarith [hRe, hIm, hImnn, sq_nonneg L]

/-! ### The window Gram determinant is the pair-block transverse surplus -/

/-- **The finite symmetric window is literally the pair-block data.**  The
transverse surplus of the pair block built from the real and imaginary parts of
the window evaluation vector is `8m'²` times the window Gram determinant. -/
theorem transverseSurplus_window (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) (m' : ℝ) :
    transverseSurplus m'
        (fun k : {k : ℤ // k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)} => (gridSample φ h α k).re)
        (fun k : {k : ℤ // k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)} => (gridSample φ h α k).im)
      = 8 * m' ^ 2 * windowGram φ h α m := by
  unfold transverseSurplus windowGram windowRe windowIm windowCross
  simp only [dotProduct, ← sq]
  rw [Finset.sum_coe_sort (Finset.Icc (-(m : ℤ)) (m : ℤ))
      (fun k => (gridSample φ h α k).re ^ 2),
    Finset.sum_coe_sort (Finset.Icc (-(m : ℤ)) (m : ℤ))
      (fun k => (gridSample φ h α k).im ^ 2)]
  congr 2
  rw [← Finset.sum_coe_sort (Finset.Icc (-(m : ℤ)) (m : ℤ))
    (fun k => (gridSample φ h α k).re * (gridSample φ h α k).im)]

/-- **Explicit floor for the finite-window transverse surplus of a pair block.**

Combining the previous two results: in the source regime the transverse surplus
of the pair block of a hypothetical off-line zero, computed on the finite
symmetric window actually available to the prime side, is at least

  `8 m'² · (9/16) L² · 2((9/512) L⁴ α² - C_φ(α)²/(h² m))`. -/
theorem transverseSurplus_window_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (m' : ℝ) :
    8 * m' ^ 2 * (9 / 16 * L ^ 2 * (2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m))))
      ≤ transverseSurplus m'
          (fun k : {k : ℤ // k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)} =>
            (gridSample φ (2 * Real.pi / L) α k).re)
          (fun k : {k : ℤ // k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)} =>
            (gridSample φ (2 * Real.pi / L) α k).im) := by
  rw [transverseSurplus_window φ (2 * Real.pi / L) α m m']
  have hfloor := windowGram_source_floor hφ hev hnn hL h2R ha hplat α hm
  nlinarith [sq_nonneg m', hfloor]

end RiemannAnalytic
