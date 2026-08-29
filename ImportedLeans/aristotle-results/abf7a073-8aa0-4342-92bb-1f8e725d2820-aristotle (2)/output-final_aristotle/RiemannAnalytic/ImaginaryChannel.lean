/-
The exact transverse (imaginary-channel) energy of the centred grid.

The Hermitian specialisation `w = conj z` of the complex bilinear Poisson
identity gives the *total* grid energy

  `∑_{k ∈ ℤ} |φ̂(kh - iα)|² = L ∫ φ(u)² cosh(2αu) du`,

while the *bilinear* specialisation `w = z` gives

  `∑_{k ∈ ℤ} φ̂(kh - iα)² = L ∫ φ(u)² du`.

Subtracting real parts separates the two channels exactly: since
`|s|² - Re (s²) = 2 (Im s)²`, the transverse energy of the whole centred grid
is

  `∑_{k ∈ ℤ} (Im φ̂(kh - iα))² = (L/2) ∫ φ(u)² (cosh(2αu) - 1) du`.

This is an exact identity, not an estimate, and combined with the plateau
coercivity of `TaperCoercivity.lean` it gives the explicit floor

  `∑_{k ∈ ℤ} (Im φ̂(kh - iα))² ≥ (9/256) L⁴ α²`

in the source regime, hence strict positivity of the transverse channel for
every off-line offset `α ≠ 0`.  Together with `LatticeRetention.lean` this
yields an unconditional finite-window retention theorem for *any* `C¹`
compactly supported even taper with a plateau — no Gaussian special functions
and no tail-domination hypothesis.
-/
import RiemannAnalytic.TransverseEnergy
import RiemannAnalytic.LatticeRetention

namespace RiemannAnalytic

open MeasureTheory Complex Finset

/-- The grid points of the Hermitian Poisson identity, centred at `-iα`, are
exactly the centred grid samples of `PoissonExtension.lean`. -/
theorem gridPoint_eq (φ : ℝ → ℝ) (hs α : ℝ) (n : ℤ) :
    PhiExt φ ((0 : ℝ) - Complex.I * (α : ℂ) + ((n : ℝ) : ℂ) * ((hs : ℝ) : ℂ))
      = gridSample φ hs α n := by
  unfold gridSample
  congr 1
  push_cast
  ring

/-- The same identity with the grid spacing written out in `ℂ`. -/
theorem gridPoint_eq' (φ : ℝ → ℝ) (L α : ℝ) (n : ℤ) :
    PhiExt φ ((0 : ℝ) - Complex.I * (α : ℂ)
        + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (L : ℂ)))
      = gridSample φ (2 * Real.pi / L) α n := by
  unfold gridSample
  congr 1
  push_cast
  ring

/-- The Hermitian grid product is the squared modulus of the centred grid
sample. -/
theorem gridProduct_conj (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (hs α : ℝ) (n : ℤ) :
    PhiExt φ ((0 : ℝ) - Complex.I * (α : ℂ) + ((n : ℝ) : ℂ) * ((hs : ℝ) : ℂ))
        * PhiExt φ ((starRingEnd ℂ) ((0 : ℝ) - Complex.I * (α : ℂ))
          + ((n : ℝ) : ℂ) * ((hs : ℝ) : ℂ))
      = ((‖gridSample φ hs α n‖ ^ 2 : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) ((0 : ℝ) - Complex.I * (α : ℂ))
        + ((n : ℝ) : ℂ) * ((hs : ℝ) : ℂ)
      = (starRingEnd ℂ) (((0 : ℝ) - Complex.I * (α : ℂ))
          + ((n : ℝ) : ℂ) * ((hs : ℝ) : ℂ)) := by
    simp
  rw [hconj, ← PhiExt_conj_even φ hev, Complex.mul_conj', gridPoint_eq]
  push_cast
  ring

/-- The taper excess is the difference of the two exponential moments. -/
theorem taperExcess_eq_sub {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) (α : ℝ) :
    taperExcess φ α
      = (∫ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t)) - ∫ t : ℝ, φ t ^ 2 := by
  have hint₁ : Integrable fun t : ℝ => φ t ^ 2 * Real.cosh (2 * α * t) :=
    hφ.integrable_sq_mul (by fun_prop)
  unfold taperExcess
  rw [← integral_sub hint₁ hφ.integrable_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  ring

/-! ### The two channel sums -/

/-- **Total grid energy of the centred grid.** -/
theorem gridSample_normSq_tsum {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ) :
    ∑' k : ℤ, ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2
      = L * ∫ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t) := by
  have h := gridEnergy_eq_cosh_moment hφ hev hL h2R 0 α
  rw [← h]
  unfold gridEnergy
  exact (tsum_congr fun n => by rw [gridPoint_eq]).symm

/-- **Bilinear grid sum of the centred grid.** -/
theorem gridSample_sq_tsum {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ) :
    ∑' k : ℤ, gridSample φ (2 * Real.pi / L) α k ^ 2
      = (L : ℂ) * ((∫ t : ℝ, φ t ^ 2 : ℝ) : ℂ) := by
  have hpoisson := complex_bilinear_poisson hφ hev hL h2R
    ((0 : ℝ) - Complex.I * (α : ℂ)) ((0 : ℝ) - Complex.I * (α : ℂ))
  rw [sub_self, PhiExt_zero] at hpoisson
  rw [← hpoisson]
  exact (tsum_congr fun n => by rw [gridPoint_eq', sq]).symm

/-- `|z|² - Re (z²) = 2 (Im z)²`: the algebraic separation of the two
channels. -/
theorem normSq_sub_re_sq (z : ℂ) : ‖z‖ ^ 2 - (z ^ 2).re = 2 * z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, sq, Complex.mul_re]
  ring

/-! ### Summability of the two channels -/

theorem summable_gridSample_normSq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Summable fun k : ℤ => ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2 := by
  have hh : 0 < 2 * Real.pi / L := by positivity
  have hprod := summable_grid_product hφ hh ((0 : ℝ) - Complex.I * (α : ℂ))
    ((starRingEnd ℂ) ((0 : ℝ) - Complex.I * (α : ℂ)))
  exact Complex.summable_ofReal.1
    (hprod.congr fun n => gridProduct_conj φ hev (2 * Real.pi / L) α n)

theorem summable_gridSample_sq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Summable fun k : ℤ => gridSample φ (2 * Real.pi / L) α k ^ 2 := by
  have hh : 0 < 2 * Real.pi / L := by positivity
  have hprod := summable_grid_product hφ hh ((0 : ℝ) - Complex.I * (α : ℂ))
    ((0 : ℝ) - Complex.I * (α : ℂ))
  exact hprod.congr fun n => by rw [gridPoint_eq, sq]

theorem summable_transverseEnergy {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Summable (transverseEnergy φ (2 * Real.pi / L) α) := by
  have hA := summable_gridSample_normSq hφ hev hL α
  have hB : Summable fun k : ℤ => (gridSample φ (2 * Real.pi / L) α k ^ 2).re :=
    ((summable_gridSample_sq hφ hL α).map Complex.reCLM (by fun_prop)).congr fun k => rfl
  have hsub := hA.sub hB
  have h2 : Summable fun k : ℤ => 2 * transverseEnergy φ (2 * Real.pi / L) α k := by
    refine hsub.congr fun k => ?_
    simpa [transverseEnergy] using normSq_sub_re_sq (gridSample φ (2 * Real.pi / L) α k)
  simpa using h2.div_const 2

/-! ### The exact transverse energy identity -/

/-- **Exact transverse energy of the centred grid.**

For a `C¹` real even taper supported in `[-R, R]` with `2R ≤ L`, the whole
centred grid carries transverse (imaginary-channel) energy exactly

  `(L/2) ∫ φ(u)² (cosh(2αu) - 1) du`. -/
theorem transverseEnergy_tsum {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ) :
    ∑' k : ℤ, transverseEnergy φ (2 * Real.pi / L) α k = L / 2 * taperExcess φ α := by
  have hA := summable_gridSample_normSq hφ hev hL α
  have hB : Summable fun k : ℤ => (gridSample φ (2 * Real.pi / L) α k ^ 2).re :=
    ((summable_gridSample_sq hφ hL α).map Complex.reCLM (by fun_prop)).congr fun k => rfl
  have hpt : ∀ k : ℤ, 2 * transverseEnergy φ (2 * Real.pi / L) α k
      = ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2
        - (gridSample φ (2 * Real.pi / L) α k ^ 2).re := by
    intro k
    exact (normSq_sub_re_sq (gridSample φ (2 * Real.pi / L) α k)).symm
  have hsum2 : ∑' k : ℤ, 2 * transverseEnergy φ (2 * Real.pi / L) α k
      = (∑' k : ℤ, ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2)
        - ∑' k : ℤ, (gridSample φ (2 * Real.pi / L) α k ^ 2).re := by
    rw [← hA.tsum_sub hB]
    exact tsum_congr hpt
  have hBval : ∑' k : ℤ, (gridSample φ (2 * Real.pi / L) α k ^ 2).re
      = L * ∫ t : ℝ, φ t ^ 2 := by
    have h := congrArg Complex.re (gridSample_sq_tsum hφ hev hL h2R α)
    rw [Complex.re_tsum (summable_gridSample_sq hφ hL α)] at h
    simpa using h
  rw [tsum_mul_left, gridSample_normSq_tsum hφ hev hL h2R α, hBval] at hsum2
  rw [taperExcess_eq_sub hφ.toCompactTaper α]
  linarith

/-- **Positivity of the transverse channel.**  For a taper with a plateau of
positive half-width, the centred grid carries strictly positive transverse
energy precisely when the offset `α` is nonzero. -/
theorem transverseEnergy_tsum_pos {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 0 < a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {α : ℝ} (hα : α ≠ 0) :
    0 < ∑' k : ℤ, transverseEnergy φ (2 * Real.pi / L) α k := by
  rw [transverseEnergy_tsum hφ hev hL h2R α]
  have hpos := (taperExcess_pos_iff hφ.toCompactTaper ha hplat α).2 hα
  positivity

/-- **Explicit transverse energy floor in the source regime.** -/
theorem transverseEnergy_tsum_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    9 / 256 * L ^ 4 * α ^ 2 ≤ ∑' k : ℤ, transverseEnergy φ (2 * Real.pi / L) α k := by
  rw [transverseEnergy_tsum hφ hev hL h2R α]
  have h := transverseDefect_lower_source_regime hφ.toCompactTaper hL ha hplat α
  linarith

/-! ### Unconditional finite-window retention -/

/-- A summable series with positive sum has a finite window that
dominates its own tail and is itself positive. -/
theorem exists_window_dominating_tail (a : ℕ → ℝ) (ha : Summable a)
    (hpos : 0 < ∑' n, a n) :
    ∃ m : ℕ, ∑' n : ℕ, a (n + m) ≤ ∑ n ∈ range m, a n ∧
      0 < ∑ n ∈ range m, a n := by
  have hhalf : (0 : ℝ) < (∑' n, a n) / 2 := by linarith
  have htend := tendsto_sum_nat_add a
  obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hhalf)).exists
  have hsplit := (ha.sum_add_tsum_nat_add m).symm
  refine ⟨m, ?_, ?_⟩ <;> linarith [hm, hsplit]

/-- **Unconditional finite-window retention for the transverse channel.**

For any `C¹` real even taper supported in `[-R, R]` with `2R ≤ L` and a plateau
of positive half-width, and for any nonzero transverse offset `α`, some finite
one-sided window of the centred grid carries strictly positive transverse
energy and at least a quarter of the full two-sided transverse energy.

No tail-domination hypothesis and no Gaussian special functions are used: the
positivity of the total transverse energy comes from the exact identity
`transverseEnergy_tsum` together with plateau coercivity. -/
theorem transverseEnergy_finite_retention {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 0 < a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {α : ℝ} (hα : α ≠ 0) :
    ∃ m : ℕ,
      0 < ∑ n ∈ range m, transverseEnergy φ (2 * Real.pi / L) α ((n : ℤ) + 1) ∧
        ∑' k : ℤ, transverseEnergy φ (2 * Real.pi / L) α k
          ≤ 4 * ∑ n ∈ range m, transverseEnergy φ (2 * Real.pi / L) α ((n : ℤ) + 1) := by
  classical
  set hs := 2 * Real.pi / L with hhs
  have hsum : Summable (transverseEnergy φ hs α) := summable_transverseEnergy hφ hev hL α
  have htot : 0 < ∑' k : ℤ, transverseEnergy φ hs α k :=
    transverseEnergy_tsum_pos hφ hev hL h2R ha hplat hα
  set c : ℕ → ℝ := fun n => transverseEnergy φ hs α ((n : ℤ) + 1) with hc
  have hnat : Summable fun n : ℕ => transverseEnergy φ hs α (n : ℤ) :=
    hsum.comp_injective fun x y hxy => by exact_mod_cast hxy
  have hcsum : Summable c := by
    have : Summable fun n : ℕ => (fun m : ℕ => transverseEnergy φ hs α (m : ℤ)) (n + 1) :=
      (summable_nat_add_iff 1).2 hnat
    simpa [hc] using this
  have htwo := transverseEnergy_twoSided φ hev hs α hsum
  have hcpos : 0 < ∑' n : ℕ, c n := by
    have : ∑' k : ℤ, transverseEnergy φ hs α k = 2 * ∑' n : ℕ, c n := by
      simpa [hc] using htwo
    linarith [this ▸ htot]
  obtain ⟨m, hdom, hwin⟩ := exists_window_dominating_tail c hcsum hcpos
  have hkey : ∀ n : ℕ, c (n + m) = transverseEnergy φ hs α ((n : ℤ) + (m : ℤ) + 1) := by
    intro n
    simp only [hc]
    push_cast
    ring_nf
  refine ⟨m, hwin, ?_⟩
  refine gridFiniteRetention φ hev hs α hsum m ?_
  rw [← tsum_congr hkey]
  exact hdom

end RiemannAnalytic
