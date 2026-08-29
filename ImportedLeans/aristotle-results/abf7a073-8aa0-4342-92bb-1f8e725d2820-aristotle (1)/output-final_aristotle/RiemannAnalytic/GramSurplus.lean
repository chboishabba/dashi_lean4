/-
The transverse surplus of a pair block, exactly, through the two channels.

`FrobeniusDecomposition.lean` splits the Frobenius square of a reflection pair
block `Q = 2m(aaᵀ - bbᵀ)` into a critical baseline plus a *transverse surplus*

  `transverseSurplus m a b = 8m² ((a·a)(b·b) - (a·b)²)`,

i.e. `8m²` times the Gram determinant of the two real coordinate vectors.  The
Gram determinant is nonnegative by Cauchy--Schwarz, and vanishes exactly when
`a` and `b` are proportional — so the surplus is the quantity that has to be
bounded *below* for an off-line zero.  Bounding `b·b` below is not enough: the
vectors must also be non-parallel.

This file removes that obstruction, by an exact identity.  Writing
`u = a + i b` for the complex evaluation vector, the two channels

  `H = ∑_k |u_k|²`  (Hermitian),   `S = ∑_k u_k²`  (bilinear)

satisfy `H = a·a + b·b`, `Re S = a·a - b·b`, `Im S = 2 a·b`, whence

  `4 ((a·a)(b·b) - (a·b)²) = H² - |S|²`.

So the Gram determinant *is* the gap between the two channels, and the
transverse surplus is `2m²(H² - |S|²)`.

On the whole centred lattice both channels are known exactly from the complex
bilinear Poisson identity:

  `H = L ∫ φ² cosh(2αu) du = L(P + E)`,   `S = L ∫ φ² du = L P`,

with `P = ∫ φ²` and `E = taperExcess φ α`.  Hence

  `H² - |S|² = L² E (2P + E) ≥ 2 L² P E`,

which is strictly positive for every `α ≠ 0`; the real and imaginary parts of
the evaluation vector are in fact exactly *orthogonal* over the whole lattice.
In the source regime (plateau half-width `a ≥ 3L/8`) this gives the explicit
floor

  `2m² (H² - |S|²) ≥ (27/128) m² L⁶ α²`.

This is the non-parallelism input that a lower bound on `b·b` alone cannot
supply.
-/
import RiemannAnalytic.GridVectors

namespace RiemannAnalytic

open MeasureTheory Complex Finset

variable {d : ℕ}

/-! ### The Gram determinant is the channel gap -/

/-- **The Gram determinant of the real and imaginary parts of a complex vector
is the gap between its Hermitian and bilinear channels.** -/
theorem gram_eq_channel_gap (u : Fin d → ℂ) :
    4 * ((reOf u ⬝ᵥ reOf u) * (imOf u ⬝ᵥ imOf u) - (reOf u ⬝ᵥ imOf u) ^ 2)
      = (∑ k, ‖u k‖ ^ 2) ^ 2 - ‖∑ k, u k ^ 2‖ ^ 2 := by
  have hA : reOf u ⬝ᵥ reOf u = ∑ k, (u k).re ^ 2 := reOf_dotProduct_self u
  have hB : imOf u ⬝ᵥ imOf u = ∑ k, (u k).im ^ 2 := imOf_dotProduct_self u
  have hC : reOf u ⬝ᵥ imOf u = ∑ k, (u k).re * (u k).im := by
    simp [dotProduct, reOf, imOf]
  have hH : ∑ k, ‖u k‖ ^ 2 = (∑ k, (u k).re ^ 2) + ∑ k, (u k).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, sq]
  have hSre : (∑ k, u k ^ 2).re = (∑ k, (u k).re ^ 2) - ∑ k, (u k).im ^ 2 := by
    rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sq, Complex.mul_re]
  have hSim : (∑ k, u k ^ 2).im = 2 * ∑ k, (u k).re * (u k).im := by
    rw [Complex.im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sq, Complex.mul_im]
    ring
  have hSnorm : ‖∑ k, u k ^ 2‖ ^ 2
      = (∑ k, u k ^ 2).re ^ 2 + (∑ k, u k ^ 2).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, sq]
  rw [hA, hB, hC, hH, hSnorm, hSre, hSim]
  ring

/-- **The transverse surplus of a grid pair block through the two channels.** -/
theorem transverseSurplus_eq_channel_gap (m : ℝ) (u : Fin d → ℂ) :
    transverseSurplus m (reOf u) (imOf u)
      = 2 * m ^ 2 * ((∑ k, ‖u k‖ ^ 2) ^ 2 - ‖∑ k, u k ^ 2‖ ^ 2) := by
  unfold transverseSurplus
  rw [← gram_eq_channel_gap u]
  ring

/-! ### The two channels of the whole centred lattice -/

/-- The channel gap of the whole centred lattice. -/
noncomputable def latticeChannelGap (φ : ℝ → ℝ) (L α : ℝ) : ℝ :=
  (∑' k : ℤ, ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2) ^ 2
    - ‖∑' k : ℤ, gridSample φ (2 * Real.pi / L) α k ^ 2‖ ^ 2

/-- **Exact value of the lattice channel gap.**  With `P = ∫ φ²` the total mass
of the squared taper and `E = taperExcess φ α` the transverse excess,

  `H² - |S|² = L² E (2P + E)`. -/
theorem latticeChannelGap_eq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ) :
    latticeChannelGap φ L α
      = L ^ 2 * taperExcess φ α * (2 * (∫ t : ℝ, φ t ^ 2) + taperExcess φ α) := by
  set P := ∫ t : ℝ, φ t ^ 2 with hP
  have hP0 : 0 ≤ P := integral_nonneg fun u => sq_nonneg _
  have hH : ∑' k : ℤ, ‖gridSample φ (2 * Real.pi / L) α k‖ ^ 2
      = L * (P + taperExcess φ α) := by
    rw [gridSample_normSq_tsum hφ hev hL h2R α, taperExcess_eq_sub hφ.toCompactTaper α]
    ring
  have hS : ‖∑' k : ℤ, gridSample φ (2 * Real.pi / L) α k ^ 2‖ = L * P := by
    rw [gridSample_sq_tsum hφ hev hL h2R α]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hL, abs_of_nonneg hP0]
  unfold latticeChannelGap
  rw [hH, hS]
  ring

/-- Over the whole lattice the real and imaginary parts of the evaluation vector
are **exactly orthogonal**. -/
theorem lattice_reIm_orthogonal {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ) :
    ∑' k : ℤ, (gridSample φ (2 * Real.pi / L) α k).re
        * (gridSample φ (2 * Real.pi / L) α k).im = 0 := by
  have hsum := summable_gridSample_sq hφ hL α
  have h := congrArg Complex.im (gridSample_sq_tsum hφ hev hL h2R α)
  rw [Complex.im_tsum hsum] at h
  have hpt : ∀ k : ℤ, (gridSample φ (2 * Real.pi / L) α k ^ 2).im
      = 2 * ((gridSample φ (2 * Real.pi / L) α k).re
        * (gridSample φ (2 * Real.pi / L) α k).im) := by
    intro k
    simp [sq, Complex.mul_im]
    ring
  rw [tsum_congr hpt, tsum_mul_left] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    add_zero] at h
  linarith

/-! ### The plateau lower bound for the total mass -/

/-- A taper with a plateau of half-width `a` has squared mass at least `2a`. -/
theorem integral_sq_ge_plateau {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) {a : ℝ}
    (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) :
    2 * a ≤ ∫ u : ℝ, φ u ^ 2 := by
  have hfint : Integrable fun u => φ u ^ 2 := hφ.integrable_sq
  have hrestrict : ∫ u in Set.Icc (-a) a, φ u ^ 2 ≤ ∫ u : ℝ, φ u ^ 2 :=
    setIntegral_le_integral hfint (Filter.Eventually.of_forall fun u => sq_nonneg _)
  have hone : ∫ u in Set.Icc (-a) a, φ u ^ 2 = ∫ _u in Set.Icc (-a) a, (1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    rw [hplat u (abs_le.2 ⟨hu.1, hu.2⟩)]
    norm_num
  have hval : ∫ _u in Set.Icc (-a) a, (1 : ℝ) = 2 * a := by
    rw [setIntegral_const]
    simp only [Real.volume_real_Icc, smul_eq_mul, mul_one, sub_neg_eq_add]
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ a + a)]
    ring
  rw [hone, hval] at hrestrict
  exact hrestrict

/-! ### The explicit transverse surplus floor -/

/-- **Strict positivity of the lattice channel gap for an off-line offset.** -/
theorem latticeChannelGap_pos {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 0 < a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {α : ℝ} (hα : α ≠ 0) :
    0 < latticeChannelGap φ L α := by
  rw [latticeChannelGap_eq hφ hev hL h2R α]
  have hE : 0 < taperExcess φ α :=
    (taperExcess_pos_iff hφ.toCompactTaper ha hplat α).2 hα
  have hP : 2 * a ≤ ∫ t : ℝ, φ t ^ 2 := integral_sq_ge_plateau hφ.toCompactTaper ha.le hplat
  have hP0 : 0 < ∫ t : ℝ, φ t ^ 2 := by linarith
  positivity

/-- **Explicit floor for the lattice channel gap in the source regime.**

For a plateau of half-width `a ≥ 3L/8` (the source regime `8w ≤ L`),

  `H² - |S|² ≥ (27/256) L⁶ α²`. -/
theorem latticeChannelGap_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    27 / 256 * L ^ 6 * α ^ 2 ≤ latticeChannelGap φ L α := by
  have ha0 : 0 < a := by linarith
  rw [latticeChannelGap_eq hφ hev hL h2R α]
  -- the mass bound
  have hP : 2 * a ≤ ∫ t : ℝ, φ t ^ 2 := integral_sq_ge_plateau hφ.toCompactTaper ha0.le hplat
  have hP34 : 3 * L / 4 ≤ ∫ t : ℝ, φ t ^ 2 := by linarith
  -- the excess bound
  have hE0 : 0 ≤ taperExcess φ α := taperExcess_nonneg φ α
  have hE : 9 / 128 * L ^ 3 * α ^ 2 ≤ taperExcess φ α := by
    have h := transverseDefect_lower_source_regime hφ.toCompactTaper hL ha hplat α
    have hLpos : 0 < L := hL
    nlinarith [h]
  set P := ∫ t : ℝ, φ t ^ 2 with hPdef
  set E := taperExcess φ α with hEdef
  have hL3 : 0 < L ^ 3 := by positivity
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  have hkey : 2 * (3 * L / 4) * (9 / 128 * L ^ 3 * α ^ 2) ≤ E * (2 * P + E) := by
    nlinarith [hE, hP34, hE0, hα2, hL.le]
  nlinarith [hkey, sq_nonneg L, hL.le]

/-- **Explicit transverse surplus floor.**

For the whole centred lattice and a taper with plateau half-width `a ≥ 3L/8`,
the transverse surplus of the pair block of a zero at transverse offset `α`
obeys

  `2m² (H² - |S|²) ≥ (27/128) m² L⁶ α²`.

This is a genuine lower bound for the Gram determinant, i.e. it certifies that
the real and imaginary coordinate vectors of an off-line zero are *not*
parallel — the input a lower bound for `b·b` alone cannot give. -/
theorem latticeTransverseSurplus_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (m α : ℝ) :
    27 / 128 * m ^ 2 * L ^ 6 * α ^ 2 ≤ 2 * m ^ 2 * latticeChannelGap φ L α := by
  have h := latticeChannelGap_floor hφ hev hL h2R ha hplat α
  nlinarith [sq_nonneg m, h]

end RiemannAnalytic
