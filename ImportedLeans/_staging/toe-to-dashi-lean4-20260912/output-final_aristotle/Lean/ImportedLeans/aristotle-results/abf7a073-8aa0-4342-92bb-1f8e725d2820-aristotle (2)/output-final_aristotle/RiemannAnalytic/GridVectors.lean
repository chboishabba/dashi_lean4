/-
The bridge between the grid samples and the Frobenius pair-block algebra.

`FrobeniusDecomposition.lean` works with real coordinate vectors `a`, `b` and
the pair blocks `Q = 2m(aaᵀ - bbᵀ)`.  In the Alpöge--Furman geometry those
vectors are the real and imaginary parts of the finite evaluation vector of a
hypothetical zero,

  `u_ρ(k) = φ̂(z_ρ + k h)`,  `0 ≤ k < d`.

This file introduces those finite vectors and proves that the abstract algebra
is literally the grid algebra:

* `cvec_reOf_imOf` — the complex vector reassembled from its real and imaginary
  parts is the original evaluation vector;
* `gridPairBlock_frobInner` — the Frobenius inner product of two pair blocks is
  `2 m m' Re (S² + H²)` with `S = ∑_k u_k v_k` and `H = ∑_k u_k conj v_k` the
  *finite-window* bilinear and Hermitian channels;
* `imOf_dotProduct_self` — the `b·b` entry of the Gram data is exactly the
  retained transverse energy of the finite window, the quantity bounded below
  in `GridTail.lean`;
* `gridVec_eq_gridSample` — for the centred coordinate `z = -iα` the finite
  vector is the finite window of the centred grid samples.
-/
import RiemannAnalytic.FrobeniusDecomposition
import RiemannAnalytic.GridTail

namespace RiemannAnalytic

open Matrix Complex Finset

variable {d : ℕ}

/-- The finite evaluation vector of a zero coordinate on the grid of spacing
`h`: `u(k) = φ̂(z + k h)`, `0 ≤ k < d`. -/
noncomputable def gridVec (φ : ℝ → ℝ) (h : ℝ) (z : ℂ) (d : ℕ) : Fin d → ℂ :=
  fun k => PhiExt φ (z + ((k : ℕ) : ℝ) * h)

/-- Real part of a complex vector. -/
def reOf (u : Fin d → ℂ) : Fin d → ℝ := fun k => (u k).re

/-- Imaginary part of a complex vector. -/
def imOf (u : Fin d → ℂ) : Fin d → ℝ := fun k => (u k).im

/-- Reassembling a complex vector from its real and imaginary parts. -/
theorem cvec_reOf_imOf (u : Fin d → ℂ) : cvec (reOf u) (imOf u) = u := by
  funext k
  simp [cvec, reOf, imOf, Complex.ext_iff]

/-- The finite-window bilinear channel. -/
theorem Sbil_eq_sum (u v : Fin d → ℂ) : Sbil u v = ∑ k, u k * v k := rfl

/-- The finite-window Hermitian channel. -/
theorem Hsesq_eq_sum (u v : Fin d → ℂ) :
    Hsesq u v = ∑ k, u k * (starRingEnd ℂ) (v k) := rfl

/-- **The pair-block Frobenius inner product in grid coordinates.** -/
theorem gridPairBlock_frobInner (m m' : ℝ) (u v : Fin d → ℂ) :
    frobInner (pairBlock m (reOf u) (imOf u)) (pairBlock m' (reOf v) (imOf v))
      = 2 * m * m' * (((∑ k, u k * v k)) ^ 2
          + ((∑ k, u k * (starRingEnd ℂ) (v k))) ^ 2).re := by
  rw [pairPair_frobInner_channels, cvec_reOf_imOf, cvec_reOf_imOf, Sbil_eq_sum, Hsesq_eq_sum]

/-- **Mixed interference of two finite windows.**  The two imaginary channels
carry exactly twice the mixed interference weight of the pair. -/
theorem gridMixedChannel_parseval (u v : Fin d → ℂ) :
    (∑ k, u k * v k).im ^ 2 + (∑ k, u k * (starRingEnd ℂ) (v k)).im ^ 2
      = 2 * ((reOf u ⬝ᵥ imOf v) ^ 2 + (imOf u ⬝ᵥ reOf v) ^ 2) := by
  have h := mixedChannel_parseval (reOf u) (imOf u) (reOf v) (imOf v)
  rwa [cvec_reOf_imOf, cvec_reOf_imOf, Sbil_eq_sum, Hsesq_eq_sum] at h

/-- The `b·b` Gram entry of the pair data is the retained transverse energy of
the finite window. -/
theorem imOf_dotProduct_self (u : Fin d → ℂ) :
    imOf u ⬝ᵥ imOf u = ∑ k, (u k).im ^ 2 := by
  simp [dotProduct, imOf, sq]

/-- The `a·a` Gram entry is the retained longitudinal energy. -/
theorem reOf_dotProduct_self (u : Fin d → ℂ) :
    reOf u ⬝ᵥ reOf u = ∑ k, (u k).re ^ 2 := by
  simp [dotProduct, reOf, sq]

/-- Together they are the retained total energy. -/
theorem reOf_add_imOf_dotProduct (u : Fin d → ℂ) :
    reOf u ⬝ᵥ reOf u + imOf u ⬝ᵥ imOf u = ∑ k, ‖u k‖ ^ 2 := by
  rw [reOf_dotProduct_self, imOf_dotProduct_self, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, sq]

/-- For the centred coordinate `z = -iα` the finite evaluation vector consists
of the first `d` centred grid samples. -/
theorem gridVec_eq_gridSample (φ : ℝ → ℝ) (h α : ℝ) (d : ℕ) (k : Fin d) :
    gridVec φ h (-(Complex.I * (α : ℂ))) d k = gridSample φ h α (k : ℕ) := by
  unfold gridVec gridSample
  congr 1
  push_cast
  ring

/-- **The transverse surplus of a grid pair block.**  It is `8m²` times the Gram
determinant of the retained real and imaginary energies; in particular it is
controlled by the retained transverse energy `∑_k (Im u_k)²` of `GridTail`. -/
theorem gridTransverseSurplus_eq (m : ℝ) (u : Fin d → ℂ) :
    transverseSurplus m (reOf u) (imOf u)
      = 8 * m ^ 2 * ((∑ k, (u k).re ^ 2) * (∑ k, (u k).im ^ 2)
          - (reOf u ⬝ᵥ imOf u) ^ 2) := by
  unfold transverseSurplus
  rw [reOf_dotProduct_self, imOf_dotProduct_self]

/-- The critical baseline of a grid pair block in the same coordinates. -/
theorem gridCriticalBaseline_eq (m : ℝ) (u : Fin d → ℂ) :
    criticalBaseline m (reOf u) (imOf u)
      = 4 * m ^ 2 * ((∑ k, (u k).re ^ 2) - ∑ k, (u k).im ^ 2) ^ 2 := by
  unfold criticalBaseline
  rw [reOf_dotProduct_self, imOf_dotProduct_self]

/-! ### The retained transverse energy is the `b·b` Gram entry -/

/-- For a real even taper the finite evaluation vector of the centred
coordinate has `b·b` equal to the one-sided window energy of `GridTail`: the
central sample is real, so the window `0 ≤ k < m+1` contributes exactly the
same as the one-sided window `1 ≤ k ≤ m`. -/
theorem imOf_gridVec_eq_window_sum (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ)
    (m : ℕ) :
    imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
        ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
      = ∑ n ∈ range m, transverseEnergy φ h α ((n : ℤ) + 1) := by
  rw [imOf_dotProduct_self]
  have hpt : ∀ k : Fin (m + 1),
      (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1) k).im ^ 2
        = (gridSample φ h α ((k : ℕ) : ℤ)).im ^ 2 := by
    intro k
    rw [gridVec_eq_gridSample]
  rw [Finset.sum_congr rfl fun k _ => hpt k]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => (gridSample φ h α (n : ℤ)).im ^ 2) (m + 1),
    Finset.sum_range_succ' (fun n : ℕ => (gridSample φ h α (n : ℤ)).im ^ 2) m]
  have hzero : (gridSample φ h α ((0 : ℕ) : ℤ)).im ^ 2 = 0 := by
    have := gridSample_zero_im φ hev h α
    simp [this]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [transverseEnergy]

/-- **Explicit lower bound for the transverse Gram entry of a grid pair block.**

For a `C¹` real even taper supported in `[-R, R]` with `2R ≤ L` and grid
spacing `h = 2π/L`, the `b·b` entry of the finite evaluation vector at the
off-line coordinate `-iα` obeys the explicit lower bound of `GridTail`. -/
theorem imOf_gridVec_lower {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L) (α : ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ imOf (gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) (m + 1))
          ⬝ᵥ imOf (gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) (m + 1)) := by
  rw [imOf_gridVec_eq_window_sum φ hev]
  exact transverseEnergy_window_lower hφ hev hL h2R α hm

end RiemannAnalytic
