import Mathlib
import RequestProject.EuclidTiling
import RequestProject.DeltaFrobenius

/-!
# The palette traces of the filling, and their character table

`RequestProject/EuclidTiling.lean` filled the whole plane with Euclid's ternary triangles: ring
`j` is the fan of the `n`-gon of circumradius `3 ^ j`, sector `k` is one of its `n` triangles,
and each sector is cut to depth `d` into `9 ^ d` parts, each of which is read by `‖Δ‖` at its
centroid (`DeltaTriangles.reading`).

This file samples that filling into a matrix and analyses it the way Frobenius analysed a
finite group.

**The matrix.** The *palette trace* of ring `j`, sector `k` is the sum of the `9 ^ d` readings
of that sector (`paletteTrace`); collecting them for `j < N` and `k < n` gives the real matrix
`traceMatrix` — `N` rows, one per ring, `n` columns, one per sector.

**The group.** Turning the frame by `2π/n` shifts the sectors cyclically
(`paletteTrace_rot`), and the sector index is only defined modulo `n`
(`paletteTrace_periodic`). So the symmetry acting on the columns of the matrix is the cyclic
group `C_n`, whose irreducible characters are the `n` maps `k ↦ ζ^{ak}`, `ζ = e^{2πi/n}`
(`chi`).

**The character table.** `charTable n a k = ζ^{ak}` is the `n × n` character table of `C_n`;
it is symmetric (`charTable_symm`), has unimodular entries (`norm_charTable`), has the trivial
character in its first row (`charTable_zero_left`), and satisfies both orthogonality relations
(`charTable_row_orthogonality`, `charTable_col_orthogonality`). Its `3, 6, 9` structure is
`chi_scale`: the rows of the table of `C_9` with index divisible by three are exactly the table
of `C_3`, so the `9`-gon's table contains the `3`-gon's, just as the rings themselves are
nested.

**The analysis.** `paletteCoeff` decomposes each row of `traceMatrix` in the character table —
the finite Fourier transform of the palette — and:

* `paletteTrace_eq_sum` (Fourier inversion): the palette trace is recovered from its character
  coefficients;
* `sum_normSq_paletteCoeff` (Plancherel) and `frobNormC_paletteChar`: the coefficient matrix has
  Frobenius norm `√n` times that of the trace matrix — the character table is `√n` times a
  unitary;
* `paletteCoeff_rot`: turning the frame by `2π/n` multiplies the `a`-th coefficient by the
  single scalar `ζ^a`, so the character table *diagonalises the spin*, and the coefficients'
  absolute values are constants of the animation (`norm_paletteCoeff_rot`).

**The mirror.** The vertical mirror `z ↦ −z̄` of `DeltaModular.Delta_neg_conj` carries sector `k`
of the still filling onto sector `−1−k` with its vertices exchanged (`conjTri_fanTri`,
`ringTri_mirror`), and Euclid's cut does not see that exchange (`child_swapTri`), so the palette
of the still filling is a palindrome, `f(−1−k) = f(k)` (`paletteTrace_mirror`). In the character
table this pins every coefficient to a line through the origin: `c(a) = ζ^a · conj c(a)`
(`fourierCoeff_mirror`, `paletteCoeff_mirror`).
-/

noncomputable section

set_option maxHeartbeats 1000000

open Complex Real

open scoped Real BigOperators

namespace PaletteCharacterTable

open DeltaTriangles EuclidTiling

/-! ### Reading `Δ` on a tile anywhere in the plane -/

/-- The upper-half-plane representative of a point, by reflection in the real axis. `Δ` lives on
the upper half plane, and the filling covers the whole plane, so a tile below the axis is read
at the reflected point. -/
def reflUp (z : ℂ) : ℂ := if 0 < z.im then z else (starRingEnd ℂ) z

@[simp] theorem reflUp_of_pos {z : ℂ} (hz : 0 < z.im) : reflUp z = z := if_pos hz

/-- Off the real axis the representative really is in the upper half plane. -/
theorem im_reflUp_pos {z : ℂ} (hz : z.im ≠ 0) : 0 < (reflUp z).im := by
  by_cases h : 0 < z.im
  · simp [reflUp, h]
  · have : z.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    simp only [reflUp, if_neg h, Complex.conj_im]
    linarith

/-- The representative is blind to the reflection in the real axis. -/
theorem reflUp_conj (z : ℂ) : reflUp ((starRingEnd ℂ) z) = reflUp z := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · have h1 : 0 < ((starRingEnd ℂ) z).im := by simpa using h
    have h2 : ¬ (0 < z.im) := not_lt.2 h.le
    rw [reflUp, reflUp, if_pos h1, if_neg h2]
  · have hz : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.2 h
    rw [hz]
  · have h1 : ¬ (0 < ((starRingEnd ℂ) z).im) := by
      simp only [Complex.conj_im]
      linarith
    rw [reflUp, reflUp, if_neg h1, if_pos h, Complex.conj_conj]

/-- **The reading of a tile**, anywhere in the plane: `‖Δ‖` at the upper-half-plane
representative of its centroid. Above the axis this is the reading of
`RequestProject/DeltaTriangles.lean`. -/
def readingRefl (T : Tri) : ℝ :=
  if (centroidT T).im = 0 then 0 else ‖DeltaModular.Delta (reflUp (centroidT T))‖

theorem readingRefl_eq_reading {T : Tri} (h : 0 < (centroidT T).im) :
    readingRefl T = reading T := by
  rw [readingRefl, if_neg h.ne', reflUp_of_pos h, reading]

/-- **The mirror does not change a reading.** The vertical mirror `z ↦ −z̄` of
`DeltaModular.Delta_neg_conj` leaves `‖Δ‖` unchanged, above the axis and below it. -/
theorem readingRefl_conjTri (T : Tri) : readingRefl (conjTri T) = readingRefl T := by
  set c : ℂ := centroidT T with hc
  have hcent : centroidT (conjTri T) = -(starRingEnd ℂ) c := centroidT_conjTri T
  have him : (-(starRingEnd ℂ) c).im = c.im := by simp
  rcases lt_trichotomy c.im 0 with h | h | h
  · have h1 : (-(starRingEnd ℂ) c).im ≠ 0 := by rw [him]; exact h.ne
    rw [readingRefl, readingRefl, ← hc, hcent, if_neg h1, if_neg h.ne]
    have e1 : reflUp (-(starRingEnd ℂ) c) = -c := by
      rw [reflUp, if_neg (by rw [him]; exact not_lt.2 h.le)]
      simp
    have e2 : reflUp c = (starRingEnd ℂ) c := by rw [reflUp, if_neg (not_lt.2 h.le)]
    have hw : 0 < ((starRingEnd ℂ) c).im := by
      simp only [Complex.conj_im]
      linarith
    have hd := DeltaModular.Delta_neg_conj hw
    rw [show (-(starRingEnd ℂ) ((starRingEnd ℂ) c)) = -c by simp] at hd
    rw [e1, e2, hd, RCLike.norm_conj]
  · rw [readingRefl, readingRefl, ← hc, hcent, if_pos (by rw [him]; exact h), if_pos h]
  · have h1 : (-(starRingEnd ℂ) c).im ≠ 0 := by rw [him]; exact h.ne'
    rw [readingRefl, readingRefl, ← hc, hcent, if_neg h1, if_neg h.ne']
    rw [reflUp_of_pos (by rw [him]; exact h), reflUp_of_pos h, DeltaModular.Delta_neg_conj h,
      RCLike.norm_conj]

/-! ### Relabelling a triangle, and the nine parts -/

/-- The same triangle with its last two vertices exchanged. -/
def swapTri (T : Tri) : Tri := (T.1, T.2.2, T.2.1)

@[simp] theorem swapTri_swapTri (T : Tri) : swapTri (swapTri T) = T := rfl

theorem swapTri_mapTri (a b : ℂ) (T : Tri) : swapTri (mapTri a b T) = mapTri a b (swapTri T) := rfl

/-- The permutation of the nine parts induced by exchanging two vertices: it swaps the parts
with exchanged barycentric parameters, and is an involution. -/
def sigma9 : Fin 9 → Fin 9 := ![0, 3, 5, 1, 4, 2, 6, 8, 7]

theorem sigma9_involutive (i : Fin 9) : sigma9 (sigma9 i) = i := by fin_cases i <;> rfl

/-- **Euclid's cut does not see the labelling of the vertices**: exchanging two vertices
permutes the nine parts. -/
theorem child_swapTri (i : Fin 9) (T : Tri) :
    child i (swapTri T) = swapTri (child (sigma9 i) T) := by
  fin_cases i <;>
    (refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp [child, affTri, para, swapTri, childP, sigma9] <;> ring)

theorem desc_swapTri (w : List (Fin 9)) (T : Tri) :
    desc w (swapTri T) = swapTri (desc (w.map sigma9) T) := by
  induction w generalizing T with
  | nil => rfl
  | cons i w ih => rw [desc_cons, child_swapTri, ih, List.map_cons, desc_cons]

@[simp] theorem centroidT_swapTri (T : Tri) : centroidT (swapTri T) = centroidT T := by
  simp only [centroidT, swapTri]
  ring

@[simp] theorem readingRefl_swapTri (T : Tri) : readingRefl (swapTri T) = readingRefl T := by
  rw [readingRefl, readingRefl, centroidT_swapTri]

/-! ### The mirror of the filling -/

/-- The vertical mirror sends the `k`-th vertex of the still frame to the `−k`-th. -/
theorem neg_conj_spinVertex (n : ℕ) (k : ℤ) :
    -(starRingEnd ℂ) (ArchimedesDelta.spinVertex n 0 k) = ArchimedesDelta.spinVertex n 0 (-k) := by
  have hang : (π : ℝ) - ArchimedesDelta.spinAngle n 0 k = ArchimedesDelta.spinAngle n 0 (-k) := by
    rw [ArchimedesDelta.spinAngle_def, ArchimedesDelta.spinAngle_def]
    push_cast
    ring
  unfold ArchimedesDelta.spinVertex
  set θ : ℝ := ArchimedesDelta.spinAngle n 0 k with hθ
  have h1 : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [h1, ← hang]
  have h2 : (((π - θ : ℝ)) : ℂ) * Complex.I
      = ((π : ℝ) : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **The mirror of a sector is a sector.** The vertical mirror carries the `k`-th triangle of
the still fan onto the `(−1−k)`-th, with its two vertices exchanged. -/
theorem conjTri_fanTri (n : ℕ) (k : ℤ) :
    conjTri (fanTri n 0 k) = swapTri (fanTri n 0 (-1 - k)) := by
  have h1 := neg_conj_spinVertex n k
  have h2 := neg_conj_spinVertex n (k + 1)
  simp only [conjTri, fanTri, swapTri, h1, h2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · show ArchimedesDelta.spinVertex n 0 (-k) = ArchimedesDelta.spinVertex n 0 (-1 - k + 1)
    congr 1
    ring
  · show ArchimedesDelta.spinVertex n 0 (-(k + 1)) = ArchimedesDelta.spinVertex n 0 (-1 - k)
    congr 1
    ring

theorem conjTri_mapTri_real (a : ℝ) (T : Tri) :
    conjTri (mapTri (a : ℂ) 0 T) = mapTri (a : ℂ) 0 (conjTri T) := by
  simp only [conjTri, mapTri, map_add, map_mul, Complex.conj_ofReal]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- The same for a whole ring of the filling. -/
theorem ringTri_mirror (n : ℕ) (j : ℕ) (k : ℤ) :
    ringTri n 0 j (-1 - k) = swapTri (conjTri (ringTri n 0 j k)) := by
  have hcast : ((3 : ℂ) ^ j) = (((3 : ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
  rw [ringTri, ringTri, hcast, conjTri_mapTri_real, conjTri_fanTri, swapTri_mapTri,
    swapTri_swapTri]

/-! ### The palette trace of a sector, and the trace matrix -/

/-- **The palette trace.** The sum of the `9 ^ d` readings `‖Δ‖` of the depth-`d` parts of
sector `k` of ring `j`. -/
def paletteTrace (n : ℕ) (t : ℝ) (d : ℕ) (j : ℕ) (k : ℤ) : ℝ :=
  ∑ v : Fin d → Fin 9, readingRefl (tile n t j k (List.ofFn v))

theorem readingRefl_nonneg (T : Tri) : 0 ≤ readingRefl T := by
  rw [readingRefl]
  split
  · exact le_rfl
  · exact norm_nonneg _

theorem paletteTrace_nonneg (n : ℕ) (t : ℝ) (d j : ℕ) (k : ℤ) : 0 ≤ paletteTrace n t d j k :=
  Finset.sum_nonneg fun _ _ => readingRefl_nonneg _

/-- Sector indices only matter modulo `n`. -/
theorem ringTri_periodic {n : ℕ} (hn : 0 < n) (t : ℝ) (j : ℕ) (k : ℤ) :
    ringTri n t j (k + n) = ringTri n t j k := by
  have h1 : ArchimedesDelta.spinVertex n t (k + n) = ArchimedesDelta.spinVertex n t k :=
    DeltaTriangles.spinVertex_add_nat n hn t k
  have h2 : ArchimedesDelta.spinVertex n t (k + n + 1) = ArchimedesDelta.spinVertex n t (k + 1) := by
    have h := DeltaTriangles.spinVertex_add_nat n hn t (k + 1)
    rw [show k + 1 + (n : ℤ) = k + n + 1 by ring] at h
    exact h
  simp only [ringTri, fanTri, h1, h2]

theorem paletteTrace_periodic {n : ℕ} (hn : 0 < n) (t : ℝ) (d j : ℕ) (k : ℤ) :
    paletteTrace n t d j (k + n) = paletteTrace n t d j k := by
  simp only [paletteTrace, tile, ringTri_periodic hn t j k]

/-- Turning the frame by `2π/n` shifts the sectors by one. -/
theorem paletteTrace_rot {n : ℕ} (hn : 0 < n) (t : ℝ) (d j : ℕ) (k : ℤ) :
    paletteTrace n (t + 2 * π / n) d j k = paletteTrace n t d j (k + 1) := by
  simp only [paletteTrace, tile, ringTri, fanTri_shift n hn t k]

/-- The involution of the words of length `d` induced by `sigma9`. -/
def wordPerm (d : ℕ) : (Fin d → Fin 9) ≃ (Fin d → Fin 9) where
  toFun v := sigma9 ∘ v
  invFun v := sigma9 ∘ v
  left_inv v := by funext i; exact sigma9_involutive (v i)
  right_inv v := by funext i; exact sigma9_involutive (v i)

/-- **The palette of the still filling is a palindrome.** The mirror `z ↦ −z̄` exchanges the
sectors `k` and `−1−k` of every ring and changes no reading, so the two sectors carry the same
palette trace. -/
theorem paletteTrace_mirror (n : ℕ) (d j : ℕ) (k : ℤ) :
    paletteTrace n 0 d j (-1 - k) = paletteTrace n 0 d j k := by
  have hterm : ∀ v : Fin d → Fin 9,
      readingRefl (tile n 0 j (-1 - k) (List.ofFn v))
        = readingRefl (tile n 0 j k (List.ofFn (wordPerm d v))) := by
    intro v
    rw [tile, ringTri_mirror, desc_swapTri, readingRefl_swapTri, desc_conjTri,
      readingRefl_conjTri, tile]
    congr 2
    rw [List.map_ofFn]
    rfl
  calc paletteTrace n 0 d j (-1 - k)
      = ∑ v : Fin d → Fin 9, readingRefl (tile n 0 j k (List.ofFn (wordPerm d v))) :=
        Finset.sum_congr rfl fun v _ => hterm v
    _ = ∑ v : Fin d → Fin 9, readingRefl (tile n 0 j k (List.ofFn v)) :=
        Fintype.sum_equiv (wordPerm d) _ _ fun v => rfl
    _ = paletteTrace n 0 d j k := rfl

/-- **The matrix of palette traces**: `N` rings by `n` sectors. -/
def traceMatrix (n : ℕ) (t : ℝ) (d N : ℕ) : Fin N → Fin n → ℝ :=
  fun j k => paletteTrace n t d (j : ℕ) ((k : ℕ) : ℤ)

/-! ### The characters of the cyclic group of sectors -/

/-- The primitive `n`-th root of unity. -/
def zeta (n : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / n)

theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  have h : (2 * (π : ℂ) * Complex.I / (n : ℂ)) = ((2 * π / n : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [zeta, h, Complex.norm_exp_ofReal_mul_I]

theorem isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem zeta_pow_self {n : ℕ} (hn : n ≠ 0) : zeta n ^ n = 1 := (isPrimitiveRoot_zeta hn).pow_eq_one

/-- **The characters of `C_n`.** `chi n a k = ζ^{ak}` is the value of the `a`-th irreducible
character of the cyclic group of sectors at the sector `k`. -/
def chi (n : ℕ) (a k : ℤ) : ℂ := zeta n ^ (a * k)

@[simp] theorem chi_zero_left (n : ℕ) (k : ℤ) : chi n 0 k = 1 := by simp [chi]

@[simp] theorem chi_zero_right (n : ℕ) (a : ℤ) : chi n a 0 = 1 := by simp [chi]

theorem chi_ne_zero (n : ℕ) (a k : ℤ) : chi n a k ≠ 0 := zpow_ne_zero _ (zeta_ne_zero n)

/-- The character table is symmetric in its two indices. -/
theorem chi_symm (n : ℕ) (a k : ℤ) : chi n a k = chi n k a := by rw [chi, chi, mul_comm]

/-- Each character is a homomorphism of the group of sectors. -/
theorem chi_add_right (n : ℕ) (a k l : ℤ) : chi n a (k + l) = chi n a k * chi n a l := by
  rw [chi, chi, chi, mul_add, zpow_add₀ (zeta_ne_zero n)]

@[simp] theorem norm_chi (n : ℕ) (a k : ℤ) : ‖chi n a k‖ = 1 := by
  rw [chi, norm_zpow, norm_zeta, one_zpow]

/-- Conjugating a character value inverts the sector. -/
theorem conj_chi (n : ℕ) (a k : ℤ) : (starRingEnd ℂ) (chi n a k) = chi n a (-k) := by
  rw [chi, chi, map_zpow₀, ← Complex.inv_eq_conj (norm_zeta n), inv_zpow, ← zpow_neg]
  congr 1
  ring

theorem chi_mul_conj (n : ℕ) (a k l : ℤ) :
    chi n a k * (starRingEnd ℂ) (chi n a l) = chi n a (k - l) := by
  rw [conj_chi, ← chi_add_right, sub_eq_add_neg]

/-- Sector indices only matter modulo `n`, for the characters too. -/
theorem chi_periodic {n : ℕ} (hn : n ≠ 0) (a k : ℤ) : chi n a (k + n) = chi n a k := by
  have h : chi n a (n : ℤ) = 1 := by
    rw [chi, mul_comm, zpow_mul, zpow_natCast, zeta_pow_self hn, one_zpow]
  rw [chi_add_right, h, mul_one]

/-- A character is trivial exactly when its index is a multiple of `n`. -/
theorem chi_one_eq_one_iff {n : ℕ} (hn : n ≠ 0) (a : ℤ) : chi n a 1 = 1 ↔ (n : ℤ) ∣ a := by
  rw [chi, mul_one]
  exact (isPrimitiveRoot_zeta hn).zpow_eq_one_iff_dvd a

theorem chi_natCast (n : ℕ) (a : ℤ) (k : ℕ) : chi n a (k : ℤ) = chi n a 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [h, chi_add_right, ih, pow_succ]

/-- **The orthogonality sum.** Summing one character over all sectors gives `n` for the trivial
character and `0` for every other. -/
theorem sum_chi {n : ℕ} (hn : n ≠ 0) (a : ℤ) :
    ∑ k ∈ Finset.range n, chi n a (k : ℤ) = if (n : ℤ) ∣ a then (n : ℂ) else 0 := by
  by_cases hd : (n : ℤ) ∣ a
  · have h1 : chi n a 1 = 1 := (chi_one_eq_one_iff hn a).2 hd
    have h : ∀ k ∈ Finset.range n, chi n a (k : ℤ) = 1 := by
      intro k _
      rw [chi_natCast, h1, one_pow]
    rw [Finset.sum_congr rfl h, if_pos hd]
    simp
  · have h1 : chi n a 1 ≠ 1 := fun h => hd ((chi_one_eq_one_iff hn a).1 h)
    have hpow : chi n a 1 ^ n = 1 := by
      have h2 := chi_periodic hn a 0
      rw [zero_add, chi_zero_right] at h2
      rw [← chi_natCast, h2]
    have h : ∀ k ∈ Finset.range n, chi n a (k : ℤ) = chi n a 1 ^ k :=
      fun k _ => chi_natCast n a k
    rw [Finset.sum_congr rfl h, geom_sum_eq h1, hpow, if_neg hd]
    simp

/-- The same sum in the other index: the columns of the table sum the same way. -/
theorem sum_chi_left {n : ℕ} (hn : n ≠ 0) (k : ℤ) :
    ∑ a ∈ Finset.range n, chi n (a : ℤ) k = if (n : ℤ) ∣ k then (n : ℂ) else 0 := by
  have h : ∀ a ∈ Finset.range n, chi n (a : ℤ) k = chi n k (a : ℤ) :=
    fun a _ => chi_symm n (a : ℤ) k
  rw [Finset.sum_congr rfl h]
  exact sum_chi hn k

/-! ### The character table of the cyclic group of sectors -/

/-- **The character table of `C_n`**, as Frobenius would tabulate it: rows are the irreducible
characters, columns are the group elements — here, the sectors of a ring. -/
def charTable (n : ℕ) : Fin n → Fin n → ℂ := fun a k => chi n ((a : ℕ) : ℤ) ((k : ℕ) : ℤ)

@[simp] theorem norm_charTable (n : ℕ) (a k : Fin n) : ‖charTable n a k‖ = 1 := norm_chi _ _ _

/-- The first row of the table is the trivial character. -/
theorem charTable_zero_left {n : ℕ} (hn : 0 < n) (k : Fin n) :
    charTable n ⟨0, hn⟩ k = 1 := by simp [charTable]

/-- The table is symmetric. -/
theorem charTable_symm (n : ℕ) (a k : Fin n) : charTable n a k = charTable n k a :=
  chi_symm _ _ _

/-- For indices in `[0, n)` the character is trivial only for the index zero. -/
theorem dvd_iff_eq {n : ℕ} (a b : Fin n) : ((n : ℤ) ∣ ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) ↔ a = b := by
  constructor
  · intro h
    have ha := a.isLt
    have hb := b.isLt
    have habs : |((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)| < (n : ℤ) := by
      rw [abs_lt]
      omega
    have hzero := Int.eq_zero_of_abs_lt_dvd h habs
    have hab : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast hab)
  · rintro rfl
    simp

/-- **Row orthogonality**, the first of Frobenius' relations: two different irreducible
characters of `C_n` are orthogonal, and each has squared length `n`. -/
theorem charTable_row_orthogonality {n : ℕ} (hn : n ≠ 0) (a b : Fin n) :
    ∑ k : Fin n, charTable n a k * (starRingEnd ℂ) (charTable n b k)
      = if a = b then (n : ℂ) else 0 := by
  have hterm : ∀ k : Fin n, charTable n a k * (starRingEnd ℂ) (charTable n b k)
      = chi n (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) ((k : ℕ) : ℤ) := by
    intro k
    simp only [charTable]
    rw [conj_chi, chi, chi, chi, ← zpow_add₀ (zeta_ne_zero n)]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range
    (fun k => chi n (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) (k : ℤ)) n, sum_chi hn]
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg (fun h => hab ((dvd_iff_eq a b).1 h)), if_neg hab]

/-- **Column orthogonality**, the second of Frobenius' relations. -/
theorem charTable_col_orthogonality {n : ℕ} (hn : n ≠ 0) (k l : Fin n) :
    ∑ a : Fin n, charTable n a k * (starRingEnd ℂ) (charTable n a l)
      = if k = l then (n : ℂ) else 0 := by
  have h : ∀ a : Fin n, charTable n a k * (starRingEnd ℂ) (charTable n a l)
      = charTable n k a * (starRingEnd ℂ) (charTable n l a) := by
    intro a
    rw [charTable_symm n a k, charTable_symm n a l]
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  exact charTable_row_orthogonality hn k l

/-- **The `3, 6, 9` structure of the table.** Scaling both the modulus and the character index
by `m` leaves the character unchanged: the rows `3` and `6` of the table of `C_9` are the rows
`1` and `2` of the table of `C_3`, so the table of the `9`-gon contains that of the `3`-gon. -/
theorem chi_scale {m : ℕ} (hm : m ≠ 0) (n : ℕ) (a k : ℤ) :
    chi (m * n) ((m : ℤ) * a) k = chi n a k := by
  have hz : zeta (m * n) ^ (m : ℤ) = zeta n := by
    rw [zeta, zeta, ← Complex.exp_int_mul]
    congr 1
    have hm' : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
    push_cast
    field_simp
  rw [chi, chi, ← hz, ← zpow_mul]
  congr 1
  ring

theorem chi_nine_three (a k : ℤ) : chi 9 (3 * a) k = chi 3 a k := by
  simpa using chi_scale (m := 3) (by norm_num) 3 a k

/-! ### Reading a row of the matrix in the character table -/

/-- **The character coefficients of a row.** The component of a real function of the sector
along the `a`-th irreducible character of the group of sectors: the finite Fourier transform. -/
def fourierCoeff (n : ℕ) (f : ℤ → ℝ) (a : ℤ) : ℂ :=
  ∑ k ∈ Finset.range n, ((f (k : ℤ) : ℝ) : ℂ) * (starRingEnd ℂ) (chi n a (k : ℤ))

/-- **Fourier inversion.** A row is recovered from its character coefficients: the character
table is a complete system for the data on the sectors. -/
theorem fourier_inversion {n : ℕ} (hn : n ≠ 0) (f : ℤ → ℝ) (k : ℕ) (hk : k < n) :
    ∑ a ∈ Finset.range n, fourierCoeff n f (a : ℤ) * chi n (a : ℤ) (k : ℤ)
      = (n : ℂ) * ((f (k : ℤ) : ℝ) : ℂ) := by
  have hexp : ∀ a ∈ Finset.range n, fourierCoeff n f (a : ℤ) * chi n (a : ℤ) (k : ℤ)
      = ∑ l ∈ Finset.range n, ((f (l : ℤ) : ℝ) : ℂ) * chi n ((k : ℤ) - (l : ℤ)) (a : ℤ) := by
    intro a _
    rw [fourierCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h : (starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ)) * chi n (a : ℤ) (k : ℤ)
        = chi n ((k : ℤ) - (l : ℤ)) (a : ℤ) := by
      rw [mul_comm, chi_mul_conj, chi_symm]
    calc ((f (l : ℤ) : ℝ) : ℂ) * (starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ)) * chi n (a : ℤ) (k : ℤ)
        = ((f (l : ℤ) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ)) * chi n (a : ℤ) (k : ℤ)) := by ring
      _ = ((f (l : ℤ) : ℝ) : ℂ) * chi n ((k : ℤ) - (l : ℤ)) (a : ℤ) := by rw [h]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hinner : ∀ l ∈ Finset.range n,
      ∑ a ∈ Finset.range n, ((f (l : ℤ) : ℝ) : ℂ) * chi n ((k : ℤ) - (l : ℤ)) (a : ℤ)
        = if l = k then (n : ℂ) * ((f (k : ℤ) : ℝ) : ℂ) else 0 := by
    intro l hl
    rw [← Finset.mul_sum, sum_chi hn]
    have hl' : l < n := Finset.mem_range.1 hl
    by_cases hlk : l = k
    · subst hlk
      simp [mul_comm]
    · have hnd : ¬ ((n : ℤ) ∣ ((k : ℤ) - (l : ℤ))) := by
        intro h
        have habs : |((k : ℤ) - (l : ℤ))| < (n : ℤ) := by
          rw [abs_lt]; omega
        have := Int.eq_zero_of_abs_lt_dvd h habs
        omega
      rw [if_neg hnd, if_neg hlk, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range n) k,
    if_pos (Finset.mem_range.2 hk)]

/-- **Plancherel.** The squared lengths of the character coefficients of a row add up to `n`
times the squared lengths of its entries. -/
theorem sum_normSq_fourierCoeff {n : ℕ} (hn : n ≠ 0) (f : ℤ → ℝ) :
    ∑ a ∈ Finset.range n, ‖fourierCoeff n f (a : ℤ)‖ ^ 2
      = n * ∑ k ∈ Finset.range n, (f (k : ℤ)) ^ 2 := by
  have hC : ∑ a ∈ Finset.range n, ((‖fourierCoeff n f (a : ℤ)‖ ^ 2 : ℝ) : ℂ)
      = ((n : ℂ)) * ∑ k ∈ Finset.range n, (((f (k : ℤ)) ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ a ∈ Finset.range n, ((‖fourierCoeff n f (a : ℤ)‖ ^ 2 : ℝ) : ℂ)
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            ((f (k : ℤ) : ℝ) : ℂ) * ((f (l : ℤ) : ℝ) : ℂ)
              * chi n (a : ℤ) ((l : ℤ) - (k : ℤ)) := by
      intro a _
      have hmc : ((‖fourierCoeff n f (a : ℤ)‖ ^ 2 : ℝ) : ℂ)
          = fourierCoeff n f (a : ℤ) * (starRingEnd ℂ) (fourierCoeff n f (a : ℤ)) := by
        rw [Complex.mul_conj]
        norm_cast
        rw [Complex.normSq_eq_norm_sq]
      rw [hmc, fourierCoeff, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have hchi : (starRingEnd ℂ) (chi n (a : ℤ) (k : ℤ))
          * (starRingEnd ℂ) ((starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ)))
          = chi n (a : ℤ) ((l : ℤ) - (k : ℤ)) := by
        rw [Complex.conj_conj, mul_comm, chi_mul_conj]
      calc ((f (k : ℤ) : ℝ) : ℂ) * (starRingEnd ℂ) (chi n (a : ℤ) (k : ℤ))
            * ((starRingEnd ℂ) (((f (l : ℤ) : ℝ) : ℂ)
              * (starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ))))
          = ((f (k : ℤ) : ℝ) : ℂ) * ((f (l : ℤ) : ℝ) : ℂ)
              * ((starRingEnd ℂ) (chi n (a : ℤ) (k : ℤ))
                * (starRingEnd ℂ) ((starRingEnd ℂ) (chi n (a : ℤ) (l : ℤ)))) := by
            rw [map_mul, Complex.conj_ofReal]; ring
        _ = ((f (k : ℤ) : ℝ) : ℂ) * ((f (l : ℤ) : ℝ) : ℂ)
              * chi n (a : ℤ) ((l : ℤ) - (k : ℤ)) := by rw [hchi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    have hswap : ∀ k ∈ Finset.range n,
        ∑ a ∈ Finset.range n, ∑ l ∈ Finset.range n,
            ((f (k : ℤ) : ℝ) : ℂ) * ((f (l : ℤ) : ℝ) : ℂ)
              * chi n (a : ℤ) ((l : ℤ) - (k : ℤ))
          = (n : ℂ) * (((f (k : ℤ)) ^ 2 : ℝ) : ℂ) := by
      intro k hk
      rw [Finset.sum_comm]
      have hinner : ∀ l ∈ Finset.range n,
          ∑ a ∈ Finset.range n,
              ((f (k : ℤ) : ℝ) : ℂ) * ((f (l : ℤ) : ℝ) : ℂ)
                * chi n (a : ℤ) ((l : ℤ) - (k : ℤ))
            = if l = k then (n : ℂ) * (((f (k : ℤ)) ^ 2 : ℝ) : ℂ) else 0 := by
        intro l hl
        have hl' : l < n := Finset.mem_range.1 hl
        have hk' : k < n := Finset.mem_range.1 hk
        rw [← Finset.mul_sum]
        have hsum : ∑ a ∈ Finset.range n, chi n (a : ℤ) ((l : ℤ) - (k : ℤ))
            = if (n : ℤ) ∣ ((l : ℤ) - (k : ℤ)) then (n : ℂ) else 0 := sum_chi_left hn _
        rw [hsum]
        by_cases hlk : l = k
        · subst hlk
          simp
          ring
        · have hnd : ¬ ((n : ℤ) ∣ ((l : ℤ) - (k : ℤ))) := by
            intro h
            have habs : |((l : ℤ) - (k : ℤ))| < (n : ℤ) := by rw [abs_lt]; omega
            have := Int.eq_zero_of_abs_lt_dvd h habs
            omega
          rw [if_neg hnd, if_neg hlk, mul_zero]
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range n) k, if_pos hk]
    rw [Finset.sum_congr rfl hswap, Finset.mul_sum]
  have h := hC
  push_cast at h
  exact_mod_cast h

/-- A cyclic shift of a sum of an `n`-periodic function of the sector. -/
theorem sum_range_shift_int {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℤ → M)
    (h : F (n : ℤ) = F 0) :
    ∑ k ∈ Finset.range n, F ((k : ℤ) + 1) = ∑ k ∈ Finset.range n, F (k : ℤ) := by
  cases n with
  | zero => simp
  | succ m =>
      have hg : (fun k : ℕ => F (k : ℤ)) (m + 1) = (fun k : ℕ => F (k : ℤ)) 0 := by
        simpa using h
      have := DeltaTriangles.sum_range_shift (fun k : ℕ => F (k : ℤ)) m hg
      simpa [Nat.cast_add, Nat.cast_one] using this

/-- **The characters diagonalise the cyclic shift.** Shifting the sectors by one multiplies the
`a`-th coefficient of an `n`-periodic row by the single scalar `ζ^a`. -/
theorem fourierCoeff_shift {n : ℕ} (hn : n ≠ 0) (f : ℤ → ℝ) (hper : f (n : ℤ) = f 0) (a : ℤ) :
    fourierCoeff n (fun k => f (k + 1)) a = chi n a 1 * fourierCoeff n f a := by
  set F : ℤ → ℂ := fun k => ((f k : ℝ) : ℂ) * (starRingEnd ℂ) (chi n a k) with hF
  have hFper : F (n : ℤ) = F 0 := by
    have h2 : chi n a (n : ℤ) = chi n a 0 := by
      have := chi_periodic hn a 0
      simpa using this
    rw [hF]
    simp only [hper, h2]
  have hstep : ∀ k ∈ Finset.range n,
      ((f ((k : ℤ) + 1) : ℝ) : ℂ) * (starRingEnd ℂ) (chi n a (k : ℤ))
        = chi n a 1 * F ((k : ℤ) + 1) := by
    intro k _
    have hch : (starRingEnd ℂ) (chi n a (k : ℤ))
        = chi n a 1 * (starRingEnd ℂ) (chi n a ((k : ℤ) + 1)) := by
      rw [conj_chi, conj_chi, ← chi_add_right]
      congr 1
      ring
    rw [hch, hF]
    ring
  rw [fourierCoeff, Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_range_shift_int n F hFper]
  rfl

/-! ### The palette in the character table -/

/-- **The character coefficients of the palette** of ring `j`. -/
def paletteCoeff (n : ℕ) (t : ℝ) (d j : ℕ) (a : ℤ) : ℂ :=
  fourierCoeff n (paletteTrace n t d j) a

/-- **The character table of the filling**: `N` rings by `n` irreducible characters. -/
def paletteChar (n : ℕ) (t : ℝ) (d N : ℕ) : Fin N → Fin n → ℂ :=
  fun j a => paletteCoeff n t d (j : ℕ) ((a : ℕ) : ℤ)

/-- **Fourier inversion for the palette.** Every palette trace is recovered from the character
coefficients of its ring: the character table is a complete system for the palette. -/
theorem paletteTrace_eq_sum {n : ℕ} (hn : n ≠ 0) (t : ℝ) (d j : ℕ) (k : ℕ) (hk : k < n) :
    ∑ a ∈ Finset.range n, paletteCoeff n t d j (a : ℤ) * chi n (a : ℤ) (k : ℤ)
      = (n : ℂ) * ((paletteTrace n t d j (k : ℤ) : ℝ) : ℂ) :=
  fourier_inversion hn (paletteTrace n t d j) k hk

/-- **Plancherel for the palette.** The squared lengths of the character coefficients of a ring
add up to `n` times the squared lengths of its palette traces. -/
theorem sum_normSq_paletteCoeff {n : ℕ} (hn : n ≠ 0) (t : ℝ) (d j : ℕ) :
    ∑ a ∈ Finset.range n, ‖paletteCoeff n t d j (a : ℤ)‖ ^ 2
      = n * ∑ k ∈ Finset.range n, (paletteTrace n t d j (k : ℤ)) ^ 2 :=
  sum_normSq_fourierCoeff hn (paletteTrace n t d j)

/-- The trivial character reads the total palette of the ring: the sum of all `n · 9 ^ d`
readings. -/
theorem paletteCoeff_zero (n : ℕ) (t : ℝ) (d j : ℕ) :
    paletteCoeff n t d j 0
      = ∑ k ∈ Finset.range n, ((paletteTrace n t d j (k : ℤ) : ℝ) : ℂ) := by
  simp [paletteCoeff, fourierCoeff]

/-! ### The Frobenius norm of the two matrices -/

/-- The Frobenius norm of a complex block of pixels. -/
def frobNormC {p q : ℕ} (A : Fin p → Fin q → ℂ) : ℝ :=
  Real.sqrt (∑ r, ∑ c, ‖A r c‖ ^ 2)

/-- **The character table is `√n` times a unitary.** The coefficient matrix of the palette has
Frobenius norm `√n` times that of the trace matrix. -/
theorem frobNormC_paletteChar {n : ℕ} (hn : n ≠ 0) (t : ℝ) (d N : ℕ) :
    frobNormC (paletteChar n t d N)
      = Real.sqrt n * DeltaFrobenius.frobNorm (traceMatrix n t d N) := by
  have hrow : ∀ j : Fin N, ∑ a : Fin n, ‖paletteChar n t d N j a‖ ^ 2
      = n * ∑ k : Fin n, traceMatrix n t d N j k * traceMatrix n t d N j k := by
    intro j
    have h1 : ∑ a : Fin n, ‖paletteChar n t d N j a‖ ^ 2
        = ∑ a ∈ Finset.range n, ‖paletteCoeff n t d (j : ℕ) (a : ℤ)‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun a => ‖paletteCoeff n t d (j : ℕ) (a : ℤ)‖ ^ 2) n
    have h2 : ∑ k : Fin n, traceMatrix n t d N j k * traceMatrix n t d N j k
        = ∑ k ∈ Finset.range n, (paletteTrace n t d (j : ℕ) (k : ℤ)) ^ 2 := by
      simp only [traceMatrix]
      rw [Fin.sum_univ_eq_sum_range
        (fun k => paletteTrace n t d (j : ℕ) (k : ℤ) * paletteTrace n t d (j : ℕ) (k : ℤ)) n]
      exact Finset.sum_congr rfl fun k _ => by rw [sq]
    rw [h1, h2]
    exact sum_normSq_paletteCoeff hn t d (j : ℕ)
  have hsum : ∑ j : Fin N, ∑ a : Fin n, ‖paletteChar n t d N j a‖ ^ 2
      = n * DeltaFrobenius.frobInner (traceMatrix n t d N) (traceMatrix n t d N) := by
    rw [DeltaFrobenius.frobInner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hrow j
  rw [frobNormC, hsum, DeltaFrobenius.frobNorm, ← Real.sqrt_mul (Nat.cast_nonneg n)]

/-! ### The character table diagonalises the spin -/

/-- **The character table diagonalises the spin.** Turning the frame by `2π/n` multiplies the
`a`-th character coefficient of every ring by the single scalar `ζ^a`: in the character basis
the rotation of the plate is diagonal. -/
theorem paletteCoeff_rot {n : ℕ} (hn : 0 < n) (t : ℝ) (d j : ℕ) (a : ℤ) :
    paletteCoeff n (t + 2 * π / n) d j a = chi n a 1 * paletteCoeff n t d j a := by
  have hper : paletteTrace n t d j (n : ℤ) = paletteTrace n t d j 0 := by
    have := paletteTrace_periodic hn t d j 0
    simpa using this
  have hshift : paletteTrace n (t + 2 * π / n) d j = fun k => paletteTrace n t d j (k + 1) := by
    funext k
    exact paletteTrace_rot hn t d j k
  rw [paletteCoeff, paletteCoeff, hshift]
  exact fourierCoeff_shift hn.ne' (paletteTrace n t d j) hper a

/-- Hence the absolute values of the character coefficients are constants of the animation. -/
theorem norm_paletteCoeff_rot {n : ℕ} (hn : 0 < n) (t : ℝ) (d j : ℕ) (a : ℤ) :
    ‖paletteCoeff n (t + 2 * π / n) d j a‖ = ‖paletteCoeff n t d j a‖ := by
  rw [paletteCoeff_rot hn, norm_mul, norm_chi, one_mul]

/-! ### The mirror, in the character table -/

/-- Reflecting the sectors of an `n`-periodic row. -/
theorem sum_range_reflect_int {M : Type*} [AddCommMonoid M] (n : ℕ) (G : ℤ → M)
    (hper : ∀ k : ℤ, G (k + n) = G k) :
    ∑ k ∈ Finset.range n, G (-1 - (k : ℤ)) = ∑ k ∈ Finset.range n, G (k : ℤ) := by
  have h : ∀ k ∈ Finset.range n, G (-1 - (k : ℤ)) = (fun m : ℕ => G (m : ℤ)) (n - 1 - k) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.1 hk
    have hcast : ((n - 1 - k : ℕ) : ℤ) = (-1 - (k : ℤ)) + n := by omega
    simp only [hcast, hper]
  rw [Finset.sum_congr rfl h, Finset.sum_range_reflect (fun m : ℕ => G (m : ℤ)) n]

/-- **The palindrome, read in the character table.** Because the still palette satisfies
`f(−1−k) = f(k)`, each of its character coefficients is pinned to the line `ζ^{a/2}ℝ`: the
coefficient equals `ζ^a` times its own conjugate. -/
theorem fourierCoeff_mirror {n : ℕ} (hn : n ≠ 0) (f : ℤ → ℝ)
    (hper : ∀ k : ℤ, f (k + n) = f k) (hmir : ∀ k : ℤ, f (-1 - k) = f k) (a : ℤ) :
    fourierCoeff n f a = chi n a 1 * (starRingEnd ℂ) (fourierCoeff n f a) := by
  set G : ℤ → ℂ := fun m => ((f m : ℝ) : ℂ) * (starRingEnd ℂ) (chi n a (-1 - m)) with hG
  have hGper : ∀ k : ℤ, G (k + n) = G k := by
    intro k
    have h2 : chi n a (-1 - (k + n)) = chi n a (-1 - k) := by
      have h3 := chi_periodic hn a (-1 - (k + (n : ℤ)))
      rw [show (-1 - (k + (n : ℤ)) + (n : ℤ)) = -1 - k by ring] at h3
      exact h3.symm
    simp only [hG, hper k, h2]
  have hleft : fourierCoeff n f a = ∑ k ∈ Finset.range n, G (-1 - (k : ℤ)) := by
    rw [fourierCoeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hG, show (-1 - (-1 - (k : ℤ))) = (k : ℤ) by ring, hmir (k : ℤ)]
  have hright : chi n a 1 * (starRingEnd ℂ) (fourierCoeff n f a)
      = ∑ k ∈ Finset.range n, G (k : ℤ) := by
    rw [fourierCoeff, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hchi : (starRingEnd ℂ) (chi n a (-1 - (k : ℤ))) = chi n a 1 * chi n a (k : ℤ) := by
      rw [conj_chi, ← chi_add_right]
      congr 1
      ring
    simp only [hG, hchi, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  calc fourierCoeff n f a = ∑ k ∈ Finset.range n, G (-1 - (k : ℤ)) := hleft
    _ = ∑ k ∈ Finset.range n, G (k : ℤ) := sum_range_reflect_int n G hGper
    _ = chi n a 1 * (starRingEnd ℂ) (fourierCoeff n f a) := hright.symm

/-- The palette of the still filling, read in the character table. -/
theorem paletteCoeff_mirror {n : ℕ} (hn : n ≠ 0) (d j : ℕ) (a : ℤ) :
    paletteCoeff n 0 d j a = chi n a 1 * (starRingEnd ℂ) (paletteCoeff n 0 d j a) :=
  fourierCoeff_mirror hn (paletteTrace n 0 d j)
    (fun k => paletteTrace_periodic (Nat.pos_of_ne_zero hn) 0 d j k)
    (fun k => paletteTrace_mirror n d j k) a

end PaletteCharacterTable
