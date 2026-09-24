/-
Exact Frobenius decomposition of the finite zero-side matrix.

Milestone **M1** of the top-down route: expand the finite zero-side Frobenius
square pair by pair and identify the exact transverse diagonal surplus.

For a hypothetical off-critical zero `ρ` with reflection partner, the finite
zero-side matrix contributes the *pair block*

  `Q ρ = 2 m_ρ (a_ρ a_ρᵀ - b_ρ b_ρᵀ)`,

where `u_ρ = a_ρ + i b_ρ` is the (complex) evaluation vector of the zero.
This file proves, for genuine real matrices and genuine dot products:

* `frobInner_vecMulVec`: the Frobenius inner product of two rank-one matrices
  is the product of the two dot products;
* `pairPair_frobInner`: the exact pair-pair Frobenius inner product;
* `pairPair_frobInner_channels`: the same quantity through the bilinear (`S`)
  and sesquilinear (`H`) complex channels, `⟨Q_ρ, Q_σ⟩ = 2 m_ρ m_σ Re(S² + H²)`;
* `mixedChannel_parseval`: `(Im S)² + (Im H)² = 2 N_{ρσ}` with
  `N_{ρσ} = (a_ρ·d_σ)² + (b_ρ·c_σ)²`, the exact "mixed interference" identity;
* `pairBlock_frobSq_decomposition`: the exact splitting of a single pair block
  into a **critical baseline** `4m²(A-B)²` and a **transverse surplus**
  `8m²(AB - C²)`, with `transverseSurplus_nonneg` proving the surplus is
  nonnegative (Cauchy--Schwarz / Gram determinant) and
  `transverseSurplus_pos_of_not_parallel` proving it is strictly positive
  exactly when the two real coordinate vectors are not proportional;
* `A_frobSq_target_decomposition`: for a whole finite family of pair blocks and
  a distinguished target `ρ₀`,

    `‖A‖_F² = criticalBaseline ρ₀ + transverseSurplus ρ₀ + interference ρ₀`

  as a literal identity of real numbers, and
  `transverseSurplus_le_of_interference`, the resulting bound on the retained
  transverse defect.
-/
import Mathlib

namespace RiemannAnalytic

open Finset Matrix Complex

variable {ι : Type*} {n : Type*} [Fintype n]

/-! ### The Frobenius inner product -/

/-- The Frobenius (Hilbert--Schmidt) inner product of two real matrices. -/
def frobInner (X Y : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j

/-- The Frobenius square (squared Hilbert--Schmidt norm) of a real matrix. -/
def frobSq (X : Matrix n n ℝ) : ℝ := frobInner X X

theorem frobInner_comm (X Y : Matrix n n ℝ) : frobInner X Y = frobInner Y X := by
  unfold frobInner
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem frobInner_add_left (X Y Z : Matrix n n ℝ) :
    frobInner (X + Y) Z = frobInner X Z + frobInner Y Z := by
  unfold frobInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [add_mul]

theorem frobInner_add_right (X Y Z : Matrix n n ℝ) :
    frobInner X (Y + Z) = frobInner X Y + frobInner X Z := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm Y X, frobInner_comm Z X]

theorem frobInner_sub_left (X Y Z : Matrix n n ℝ) :
    frobInner (X - Y) Z = frobInner X Z - frobInner Y Z := by
  unfold frobInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [sub_mul]

theorem frobInner_sub_right (X Y Z : Matrix n n ℝ) :
    frobInner X (Y - Z) = frobInner X Y - frobInner X Z := by
  rw [frobInner_comm, frobInner_sub_left, frobInner_comm Y X, frobInner_comm Z X]

theorem frobInner_zero_left (Y : Matrix n n ℝ) : frobInner 0 Y = 0 := by
  simp [frobInner]

theorem frobInner_smul_left (c : ℝ) (X Y : Matrix n n ℝ) :
    frobInner (c • X) Y = c * frobInner X Y := by
  unfold frobInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]

theorem frobInner_smul_right (c : ℝ) (X Y : Matrix n n ℝ) :
    frobInner X (c • Y) = c * frobInner X Y := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm]

/-- The Frobenius inner product is additive over finite sums in its left
argument. -/
theorem frobInner_sum_left (s : Finset ι) (M : ι → Matrix n n ℝ) (Y : Matrix n n ℝ) :
    frobInner (∑ i ∈ s, M i) Y = ∑ i ∈ s, frobInner (M i) Y := by
  classical
  induction s using Finset.induction with
  | empty => simp [frobInner_zero_left]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, frobInner_add_left, ih]

/-- The Frobenius inner product is additive over finite sums in its right
argument. -/
theorem frobInner_sum_right (s : Finset ι) (X : Matrix n n ℝ) (M : ι → Matrix n n ℝ) :
    frobInner X (∑ i ∈ s, M i) = ∑ i ∈ s, frobInner X (M i) := by
  rw [frobInner_comm, frobInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => frobInner_comm _ _

/-- Frobenius inner products of rank-one matrices factor through dot products. -/
theorem frobInner_vecMulVec (a b c d : n → ℝ) :
    frobInner (vecMulVec a b) (vecMulVec c d) = (a ⬝ᵥ c) * (b ⬝ᵥ d) := by
  unfold frobInner
  simp only [vecMulVec_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The Frobenius square of a sum of two matrices. -/
theorem frobSq_add (X Y : Matrix n n ℝ) :
    frobSq (X + Y) = frobSq X + 2 * frobInner X Y + frobSq Y := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right,
    frobInner_comm Y X]
  ring

/-- The Frobenius square of a finite sum of matrices is the full double sum of
Frobenius inner products. -/
theorem frobSq_sum (s : Finset ι) (M : ι → Matrix n n ℝ) :
    frobSq (∑ i ∈ s, M i) = ∑ i ∈ s, ∑ j ∈ s, frobInner (M i) (M j) := by
  unfold frobSq
  rw [frobInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => frobInner_sum_right s (M i) M

/-! ### Pair blocks -/

/-- The pair block contributed by an off-critical zero with real coordinate
vectors `a`, `b` and multiplicity weight `m`:  `Q = 2m (a aᵀ - b bᵀ)`. -/
def pairBlock (m : ℝ) (a b : n → ℝ) : Matrix n n ℝ :=
  (2 * m) • (vecMulVec a a - vecMulVec b b)

/-- **Exact pair-pair Frobenius inner product.** -/
theorem pairPair_frobInner (m m' : ℝ) (a b c d : n → ℝ) :
    frobInner (pairBlock m a b) (pairBlock m' c d)
      = 4 * m * m' * ((a ⬝ᵥ c) ^ 2 - (a ⬝ᵥ d) ^ 2 - (b ⬝ᵥ c) ^ 2 + (b ⬝ᵥ d) ^ 2) := by
  unfold pairBlock
  rw [frobInner_smul_left, frobInner_smul_right, frobInner_sub_left,
    frobInner_sub_right, frobInner_sub_right, frobInner_vecMulVec,
    frobInner_vecMulVec, frobInner_vecMulVec, frobInner_vecMulVec]
  ring

/-- The Frobenius square of a single pair block. -/
theorem pairBlock_frobSq (m : ℝ) (a b : n → ℝ) :
    frobSq (pairBlock m a b)
      = 4 * m ^ 2 * ((a ⬝ᵥ a) ^ 2 + (b ⬝ᵥ b) ^ 2 - 2 * (a ⬝ᵥ b) ^ 2) := by
  unfold frobSq
  rw [pairPair_frobInner]
  have hba : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm b a
  rw [hba]
  ring

/-! ### Critical baseline and transverse surplus -/

/-- The **critical baseline** of a pair block: the Frobenius square the block
would have if its two real coordinate vectors were proportional, i.e. if the
zero sat on the critical line in this observable. -/
def criticalBaseline (m : ℝ) (a b : n → ℝ) : ℝ :=
  4 * m ^ 2 * ((a ⬝ᵥ a) - (b ⬝ᵥ b)) ^ 2

/-- The **transverse surplus** of a pair block: `8m²` times the Gram
determinant of the two real coordinate vectors. -/
def transverseSurplus (m : ℝ) (a b : n → ℝ) : ℝ :=
  8 * m ^ 2 * ((a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2)

/-- **Exact decomposition of a single pair block** into critical baseline plus
transverse surplus. -/
theorem pairBlock_frobSq_decomposition (m : ℝ) (a b : n → ℝ) :
    frobSq (pairBlock m a b) = criticalBaseline m a b + transverseSurplus m a b := by
  rw [pairBlock_frobSq]
  unfold criticalBaseline transverseSurplus
  ring

/-- Consistency check for the name *critical baseline*: when the two real
coordinate vectors are proportional — the on-line situation — the pair block's
Frobenius square is exactly the baseline, with zero surplus. -/
theorem pairBlock_frobSq_of_parallel (m : ℝ) (a : n → ℝ) (c : ℝ) :
    frobSq (pairBlock m a (c • a)) = criticalBaseline m a (c • a) ∧
      transverseSurplus m a (c • a) = 0 := by
  have hsurp : transverseSurplus m a (c • a) = 0 := by
    unfold transverseSurplus
    have h1 : (c • a) ⬝ᵥ (c • a) = c ^ 2 * (a ⬝ᵥ a) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    have h2 : a ⬝ᵥ (c • a) = c * (a ⬝ᵥ a) := by
      rw [dotProduct_smul, smul_eq_mul]
    rw [h1, h2]
    ring
  refine ⟨?_, hsurp⟩
  rw [pairBlock_frobSq_decomposition, hsurp, add_zero]

/-- The Gram determinant of two real vectors is nonnegative (Cauchy--Schwarz). -/
theorem gram_nonneg (a b : n → ℝ) : 0 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ a b
  simp only [dotProduct]
  have ha : ∑ i, a i * a i = ∑ i, a i ^ 2 := Finset.sum_congr rfl fun i _ => by ring
  have hb : ∑ i, b i * b i = ∑ i, b i ^ 2 := Finset.sum_congr rfl fun i _ => by ring
  rw [ha, hb]
  linarith

/-- The transverse surplus is nonnegative. -/
theorem transverseSurplus_nonneg (m : ℝ) (a b : n → ℝ) : 0 ≤ transverseSurplus m a b := by
  unfold transverseSurplus
  have := gram_nonneg a b
  positivity

/-- The transverse surplus is strictly positive exactly when the two real
coordinate vectors of the zero fail to be proportional — i.e. exactly when the
zero is genuinely off the critical line in this observable. -/
theorem transverseSurplus_pos_of_not_parallel {m : ℝ} (hm : m ≠ 0) (a b : n → ℝ)
    (hnp : ∀ c : ℝ, b ≠ c • a) (ha : a ≠ 0) : 0 < transverseSurplus m a b := by
  unfold transverseSurplus
  have hgram : 0 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := gram_nonneg a b
  rcases hgram.lt_or_eq with h | h
  · have hm2 : 0 < m ^ 2 := by positivity
    nlinarith
  · exfalso
    have hnn : 0 ≤ a ⬝ᵥ a := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hne : a ⬝ᵥ a ≠ 0 := fun h0 => ha (dotProduct_self_eq_zero.1 h0)
    have haa : 0 < a ⬝ᵥ a := lt_of_le_of_ne hnn (Ne.symm hne)
    set c := (a ⬝ᵥ b) / (a ⬝ᵥ a) with hc
    refine hnp c ?_
    have hexp : (b - c • a) ⬝ᵥ (b - c • a)
        = (b ⬝ᵥ b) - 2 * c * (a ⬝ᵥ b) + c ^ 2 * (a ⬝ᵥ a) := by
      simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm b a]
      ring
    have hzero : (b - c • a) ⬝ᵥ (b - c • a) = 0 := by
      rw [hexp, hc]
      field_simp
      nlinarith [h]
    have hsub := (dotProduct_self_eq_zero (v := b - c • a)).1 hzero
    exact sub_eq_zero.1 hsub

/-! ### The complex channels -/

/-- The complex evaluation vector `u = a + i b` of a zero. -/
def cvec (a b : n → ℝ) : n → ℂ := fun i => (a i : ℂ) + Complex.I * (b i : ℂ)

/-- The bilinear channel `S_{ρσ} = ∑ u_ρ(i) u_σ(i)`. -/
noncomputable def Sbil (u v : n → ℂ) : ℂ := ∑ i, u i * v i

/-- The sesquilinear channel `H_{ρσ} = ∑ u_ρ(i) conj(u_σ(i))`. -/
noncomputable def Hsesq (u v : n → ℂ) : ℂ := ∑ i, u i * (starRingEnd ℂ) (v i)

theorem Sbil_cvec_re (a b c d : n → ℝ) :
    (Sbil (cvec a b) (cvec c d)).re = (a ⬝ᵥ c) - (b ⬝ᵥ d) := by
  unfold Sbil cvec
  rw [Complex.re_sum]
  simp [dotProduct, Complex.add_re, Complex.mul_re, Finset.sum_sub_distrib]

theorem Sbil_cvec_im (a b c d : n → ℝ) :
    (Sbil (cvec a b) (cvec c d)).im = (a ⬝ᵥ d) + (b ⬝ᵥ c) := by
  unfold Sbil cvec
  rw [Complex.im_sum]
  simp [dotProduct, Complex.add_im, Complex.mul_im, Finset.sum_add_distrib]

theorem Hsesq_cvec_re (a b c d : n → ℝ) :
    (Hsesq (cvec a b) (cvec c d)).re = (a ⬝ᵥ c) + (b ⬝ᵥ d) := by
  unfold Hsesq cvec
  rw [Complex.re_sum]
  simp [dotProduct, Complex.add_re, Complex.mul_re, Finset.sum_add_distrib]

theorem Hsesq_cvec_im (a b c d : n → ℝ) :
    (Hsesq (cvec a b) (cvec c d)).im = (b ⬝ᵥ c) - (a ⬝ᵥ d) := by
  unfold Hsesq cvec
  rw [Complex.im_sum]
  simp [dotProduct, Complex.add_im, Complex.mul_im]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The pair-pair Frobenius inner product through the complex channels:**
`⟨Q_ρ, Q_σ⟩_F = 2 m_ρ m_σ Re (S² + H²)`. -/
theorem pairPair_frobInner_channels (m m' : ℝ) (a b c d : n → ℝ) :
    frobInner (pairBlock m a b) (pairBlock m' c d)
      = 2 * m * m' * ((Sbil (cvec a b) (cvec c d)) ^ 2
          + (Hsesq (cvec a b) (cvec c d)) ^ 2).re := by
  have hre : ((Sbil (cvec a b) (cvec c d)) ^ 2 + (Hsesq (cvec a b) (cvec c d)) ^ 2).re
      = ((Sbil (cvec a b) (cvec c d)).re ^ 2 - (Sbil (cvec a b) (cvec c d)).im ^ 2)
        + ((Hsesq (cvec a b) (cvec c d)).re ^ 2 - (Hsesq (cvec a b) (cvec c d)).im ^ 2) := by
    simp [pow_two, Complex.add_re, Complex.mul_re]
  rw [pairPair_frobInner, hre, Sbil_cvec_re, Sbil_cvec_im, Hsesq_cvec_re, Hsesq_cvec_im]
  ring

/-- **Mixed-channel Parseval identity:** the two imaginary channels carry
exactly twice the mixed interference weight
`N_{ρσ} = (a_ρ·d_σ)² + (b_ρ·c_σ)²`. -/
theorem mixedChannel_parseval (a b c d : n → ℝ) :
    (Sbil (cvec a b) (cvec c d)).im ^ 2 + (Hsesq (cvec a b) (cvec c d)).im ^ 2
      = 2 * ((a ⬝ᵥ d) ^ 2 + (b ⬝ᵥ c) ^ 2) := by
  rw [Sbil_cvec_im, Hsesq_cvec_im]
  ring

/-! ### The target split of the full finite matrix -/

/-- Splitting the Frobenius square of a finite sum of matrices around a
distinguished index. -/
theorem frobSq_sum_target_split [DecidableEq ι] (s : Finset ι) (M : ι → Matrix n n ℝ)
    {t : ι} (ht : t ∈ s) :
    frobSq (∑ i ∈ s, M i)
      = frobSq (M t) + 2 * ∑ j ∈ s.erase t, frobInner (M t) (M j)
        + frobSq (∑ j ∈ s.erase t, M j) := by
  classical
  have hsplit : ∑ i ∈ s, M i = M t + ∑ j ∈ s.erase t, M j :=
    (Finset.add_sum_erase s M ht).symm
  rw [hsplit, frobSq_add, frobInner_sum_right]

/-- **M1: exact target decomposition of the finite zero-side Frobenius square.**

For a finite family of pair blocks `Q ρ = 2 m_ρ (a_ρ a_ρᵀ - b_ρ b_ρᵀ)` and a
distinguished target zero `ρ₀`, the Frobenius square of the assembled matrix
splits *exactly* into the critical baseline of the target, the transverse
surplus of the target, and the interference of the target with everything
else. -/
theorem A_frobSq_target_decomposition [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) {t : ι} (ht : t ∈ s) :
    frobSq (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ))
      = criticalBaseline (m t) (a t) (b t) + transverseSurplus (m t) (a t) (b t)
        + (2 * ∑ j ∈ s.erase t, frobInner (pairBlock (m t) (a t) (b t))
              (pairBlock (m j) (a j) (b j))
            + frobSq (∑ j ∈ s.erase t, pairBlock (m j) (a j) (b j))) := by
  rw [frobSq_sum_target_split s (fun ρ => pairBlock (m ρ) (a ρ) (b ρ)) ht,
    pairBlock_frobSq_decomposition]
  ring

/-- **Retained-defect inequality.**  The transverse surplus of the target zero
is exactly the Frobenius square of the assembled matrix minus the critical
baseline and the interference; in particular, if the assembled Frobenius square
is bounded above by `C` and the interference is bounded below by `-E`, then the
surplus obeys `D ≤ C - baseline + E`. -/
theorem transverseSurplus_le_of_interference [DecidableEq ι] (s : Finset ι) (m : ι → ℝ)
    (a b : ι → n → ℝ) {t : ι} (ht : t ∈ s) {C E : ℝ}
    (hC : frobSq (∑ ρ ∈ s, pairBlock (m ρ) (a ρ) (b ρ)) ≤ C)
    (hE : -E ≤ 2 * ∑ j ∈ s.erase t, frobInner (pairBlock (m t) (a t) (b t))
              (pairBlock (m j) (a j) (b j))
            + frobSq (∑ j ∈ s.erase t, pairBlock (m j) (a j) (b j))) :
    transverseSurplus (m t) (a t) (b t) ≤ C - criticalBaseline (m t) (a t) (b t) + E := by
  have h := A_frobSq_target_decomposition s m a b ht
  linarith [hC, hE, h.symm.le, h.le]

end RiemannAnalytic
