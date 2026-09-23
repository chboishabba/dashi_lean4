/-
# Entrywise differentiation of matrix-valued families

The fixed-constraint-coordinate Gaussian of the Bałaban block-spin step is the
restricted operator `Â(U) = C(U)ᵀ A(U) C(U)`, and the Row A1a Gaussian datum is
its *first background variation*.  To differentiate a product of
background-dependent matrices without choosing a matrix norm, this file works
entrywise: a family `A : ℝ → Matrix m n ℝ` has derivative `A'` at `t` when every
entry does.

Everything here is elementary calculus, but it is the infrastructure the
constrained-Gaussian first variation is built from:

* `HasMatDerivAt.mul` — the noncommutative product rule `(AB)' = A'B + AB'`,
  with the factor order preserved;
* `HasMatDerivAt.transpose`, `.add`, `.neg`, `.smul`, `.const`;
* `HasMatDerivAt.mul₃` — the three-factor rule, which is exactly the shape of
  `D(CᵀAC)`;
* `HasMatDerivAt.of_eq_zero` — the derivative of an identically vanishing family
  vanishes, the form in which the constraint identity `Q(U)C(U) = 0` is
  differentiated.
-/
import Mathlib

namespace YangMills

open Matrix

variable {l m n p : Type*}

/-- A matrix-valued family of one real parameter has entrywise derivative `A'`
at `t`. -/
def HasMatDerivAt (A : ℝ → Matrix m n ℝ) (A' : Matrix m n ℝ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t

namespace HasMatDerivAt

theorem const (A : Matrix m n ℝ) (t : ℝ) : HasMatDerivAt (fun _ => A) 0 t :=
  fun i j => by simpa using (hasDerivAt_const t (A i j))

theorem add {A B : ℝ → Matrix m n ℝ} {A' B' : Matrix m n ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) (hB : HasMatDerivAt B B' t) :
    HasMatDerivAt (fun s => A s + B s) (A' + B') t :=
  fun i j => by simpa using (hA i j).add (hB i j)

theorem neg {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) : HasMatDerivAt (fun s => -A s) (-A') t :=
  fun i j => by simpa using (hA i j).neg

theorem smul {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {c : ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) : HasMatDerivAt (fun s => c • A s) (c • A') t :=
  fun i j => by simpa using (hA i j).const_mul c

theorem transpose {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) : HasMatDerivAt (fun s => (A s)ᵀ) A'ᵀ t :=
  fun i j => hA j i

/-- **The noncommutative product rule**, entrywise: `(AB)' = A'B + AB'`, with
the order of the factors preserved. -/
theorem mul [Fintype n] {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ}
    {A' : Matrix m n ℝ} {B' : Matrix n p ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) (hB : HasMatDerivAt B B' t) :
    HasMatDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  intro i j
  have hentry : (fun s => (A s * B s) i j) = fun s => ∑ k : n, A s i k * B s k j := by
    funext s; rw [Matrix.mul_apply]
  rw [hentry]
  have hsum0 : HasDerivAt (∑ k : n, fun s => A s i k * B s k j)
      (∑ k : n, (A' i k * B t k j + A t i k * B' k j)) t :=
    HasDerivAt.sum (fun k _ => (hA i k).mul (hB k j))
  have hfun : (∑ k : n, fun s => A s i k * B s k j)
      = fun s => ∑ k : n, A s i k * B s k j := by
    funext s; simp [Finset.sum_apply]
  rw [hfun] at hsum0
  have hval : (∑ k : n, (A' i k * B t k j + A t i k * B' k j))
      = (A' * B t + A t * B') i j := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  rwa [hval] at hsum0

/-- Multiplication by a constant matrix on the right. -/
theorem mul_const [Fintype n] {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) (N : Matrix n p ℝ) :
    HasMatDerivAt (fun s => A s * N) (A' * N) t := by
  have h := hA.mul (HasMatDerivAt.const N t)
  simpa using h

/-- Multiplication by a constant matrix on the left. -/
theorem const_mul [Fintype n] {B : ℝ → Matrix n p ℝ} {B' : Matrix n p ℝ} {t : ℝ}
    (M : Matrix m n ℝ) (hB : HasMatDerivAt B B' t) :
    HasMatDerivAt (fun s => M * B s) (M * B') t := by
  have h := (HasMatDerivAt.const M t).mul hB
  simpa using h

/-- The three-factor rule — the shape of `D(CᵀAC)`. -/
theorem mul₃ [Fintype m] [Fintype n] {A : ℝ → Matrix l m ℝ} {B : ℝ → Matrix m n ℝ}
    {C : ℝ → Matrix n p ℝ}
    {A' : Matrix l m ℝ} {B' : Matrix m n ℝ} {C' : Matrix n p ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) (hB : HasMatDerivAt B B' t) (hC : HasMatDerivAt C C' t) :
    HasMatDerivAt (fun s => A s * B s * C s)
      (A' * B t * C t + A t * B' * C t + A t * B t * C') t := by
  have h := (hA.mul hB).mul hC
  have hval : (A' * B t + A t * B') * C t + A t * B t * C'
      = A' * B t * C t + A t * B' * C t + A t * B t * C' := by
    rw [Matrix.add_mul]
  rwa [hval] at h

/-- Entrywise derivatives are unique. -/
theorem unique {A : ℝ → Matrix m n ℝ} {A' A'' : Matrix m n ℝ} {t : ℝ}
    (h1 : HasMatDerivAt A A' t) (h2 : HasMatDerivAt A A'' t) : A' = A'' := by
  ext i j
  exact (h1 i j).unique (h2 i j)

/-- The derivative of an identically vanishing family vanishes.  This is the
form in which the constraint identity is differentiated. -/
theorem of_eq_zero {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t : ℝ}
    (hA : HasMatDerivAt A A' t) (h0 : ∀ s, A s = 0) : A' = 0 := by
  refine hA.unique ?_
  intro i j
  have hij : (fun s => A s i j) = fun _ => (0 : ℝ) := by
    funext s; rw [h0 s]; simp
  rw [hij]
  simpa using hasDerivAt_const t (0 : ℝ)

end HasMatDerivAt

end YangMills
