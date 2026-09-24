import Mathlib
import RequestProject.Hecke23

/-!
# Five Hecke words: `T2`, `T3`, `T2 T3`, `T2 T3 T2`, `T3 T3 T3`

This file follows a single thread: start from an eigenform `f` of weight `k` with eigenvalue
system `a` and apply the two smallest Hecke operators in the five patterns

```
  T2 ,  T3 ,  T2 T3 ,  T2 T3 T2 ,  T3 T3 T3 .
```

Each of the resulting five modular forms is again a multiple of `f`, and the multiplier is the
product of the eigenvalues of the letters (`wordEigenvalue`). The content of the file is the
translation of each of those five products back into the *basis* `T 1, T 2, T 3, …` of the Hecke
algebra, i.e. the answer to "which single Hecke operators does this word cost?":

* `T2` and `T3` are already basis elements;
* `T2 T3 = T 6` — coprime letters just multiply;
* `T2 T3 T2 = T 12 + 2 ^ (k-1) * T 3` — the repeated letter produces an echo;
* `T3 T3 T3 = T 27 + 2 * 3 ^ (k-1) * T 3` — the same letter three times produces two echoes.

Both sides are proved twice, and independently.

1. `Hecke23.HeckeSystem` level (`eigen_*` theorems): as identities between the eigenvalue
   products and the eigenvalues `a 6`, `a 12`, `a 27`, valid in every Hecke system.
2. Hecke-algebra level (`hmul_*` theorems): in the formal algebra `ℕ →₀ R` with the classical
   structure constants `T m * T n = ∑_{d ∣ gcd m n} d ^ (k-1) * T (m n / d ^ 2)`, where the same
   three identities are computations with divisor sets.

Finally `eigen_polynomial_*` records each of the five multipliers as an explicit polynomial in
just `a 2` and `a 3` — the "3, 6, 9" moral of the project, in its Hecke incarnation.
-/

namespace HeckeWords

open Hecke23

variable {R : Type*} [CommRing R] {k : ℕ} {a : ℕ → R}

/-! ## 1. The eigenvalue side -/

/-- The multiplier by which the word `w` (read left to right, each letter a prime) scales an
eigenform with eigenvalue system `a`: the product of the eigenvalues of the letters. -/
def wordEigenvalue (a : ℕ → R) (w : List ℕ) : R := (w.map a).prod

@[simp] theorem wordEigenvalue_nil : wordEigenvalue a [] = 1 := rfl

@[simp] theorem wordEigenvalue_cons (p : ℕ) (w : List ℕ) :
    wordEigenvalue a (p :: w) = a p * wordEigenvalue a w := rfl

/-- `12 = 2 ^ 2 * 3`. -/
theorem a_twelve (ha : HeckeSystem k a) :
    a 12 = a 2 ^ 2 * a 3 - (2 : R) ^ (k - 1) * a 3 := by
  have h : (12 : ℕ) = 4 * 3 := by norm_num
  rw [h, ha.mul_coprime 4 3 (by decide), a_four ha]
  ring

/-- `27 = 3 ^ 3`. -/
theorem a_twentyseven (ha : HeckeSystem k a) :
    a 27 = a 3 ^ 3 - 2 * (3 : R) ^ (k - 1) * a 3 := by
  have h := ha.prime_pow 3 Nat.prime_three 1
  norm_num at h
  rw [h, a_nine ha]
  ring

/-- Word 1: `T2` acts by `a 2`. -/
theorem eigen_word_two : wordEigenvalue a [2] = a 2 := by simp

/-- Word 2: `T3` acts by `a 3`. -/
theorem eigen_word_three : wordEigenvalue a [3] = a 3 := by simp

/-- Word 3: `T2 T3` acts by `a 6` — the letters are coprime, so nothing is lost. -/
theorem eigen_word_two_three (ha : HeckeSystem k a) :
    wordEigenvalue a [2, 3] = a 6 := by
  simp [a_six ha]

/-- Word 4: `T2 T3 T2 = T 12 + 2 ^ (k-1) T 3`. -/
theorem eigen_word_two_three_two (ha : HeckeSystem k a) :
    wordEigenvalue a [2, 3, 2] = a 12 + (2 : R) ^ (k - 1) * a 3 := by
  simp [a_twelve ha]
  ring

/-- Word 5: `T3 T3 T3 = T 27 + 2 · 3 ^ (k-1) T 3`. -/
theorem eigen_word_three_three_three (ha : HeckeSystem k a) :
    wordEigenvalue a [3, 3, 3] = a 27 + 2 * (3 : R) ^ (k - 1) * a 3 := by
  simp [a_twentyseven ha]
  ring

/-! ## 2. The Hecke algebra side -/

/-- The formal Hecke operator `T n`, as a basis vector of the Hecke algebra `ℕ →₀ R`. -/
noncomputable def T (n : ℕ) : ℕ →₀ R := Finsupp.single n 1

/-- The structure constants: `T m * T n = ∑_{d ∣ gcd m n} d ^ (k-1) T (m n / d ^ 2)`. -/
noncomputable def basisMul (k m n : ℕ) : ℕ →₀ R :=
  ∑ d ∈ (Nat.gcd m n).divisors, ((d : R) ^ (k - 1)) • T (m * n / d ^ 2)

/-- Multiplication in the weight-`k` Hecke algebra, the bilinear extension of `basisMul`. -/
noncomputable def hmul (k : ℕ) (f g : ℕ →₀ R) : ℕ →₀ R :=
  f.sum fun m c => g.sum fun n c' => (c * c') • basisMul k m n

/-- On basis vectors, `hmul` is given by the structure constants. -/
theorem hmul_T_T (k m n : ℕ) :
    hmul k (T m) (T n) = basisMul (R := R) k m n := by
  simp [hmul, T, Finsupp.sum_single_index]

/-- A scaled basis vector on the left. -/
theorem hmul_single_T (k m n : ℕ) (c : R) :
    hmul k (Finsupp.single m c) (T n) = c • basisMul (R := R) k m n := by
  simp [hmul, T, Finsupp.sum_single_index]

theorem hmul_add_left (k : ℕ) (f g h : ℕ →₀ R) :
    hmul k (f + g) h = hmul k f h + hmul k g h := by
  simp [hmul, Finsupp.sum_add_index', add_mul, add_smul, Finsupp.sum_add]

theorem smul_T (c : R) (n : ℕ) : c • (T n : ℕ →₀ R) = Finsupp.single n c := by
  simp [T, Finsupp.smul_single]

/-- **Word 3, in the algebra**: `T2 * T3 = T 6`. Coprime letters cost nothing. -/
theorem hmul_two_three : hmul (R := R) k (T 2) (T 3) = T 6 := by
  rw [hmul_T_T, basisMul]
  norm_num

/-- **Word 4, in the algebra**: `(T2 T3) T2 = T 12 + 2 ^ (k-1) T 3`. -/
theorem hmul_two_three_two :
    hmul k (hmul (R := R) k (T 2) (T 3)) (T 2) = T 12 + ((2 : R) ^ (k - 1)) • T 3 := by
  rw [hmul_two_three, hmul_T_T, basisMul,
    show (Nat.gcd 6 2).divisors = {1, 2} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- `T3 * T3 = T 9 + 3 ^ (k-1) T 1`: the first echo. -/
theorem hmul_three_three :
    hmul (R := R) k (T 3) (T 3) = T 9 + ((3 : R) ^ (k - 1)) • T 1 := by
  rw [hmul_T_T, basisMul, show (Nat.gcd 3 3).divisors = {1, 3} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- **Word 5, in the algebra**: `(T3 T3) T3 = T 27 + 2 · 3 ^ (k-1) T 3`. -/
theorem hmul_three_three_three :
    hmul k (hmul (R := R) k (T 3) (T 3)) (T 3)
      = T 27 + (2 * (3 : R) ^ (k - 1)) • T 3 := by
  rw [hmul_three_three, hmul_add_left, smul_T, hmul_single_T, hmul_T_T, basisMul, basisMul,
    show (Nat.gcd 9 3).divisors = {1, 3} from by decide,
    show (Nat.gcd 1 3).divisors = {1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_singleton]
  norm_num
  module

/-! ## 3. The two sides agree

An eigenvalue system `a` turns a Hecke algebra element into a scalar; the two descriptions of
each word — the product of eigenvalues, and the expansion into basis operators — are then the
same number. -/

/-- Evaluate a Hecke algebra element at the eigenvalue system `a`: `T n ↦ a n`, extended
linearly. For an eigenform `f` with system `a`, this is the scalar by which the operator acts. -/
noncomputable def evalT (a : ℕ → R) (f : ℕ →₀ R) : R := f.sum fun n c => c * a n

@[simp] theorem evalT_T (a : ℕ → R) (n : ℕ) : evalT a (T n) = a n := by
  simp [evalT, T, Finsupp.sum_single_index]

theorem evalT_add (a : ℕ → R) (f g : ℕ →₀ R) :
    evalT a (f + g) = evalT a f + evalT a g := by
  simp [evalT, Finsupp.sum_add_index', add_mul]

@[simp] theorem evalT_smul_T (a : ℕ → R) (c : R) (n : ℕ) :
    evalT a (c • (T n : ℕ →₀ R)) = c * a n := by
  simp [evalT, T, Finsupp.smul_single, Finsupp.sum_single_index]

/-- Word 3: the two computations agree. -/
theorem evalT_word_two_three (ha : HeckeSystem k a) :
    evalT a (hmul k (T 2) (T 3)) = wordEigenvalue a [2, 3] := by
  rw [hmul_two_three, evalT_T, eigen_word_two_three ha]

/-- Word 4: the two computations agree. -/
theorem evalT_word_two_three_two (ha : HeckeSystem k a) :
    evalT a (hmul k (hmul k (T 2) (T 3)) (T 2)) = wordEigenvalue a [2, 3, 2] := by
  rw [hmul_two_three_two, evalT_add, evalT_T, evalT_smul_T, eigen_word_two_three_two ha]

/-- Word 5: the two computations agree. -/
theorem evalT_word_three_three_three (ha : HeckeSystem k a) :
    evalT a (hmul k (hmul k (T 3) (T 3)) (T 3)) = wordEigenvalue a [3, 3, 3] := by
  rw [hmul_three_three_three, evalT_add, evalT_T, evalT_smul_T,
    eigen_word_three_three_three ha]

/-! ## 4. The five multipliers as polynomials in `a 2` and `a 3` -/

theorem eigen_polynomial_two : wordEigenvalue a [2] = a 2 := by simp

theorem eigen_polynomial_three : wordEigenvalue a [3] = a 3 := by simp

theorem eigen_polynomial_two_three : wordEigenvalue a [2, 3] = a 2 * a 3 := by simp

theorem eigen_polynomial_two_three_two :
    wordEigenvalue a [2, 3, 2] = a 2 ^ 2 * a 3 := by
  simp; ring

theorem eigen_polynomial_three_three_three :
    wordEigenvalue a [3, 3, 3] = a 3 ^ 3 := by
  simp; ring

/-! ## 5. A concrete anchor: the discriminant form

For `Δ` of weight `12` the eigenvalues are Ramanujan's `τ`, with `τ 2 = -24` and `τ 3 = 252`.
The five words then take the values below — every number in them is forced by the two inputs. -/

theorem delta_values {a : ℕ → ℤ} (ha : HeckeSystem 12 a) (h2 : a 2 = -24) (h3 : a 3 = 252) :
    a 6 = -6048 ∧ a 12 = -370944 ∧ a 27 = -73279080 ∧
      wordEigenvalue a [2, 3] = -6048 ∧
      wordEigenvalue a [2, 3, 2] = 145152 ∧
      wordEigenvalue a [3, 3, 3] = 16003008 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_six ha, h2, h3]; norm_num
  · rw [a_twelve ha, h2, h3]; norm_num
  · rw [a_twentyseven ha, h3]; norm_num
  · rw [eigen_polynomial_two_three, h2, h3]; norm_num
  · rw [eigen_polynomial_two_three_two, h2, h3]; norm_num
  · rw [eigen_polynomial_three_three_three, h3]; norm_num

end HeckeWords
