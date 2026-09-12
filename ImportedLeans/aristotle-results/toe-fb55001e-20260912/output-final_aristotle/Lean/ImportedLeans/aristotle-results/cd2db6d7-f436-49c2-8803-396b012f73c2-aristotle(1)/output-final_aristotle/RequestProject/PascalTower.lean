import Mathlib

/-!
# Stage 1 of the tower: Pascal's triangle, built from row `0` upwards

This file starts the construction asked for in the third thread of the project — *a Pascal
triangle, a tree, and a `GF` extension tower, built from the beginning, smallest to largest* — at
the smallest possible object: row `0` of Pascal's triangle, the one-element list `[1]`.

Everything here is produced by an explicit recursion that only ever looks at the previous row, so
the triangle really is built smallest-to-largest:

* `PascalTower.row` — `row 0 = [1]`, and `row (n+1)` is `row n` added to its own shift.
* `PascalTower.row_eq_map_choose`, `row_length`, `row_sum`, `row_reverse` — the row is the list of
  binomial coefficients, it has `n+1` entries, it sums to `2 ^ n`, and it is a palindrome.
* `PascalTower.triangle`, `triangle_succ` — the first `n+1` rows, smallest first, each triangle
  extending the previous one.

The same recursion carries a parameter `q`, giving the *`q`-Pascal triangle* of Gaussian binomial
coefficients:

* `PascalTower.gauss` — `[n+1 choose k+1]_q = [n choose k]_q + q^(k+1) · [n choose k+1]_q`.
* `PascalTower.gauss_one` — at `q = 1` the `q`-triangle collapses onto the ordinary one.
* `PascalTower.gauss_self`, `gauss_eq_zero_of_lt`, `gauss_succ_one` — the boundary of the triangle,
  and its second column `1 + q + ⋯ + q^(n-1)`.
* `PascalTower.gauss_mul_qFact` — the division-free form of the closed formula
  `[n choose k]_q = [n]_q! / ([k]_q! [n-k]_q!)`, and `PascalTower.gauss_symm`, the palindromic
  symmetry it implies.

The point of the `q`-analogue is that it is the triangle *of the field tower*: over `GF(q)` the
entry `[n choose k]_q` counts the `k`-dimensional subspaces of `GF(q)ⁿ`.  The `k = 1` case of that
statement is proved in `RequestProject/ExtensionTowerTree.lean`
(`ExtensionTower.card_projectivization_eq_gauss`), where the fields of the tower are available.
-/

namespace PascalTower

open Finset

/-! ## The ordinary triangle -/

/-- Row `n` of Pascal's triangle, built from row `n - 1` by adding the row to its own shift.
`row 0 = [1]`, `row 1 = [1, 1]`, `row 2 = [1, 2, 1]`, … -/
def row : Nat → List Nat
  | 0 => [1]
  | n + 1 => List.zipWith (· + ·) (0 :: row n) (row n ++ [0])

@[simp] theorem row_zero : row 0 = [1] := rfl

theorem row_succ (n : Nat) :
    row (n + 1) = List.zipWith (· + ·) (0 :: row n) (row n ++ [0]) := rfl

/-- Row `n` has `n + 1` entries. -/
@[simp] theorem row_length (n : Nat) : (row n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [row_succ, ih]

/-- The entries of row `n` are the binomial coefficients `C(n, k)`. -/
theorem row_eq_map_choose (n : Nat) : row n = (List.range (n + 1)).map (n.choose ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [row_succ, ih]
    apply List.ext_getElem
    · simp
    · intro k h₁ h₂
      have hk : k < n + 2 := by simp only [List.length_map, List.length_range] at h₂; omega
      simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_cons]
      by_cases h0 : k = 0
      · subst h0; simp
      · rw [dif_neg h0]
        by_cases hkn : k < n + 1
        · rw [List.getElem_append_left (by simpa using hkn)]
          simp only [List.getElem_map, List.getElem_range]
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          simp [Nat.choose_succ_succ' n j]
        · have hk' : k = n + 1 := by omega
          subst hk'
          rw [List.getElem_append_right (by simp)]
          simp

theorem row_getElem (n k : Nat) (h : k < n + 1) :
    (row n)[k]'(by simpa using h) = n.choose k := by
  simp [row_eq_map_choose]

/-- Row `n` sums to `2 ^ n`. -/
@[simp] theorem row_sum (n : Nat) : (row n).sum = 2 ^ n := by
  rw [row_eq_map_choose]
  have h : ((List.range (n + 1)).map (n.choose ·)).sum
      = ∑ k ∈ Finset.range (n + 1), n.choose k := rfl
  rw [h, Nat.sum_range_choose]

/-- Row `n` is a palindrome. -/
theorem row_reverse (n : Nat) : (row n).reverse = row n := by
  apply List.ext_getElem
  · simp
  · intro k h₁ h₂
    have hk : k < n + 1 := by simpa using h₂
    rw [List.getElem_reverse]
    simp only [row_length]
    rw [row_getElem _ _ (by omega), row_getElem _ _ hk, show n + 1 - 1 - k = n - k by omega,
      Nat.choose_symm (by omega)]

/-- The first `n + 1` rows of Pascal's triangle, smallest row first. -/
def triangle (n : Nat) : List (List Nat) := (List.range (n + 1)).map row

@[simp] theorem triangle_length (n : Nat) : (triangle n).length = n + 1 := by
  simp [triangle]

theorem triangle_getElem (n k : Nat) (h : k < n + 1) :
    (triangle n)[k]'(by simpa [triangle] using h) = row k := by
  simp [triangle]

/-- Each triangle extends the previous one: the construction really does go smallest to
largest. -/
theorem triangle_succ (n : Nat) : triangle (n + 1) = triangle n ++ [row (n + 1)] := by
  simp [triangle, List.range_succ]

/-! ## The `q`-analogue: the Gaussian triangle of the field tower -/

/-- The Gaussian binomial coefficient `[n choose k]_q`, defined by the `q`-Pascal recursion
`[n+1 choose k+1]_q = [n choose k]_q + q^(k+1) · [n choose k+1]_q`, again building each row from
the previous one. -/
def gauss (q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gauss q n k + q ^ (k + 1) * gauss q n (k + 1)

@[simp] theorem gauss_zero_right (q n : Nat) : gauss q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem gauss_zero_succ (q k : Nat) : gauss q 0 (k + 1) = 0 := rfl

theorem gauss_succ_succ (q n k : Nat) :
    gauss q (n + 1) (k + 1) = gauss q n k + q ^ (k + 1) * gauss q n (k + 1) := rfl

/-- At `q = 1` the Gaussian triangle is Pascal's triangle. -/
theorem gauss_one (n k : Nat) : gauss 1 n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gauss_succ_succ, ih, Nat.choose_succ_succ]

/-- Above the diagonal the Gaussian triangle vanishes. -/
theorem gauss_eq_zero_of_lt {q n k : Nat} (h : n < k) : gauss q n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [gauss_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- The diagonal of the Gaussian triangle is `1`. -/
@[simp] theorem gauss_self (q n : Nat) : gauss q n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [gauss_succ_succ, ih, gauss_eq_zero_of_lt (Nat.lt_succ_self n)]; simp

/-- The second column of the Gaussian triangle is `1 + q + ⋯ + q^(n-1)`: over `GF(q)` this is the
number of lines through the origin in `GF(q)ⁿ`. -/
theorem gauss_succ_one (q n : Nat) : gauss q n 1 = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp
  | succ n ih => rw [gauss_succ_succ, gauss_zero_right, ih, geom_sum_succ]; ring

/-- `(1 + q + ⋯ + q^(n-1))·(q-1) + 1 = qⁿ`: the geometric sum identity, division-free, in `ℕ`. -/
theorem geom_sum_mul_pred (q n : Nat) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range n, q ^ i) * (q - 1) + 1 = q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geom_sum_succ']
    obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have h1 : (q + 1) ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [add_mul, pow_succ]
    nlinarith [ih]

/-- The projective count from the second column of the Gaussian triangle:
`[n choose 1]_q · (q - 1) + 1 = qⁿ`. -/
theorem gauss_one_mul_pred (q n : Nat) (hq : 1 ≤ q) :
    gauss q n 1 * (q - 1) + 1 = q ^ n := by
  rw [gauss_succ_one]
  exact geom_sum_mul_pred q n hq

/-! ### `q`-integers and `q`-factorials -/

/-- The `q`-integer `[n]_q = 1 + q + ⋯ + q^(n-1)`. -/
def qInt (q n : Nat) : Nat := ∑ i ∈ Finset.range n, q ^ i

/-- The `q`-factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q`. -/
def qFact (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => qFact q n * qInt q (n + 1)

@[simp] theorem qFact_zero (q : Nat) : qFact q 0 = 1 := rfl

theorem qFact_succ (q n : Nat) : qFact q (n + 1) = qFact q n * qInt q (n + 1) := rfl

theorem qInt_pos (q n : Nat) (hn : 0 < n) : 0 < qInt q n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold qInt
  rw [Finset.sum_range_succ']
  simp

theorem qFact_pos (q n : Nat) : 0 < qFact q n := by
  induction n with
  | zero => simp
  | succ n ih => exact Nat.mul_pos ih (qInt_pos q (n + 1) (by omega))

/-- `[k+1]_q + q^(k+1) [n-k]_q = [n+1]_q`: the `q`-integer identity behind the `q`-Pascal rule. -/
theorem qInt_succ_add (q n k : Nat) (h : k ≤ n) :
    qInt q (k + 1) + q ^ (k + 1) * qInt q (n - k) = qInt q (n + 1) := by
  unfold qInt
  conv_rhs => rw [show n + 1 = (k + 1) + (n - k) by omega, Finset.sum_range_add]
  rw [Finset.mul_sum]
  have h2 : ∀ i, q ^ (k + 1) * q ^ i = q ^ (k + 1 + i) := fun i => by rw [← pow_add]
  simp only [h2]

/-- The closed formula `[n choose k]_q = [n]_q! / ([k]_q! [n-k]_q!)`, stated without division. -/
theorem gauss_mul_qFact (q : Nat) : ∀ n k : Nat, k ≤ n →
    gauss q n k * (qFact q k * qFact q (n - k)) = qFact q n := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    simp
  | succ n ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have h1 := ih k (by omega)
        have h2 := ih (k + 1) (by omega)
        rw [gauss_succ_succ]
        have e1 : qFact q (k + 1) = qFact q k * qInt q (k + 1) := rfl
        have e2 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
        have e3 : qFact q (n - k) = qFact q (n - (k + 1)) * qInt q (n - k) := by
          rw [show n - k = (n - (k + 1)) + 1 by omega]
          rfl
        rw [e2]
        have e4 : qFact q ((n - (k + 1)) + 1)
            = qFact q (n - (k + 1)) * qInt q (n - (k + 1) + 1) := rfl
        rw [e4, e1, show n - (k + 1) + 1 = n - k by omega]
        have expand : (gauss q n k + q ^ (k + 1) * gauss q n (k + 1)) *
            (qFact q k * qInt q (k + 1) * (qFact q (n - (k + 1)) * qInt q (n - k)))
            = qInt q (k + 1) * (gauss q n k * (qFact q k * qFact q (n - k)))
              + q ^ (k + 1) * qInt q (n - k) *
                (gauss q n (k + 1) * (qFact q (k + 1) * qFact q (n - (k + 1)))) := by
          rw [e1, e3]; ring
        rw [expand, h1, h2]
        calc qInt q (k + 1) * qFact q n + q ^ (k + 1) * qInt q (n - k) * qFact q n
            = (qInt q (k + 1) + q ^ (k + 1) * qInt q (n - k)) * qFact q n := by ring
          _ = qInt q (n + 1) * qFact q n := by rw [qInt_succ_add q n k (by omega)]
          _ = qFact q (n + 1) := by rw [qFact_succ]; ring
      · have hkn' : k = n := by omega
        subst hkn'
        simp

/-- The symmetry `[n choose k]_q = [n choose n-k]_q` of the Gaussian triangle. -/
theorem gauss_symm {q n k : Nat} (h : k ≤ n) : gauss q n k = gauss q n (n - k) := by
  have h1 := gauss_mul_qFact q n k h
  have h2 := gauss_mul_qFact q n (n - k) (by omega)
  rw [show n - (n - k) = k by omega] at h2
  have hpos : 0 < qFact q k * qFact q (n - k) :=
    Nat.mul_pos (qFact_pos q k) (qFact_pos q (n - k))
  have : gauss q n k * (qFact q k * qFact q (n - k))
      = gauss q n (n - k) * (qFact q k * qFact q (n - k)) := by
    rw [h1]
    rw [show qFact q k * qFact q (n - k) = qFact q (n - k) * qFact q k by ring, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- Row `n` of the Gaussian triangle. -/
def gaussRow (q n : Nat) : List Nat := (List.range (n + 1)).map (gauss q n)

@[simp] theorem gaussRow_length (q n : Nat) : (gaussRow q n).length = n + 1 := by
  simp [gaussRow]

/-- At `q = 1` the Gaussian rows are the Pascal rows. -/
theorem gaussRow_one (n : Nat) : gaussRow 1 n = row n := by
  simp [gaussRow, row_eq_map_choose, gauss_one]

/-- The Gaussian triangle, smallest row first. -/
def gaussTriangle (q n : Nat) : List (List Nat) := (List.range (n + 1)).map (gaussRow q)

@[simp] theorem gaussTriangle_length (q n : Nat) : (gaussTriangle q n).length = n + 1 := by
  simp [gaussTriangle]

theorem gaussTriangle_succ (q n : Nat) :
    gaussTriangle q (n + 1) = gaussTriangle q n ++ [gaussRow q (n + 1)] := by
  simp [gaussTriangle, List.range_succ]

/-- The first four rows of the ordinary triangle. -/
example : triangle 3 = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1]] := by decide

/-- The first four rows of the Gaussian triangle at `q = 2`, the triangle of subspace counts of
`GF(2)ⁿ`. -/
example : gaussTriangle 2 3 = [[1], [1, 1], [1, 3, 1], [1, 7, 7, 1]] := by decide

end PascalTower
