import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Collatz/Syracuse inverse-of-three producer

Mathlib-backed arithmetic producer for the dashi_agda same-object
Collatz/Syracuse parity-cylinder lane.

This file proves only finite modular arithmetic.  It does not identify the
finite transfer chain with the integer Syracuse process and it makes no
Collatz-conjecture claim.
-/

namespace AgdaMirror.CollatzSyracuseInv3Exact

lemma coprime_three_two_pow (m : ℕ) : Nat.Coprime 3 (2 ^ m) := by
  have h : Nat.Coprime 3 2 := by decide
  exact h.pow_right m

/-- The canonical inverse of 3 in `ZMod (2^m)`. -/
def inv3 (m : ℕ) : ZMod (2 ^ m) :=
  (ZMod.unitOfCoprime 3 (coprime_three_two_pow m)).inv

/-- Source theorem used by the Agda parity-cylinder reverse step. -/
theorem three_mul_inv3 (m : ℕ) :
    (3 : ZMod (2 ^ m)) * inv3 m = 1 := by
  have h := (ZMod.unitOfCoprime 3 (coprime_three_two_pow m)).mul_inv
  simpa [inv3] using h

theorem inv3_mul_three (m : ℕ) :
    inv3 m * (3 : ZMod (2 ^ m)) = 1 := by
  rw [mul_comm, three_mul_inv3]

/-- Reverse one even Syracuse parity step on the finite cylinder. -/
def evenBack (m : ℕ) (y : ZMod (2 ^ m)) : ZMod (2 ^ m) := 2 * y

/-- Reverse one odd Syracuse parity step on the finite cylinder. -/
def oddBack (m : ℕ) (y : ZMod (2 ^ m)) : ZMod (2 ^ m) :=
  inv3 m * (2 * y - 1)

theorem evenBack_spec (m : ℕ) (y : ZMod (2 ^ m)) :
    evenBack m y = 2 * y := rfl

/-- The odd reverse branch solves `3x+1 = 2y` exactly in `ZMod (2^m)`. -/
theorem oddBack_spec (m : ℕ) (y : ZMod (2 ^ m)) :
    3 * oddBack m y + 1 = 2 * y := by
  rw [oddBack]
  calc
    3 * (inv3 m * (2 * y - 1)) + 1
        = (3 * inv3 m) * (2 * y - 1) + 1 := by ring
    _ = 1 * (2 * y - 1) + 1 := by rw [three_mul_inv3]
    _ = 2 * y := by ring

/-- Multiplication by three is cancellable on every `2^m` cylinder. -/
theorem three_mul_injective (m : ℕ) :
    Function.Injective (fun x : ZMod (2 ^ m) => 3 * x) := by
  intro x y h
  calc
    x = inv3 m * (3 * x) := by rw [← mul_assoc, inv3_mul_three, one_mul]
    _ = inv3 m * (3 * y) := by rw [h]
    _ = y := by rw [← mul_assoc, inv3_mul_three, one_mul]

/-- The odd reverse branch is unique. -/
theorem oddBack_unique (m : ℕ) (x y : ZMod (2 ^ m))
    (h : 3 * x + 1 = 2 * y) : x = oddBack m y := by
  apply three_mul_injective m
  have hx : 3 * x = 2 * y - 1 := by linear_combination h
  have hb : 3 * oddBack m y = 2 * y - 1 := by
    have hs := oddBack_spec m y
    linear_combination hs
  exact hx.trans hb.symm

end AgdaMirror.CollatzSyracuseInv3Exact
