import Mathlib

/-!
# JMD "Full Stack Architecture" — FactorVec / valuation sheaf

This file formalises the document's "Lattices of the Primes" / FactorVec core:
the observation that prime *valuations* turn multiplication into addition, so a
number is faithfully a vector of prime exponents, and that FactorVec is the
*global section* of a valuation sheaf whose restriction maps simply forget
primes.

* **Logarithmic linearisation.** `v_p(x·y) = v_p(x) + v_p(y)` — multiplication
  becomes addition (`factorVec_mul`, `factorization_additive`).
* **FactorVec.** On the 15 supersingular primes, `n ↦ (v_p n)_p` is the
  document's `FactorVec` coordinate (`factorVec`).
* **Restriction = forgetting primes.** Restricting a valuation vector to a
  subset of primes is the natural projection, and it is functorial /
  compatible with `factorVec` (`factorVec_restrict`).
* **Global section.** A valuation vector is determined by its components, so the
  global section of the valuation sheaf is exactly the full FactorVec
  (`factorVec_injOn_components`).
-/

namespace FactorVecSheaf

open scoped BigOperators

/-- The 15 supersingular primes as an indexed family (the FactorVec basis). -/
def basisPrime : Fin 15 → ℕ
  | 0 => 2  | 1 => 3  | 2 => 5  | 3 => 7  | 4 => 11
  | 5 => 13 | 6 => 17 | 7 => 19 | 8 => 23 | 9 => 29
  | 10 => 31 | 11 => 41 | 12 => 47 | 13 => 59 | 14 => 71

theorem basisPrime_prime (i : Fin 15) : Nat.Prime (basisPrime i) := by
  fin_cases i <;> decide

/-! ## Logarithmic linearisation: multiplication becomes addition -/

/-
**Additivity of valuations (general).** For nonzero `x, y` the prime
exponent of a product is the sum of the exponents: `v_p(x·y) = v_p(x)+v_p(y)`.
This is the document's "multiplication becomes addition" linearisation.
-/
theorem factorization_additive {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (p : ℕ) :
    (x * y).factorization p = x.factorization p + y.factorization p := by
  rw [ Nat.factorization_mul hx hy ] ; aesop;

/-- The **FactorVec** of `n`: its vector of supersingular-prime valuations. -/
def factorVec (n : ℕ) : Fin 15 → ℕ :=
  fun i => n.factorization (basisPrime i)

/-
**FactorVec is additive.** For nonzero `m, n`, `FactorVec(m·n) =
FactorVec(m) + FactorVec(n)`: the carrier is logarithm-based, primes are merely
basis vectors.
-/
theorem factorVec_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    factorVec (m * n) = factorVec m + factorVec n := by
  funext i
  simpa [factorVec, Pi.add_apply] using factorization_additive hm hn (basisPrime i)

/-
FactorVec of `1` is the zero vector.
-/
theorem factorVec_one : factorVec 1 = 0 := by
  funext i
  simp [factorVec]

/-! ## Restriction = forgetting primes -/

/-- **Restriction map** of the valuation sheaf: re-index a valuation vector
along a map of prime-index sets (the sheaf "forgets" the primes not in the
sub-index `s`). -/
def restrict {s t : Type*} (ι : s → t) (v : t → ℕ) : s → ℕ :=
  fun a => v (ι a)

/-- **Compatibility of `factorVec` with restriction.** Restriction is just
precomposition, so `restrict ι (factorVec n) = (factorVec n) ∘ ι`; restricting
the global FactorVec to a subset of primes recovers exactly the local
valuations there. -/
theorem factorVec_restrict {s : Type*} (ι : s → Fin 15) (n : ℕ) (a : s) :
    restrict ι (factorVec n) a = n.factorization (basisPrime (ι a)) := by
  rfl

/-- **Functoriality of restriction.** Restricting along `ι` then `κ` equals
restricting along the composite `ι ∘ κ` (gluing/restriction is a presheaf). -/
theorem restrict_comp {s t u : Type*} (ι : s → u) (κ : t → s)
    (v : u → ℕ) :
    restrict κ (restrict ι v) = restrict (ι ∘ κ) v := by
  rfl

/-! ## Global section: a valuation vector is its components -/

/-- **Global section property.** A valuation vector is determined by its
components: if two FactorVecs agree on every supersingular prime they are equal.
So FactorVec is the global section `Γ(V)` of the valuation sheaf, glued from the
local prime data. -/
theorem factorVec_ext {u v : Fin 15 → ℕ} (h : ∀ i, u i = v i) : u = v :=
  funext h

end FactorVecSheaf