import Mathlib
import AgdaMirror.MonsterOntos

/-!
# Lean mirror of `DASHI/Arithmetic/TrackedCoprimeTable.agda` (genuine, fully proved)

The canonical tracked-base coprime evidence over the 15 supersingular primes.
Distinct tracked bases have coprime `Nat` images (`distinctTrackedBasesCoprime`),
the centralised `15 × 15` coprimality table downstream arithmetic modules
consume as a single theorem.  Proved by exhaustive decision over the finite
carrier.
-/

namespace AgdaMirror.TrackedCoprimeTable

open AgdaMirror.MonsterOntos
open SSP

/-- The gcd table: `toNat p` on the diagonal, `1` off-diagonal. -/
def gcdTable (p q : SSP) : Nat := if p = q then toNat p else 1

theorem gcdTable_distinct (p q : SSP) (h : p ≠ q) : gcdTable p q = 1 := by
  simp [gcdTable, h]

/-- Distinct tracked bases are coprime (the centralised table). -/
theorem distinctTrackedBasesCoprime (p q : SSP) (h : p ≠ q) :
    Nat.Coprime (toNat p) (toNat q) := by
  cases p <;> cases q <;> first | exact absurd rfl h | decide

end AgdaMirror.TrackedCoprimeTable
