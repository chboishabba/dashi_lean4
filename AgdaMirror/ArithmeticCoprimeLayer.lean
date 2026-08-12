import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.CoprimeLayer
import AgdaMirror.TrackedCoprimeTable

/-!
# Lean mirror of `DASHI/Arithmetic/CoprimeLayer.agda` (tracked-carrier version)

The "tracked-only arithmetic seam": distinct tracked prime powers are coprime
(`distinctTrackedPrimePowersCoprime`), specialised to the `SSP` carrier and its
`toNat` embedding, plus the reusable coprime product-divisibility lemma
(`coprimeProductDivides`).  Both are proved from the generic `ℕ` layer
(`AgdaMirror.CoprimeLayer`) and the tracked-base coprimality table.
-/

namespace AgdaMirror.ArithmeticCoprimeLayer

open AgdaMirror.MonsterOntos
open AgdaMirror.TrackedCoprimeTable
open SSP

/-- Distinct tracked prime powers are coprime. -/
theorem distinctTrackedPrimePowersCoprime (p q : SSP) (a b : Nat) (h : p ≠ q) :
    Nat.Coprime (toNat p ^ a) (toNat q ^ b) :=
  AgdaMirror.CoprimeLayer.distinctPrimePowersCoprime a b (distinctTrackedBasesCoprime p q h)

/-- Coprime divisors multiply. -/
theorem coprimeProductDivides {m n o : Nat}
    (c : Nat.Coprime m n) (hm : m ∣ o) (hn : n ∣ o) : m * n ∣ o :=
  AgdaMirror.CoprimeLayer.coprimeProductDivides c hm hn

end AgdaMirror.ArithmeticCoprimeLayer
