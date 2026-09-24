import Mathlib

/-!
# Lean mirror of `DASHI/Arithmetic/CoprimeLayer.agda` (genuine number theory)

Faithful transcription of the "tracked-only arithmetic seam": the coprimality
layer used by the DASHI valuation arithmetic.  The Agda module works over the
tracked supersingular-prime carrier `SSP` with `toNat`, deriving from the
distinct-base coprimality table.  Here we capture the genuine mathematical
content directly over `ℕ`:

* distinct coprime bases give coprime prime powers
  (`distinctPrimePowersCoprime`), proved from the base coprimality;
* coprime divisors multiply: if `m, n` are coprime and both divide `o`, then
  `m * n ∣ o` (`coprimeProductDivides`).

These are exactly the two laws bundled in the Agda `CoprimeLayer` record, here
proved with no `sorry` and axiom-clean.
-/

namespace AgdaMirror.CoprimeLayer

/-- A tracked base `b` (coprime to a distinct base) raised to a power stays
coprime to powers of the other base. -/
theorem baseVsPrimePowerCoprime {p q : Nat} (b : Nat) (h : Nat.Coprime p q) :
    Nat.Coprime p (q ^ b) :=
  h.pow_right b

/-- Distinct coprime bases give coprime prime powers (mirrors
`distinctTrackedPrimePowersCoprime`). -/
theorem distinctPrimePowersCoprime {p q : Nat} (a b : Nat) (h : Nat.Coprime p q) :
    Nat.Coprime (p ^ a) (q ^ b) :=
  (h.pow_left a).pow_right b

/-- Coprime divisors multiply (mirrors `coprimeProductDivides`). -/
theorem coprimeProductDivides {m n o : Nat}
    (c : Nat.Coprime m n) (hm : m ∣ o) (hn : n ∣ o) : m * n ∣ o :=
  c.mul_dvd_of_dvd_of_dvd hm hn

/-- The packaged coprime-layer surface (mirrors the Agda `CoprimeLayer` record),
specialised to a tracked carrier `T` with a coprime-on-distinct base map. -/
structure CoprimeLayerSurface (T : Type) (toNat : T → Nat)
    (basesCoprime : ∀ p q : T, p ≠ q → Nat.Coprime (toNat p) (toNat q)) where
  primePowersCoprime :
    ∀ (p q : T) (a b : Nat), p ≠ q →
      Nat.Coprime (toNat p ^ a) (toNat q ^ b)
  productDivides :
    ∀ m n o : Nat, Nat.Coprime m n → m ∣ o → n ∣ o → m * n ∣ o

/-- The canonical coprime layer over any tracked carrier whose distinct bases are
coprime. -/
def coprimeLayer (T : Type) (toNat : T → Nat)
    (basesCoprime : ∀ p q : T, p ≠ q → Nat.Coprime (toNat p) (toNat q)) :
    CoprimeLayerSurface T toNat basesCoprime where
  primePowersCoprime := fun p q a b hpq =>
    distinctPrimePowersCoprime a b (basesCoprime p q hpq)
  productDivides := fun _ _ _ c hm hn => coprimeProductDivides c hm hn

end AgdaMirror.CoprimeLayer
