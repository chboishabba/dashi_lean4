import Mathlib.NumberTheory.SumTwoSquares

/-!
# CM split-prime witness producer for E : y^2 = x^3 - x

Mathlib already proves Fermat's two-squares theorem.  This file extracts the
exact witness required by the Agda CM coefficient lane for primes p ≡ 1 mod 4.

It does NOT identify the signed Frobenius trace of the elliptic curve; the CM
primary/sign normalization remains a separate theorem.
-/

namespace Synthesis.Millennium.BSD

structure SplitPrimeWitness (p : ℕ) where
  u : ℕ
  v : ℕ
  normExact : p = u ^ 2 + v ^ 2

theorem splitPrimeWitness_of_mod_four_eq_one
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    Nonempty (SplitPrimeWitness p) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, v, huv⟩ := hp.sq_add_sq (by omega)
  exact ⟨⟨u, v, huv.symm⟩⟩

def cmMagnitude {p : ℕ} (w : SplitPrimeWitness p) : ℕ :=
  2 * w.u

def cmCompanion {p : ℕ} (w : SplitPrimeWitness p) : ℕ :=
  2 * w.v

theorem doubled_norm_identity
    {p : ℕ} (w : SplitPrimeWitness p) :
    cmMagnitude w ^ 2 + cmCompanion w ^ 2 = 4 * p := by
  rw [cmMagnitude, cmCompanion, w.normExact]
  ring

end Synthesis.Millennium.BSD
