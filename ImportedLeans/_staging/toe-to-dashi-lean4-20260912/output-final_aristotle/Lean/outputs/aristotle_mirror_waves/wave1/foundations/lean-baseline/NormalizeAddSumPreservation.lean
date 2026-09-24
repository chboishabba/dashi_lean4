import Mathlib
import AgdaMirror.NormalizeAdd
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.MonsterOntos

/-!
# Lean mirror of `DASHI/Arithmetic/NormalizeAddSumPreservation.agda` (genuine, fully proved)

The `normalizeAdd` step resolves residue/carry bookkeeping fields but never
rewrites `lhs` or `rhs`.  Therefore the observable sum `lhs + rhs` is
definitionally preserved, and so is its `p`-adic valuation for every (tracked)
prime.  This is a genuine positive invariant; faithful to the Agda's note, it is
*not* a W2 kill receipt by itself.
-/

namespace AgdaMirror.NormalizeAddSumPreservation

open AgdaMirror.NormalizeAdd
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.MonsterOntos

/-- The observable sum is preserved by one step. -/
theorem normalizeAdd_sumPreserved (s : NormalizeAddState) :
    (normalizeAdd s).lhs + (normalizeAdd s).rhs = s.lhs + s.rhs := rfl

/-- The `p`-adic valuation of the observable sum is preserved (any prime). -/
theorem vpSumInvariant (p : Nat) (s : NormalizeAddState) :
    vp p ((normalizeAdd s).lhs + (normalizeAdd s).rhs) = vp p (s.lhs + s.rhs) := rfl

/-- Same invariant for the 15 tracked primes. -/
theorem trackedPrimeVpSumInvariant (p : SSP) (s : NormalizeAddState) :
    vp (toNat p) ((normalizeAdd s).lhs + (normalizeAdd s).rhs)
      = vp (toNat p) (s.lhs + s.rhs) := rfl

/-- The sum-preservation receipt as a bundled record (with the non-promotion
boundary kept as an honest abstract field, never an axiom). -/
structure NormalizeAddSumPreservationReceipt where
  State : Type
  step : State → State
  sumObservable : State → Nat
  sumPreserved : ∀ s, sumObservable (step s) = sumObservable s
  pAdicSumInvariant : ∀ (p : Nat) (s : State),
    vp p (sumObservable (step s)) = vp p (sumObservable s)
  trackedPrimeInvariant : ∀ (p : SSP) (s : State),
    vp (toNat p) (sumObservable (step s)) = vp (toNat p) (sumObservable s)
  nonPromotionBoundary : Prop

/-- The canonical receipt instance built from `normalizeAdd`. -/
def canonicalNormalizeAddSumPreservationReceipt : NormalizeAddSumPreservationReceipt where
  State := NormalizeAddState
  step := normalizeAdd
  sumObservable := fun s => s.lhs + s.rhs
  sumPreserved := normalizeAdd_sumPreserved
  pAdicSumInvariant := vpSumInvariant
  trackedPrimeInvariant := trackedPrimeVpSumInvariant
  nonPromotionBoundary := True

end AgdaMirror.NormalizeAddSumPreservation
