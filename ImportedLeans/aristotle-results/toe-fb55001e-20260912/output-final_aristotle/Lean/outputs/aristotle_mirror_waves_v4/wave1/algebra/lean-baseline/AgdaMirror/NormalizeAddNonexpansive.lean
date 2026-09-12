import Mathlib
import AgdaMirror.NormalizeAdd

/-!
# Lean mirror of `DASHI/Arithmetic/NormalizeAddNonexpansive.agda` (genuine, fully proved)

The one-step carry resolution `normalizeAdd` is *non-expansive* on the `p`-adic
agreement surface: if `x` and `y` agree on prime and `p`-adic depth up to `k`,
so do their resolved states.  This holds because `normalizeAdd` preserves both
the prime and the `p`-adic depth fields.
-/

namespace AgdaMirror.NormalizeAddNonexpansive

open AgdaMirror.NormalizeAdd

/-- `normalizeAdd` preserves `p`-adic agreement up to depth `k`. -/
theorem normalizeAdd_nonexpansive (x y : NormalizeAddState) (k : Nat)
    (h : padicAgreement x y k) :
    padicAgreement (normalizeAdd x) (normalizeAdd y) k := by
  obtain ⟨samePrime, samePadicDepth, kx, ky⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [normalizeAdd_primePreserved, normalizeAdd_primePreserved]; exact samePrime
  · rw [normalizeAdd_padicDepthPreserved, normalizeAdd_padicDepthPreserved]; exact samePadicDepth
  · rw [normalizeAdd_padicDepthPreserved]; exact kx
  · rw [normalizeAdd_padicDepthPreserved]; exact ky

/-- The non-expansiveness contract, witnessed. -/
structure NonexpansiveContract where
  nonexpansive : ∀ x y k, padicAgreement x y k →
    padicAgreement (normalizeAdd x) (normalizeAdd y) k

/-- The canonical non-expansiveness witness. -/
def firstNormalizeAddNonexpansive : NonexpansiveContract :=
  ⟨normalizeAdd_nonexpansive⟩

end AgdaMirror.NormalizeAddNonexpansive
