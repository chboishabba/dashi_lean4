import Mathlib

/-!
# Finite Gibbs disintegration: exact exterior-only factor cancellation

Theorem donor: elementary normalization of finite Gibbs densities
(classical finite-volume DLR/Markov-random-field locality).
For a bare plaquette-local Wilson law, a change of an exterior coordinate
not belonging to any plaquette touching the selected interior changes
only an x-independent factor. This lemma proves that factor cancels.

It does NOT instantiate the original SU(N) continuous Haar carrier,
prove a plaquette-incidence coverage theorem, or estimate the blocked
effective versus renormalized target law. The required same-source
Wilson action/measure and boundary geometry are explicit OPEN inputs.

Source: DASHI original F19/P0/R445 + PR #1503 weighted conditional TV.
Lean 4.28 source-written; no kernel check in this runtime.
-/

namespace Synthesis.YMFiniteRangeGibbs
noncomputable section

variable {α β : Type*} [DecidableEq α]

/-- The exact density of the interior conditional law, with
an exterior-only positive scalar factor. -/
def conditionalWeight (interior : Finset α) (w : α → ℝ)
    (outside : β → ℝ) (y : β) (x : α) : ℝ :=
  (outside y * w x) / (∑ z ∈ interior, outside y * w z)

/-- No independence assumption on the *outside probability law* is used.
The cancellation is conditional normalization on the same interior. -/
theorem exteriorFactorCancels
    (interior : Finset α) (w : α → ℝ) (outside : β → ℝ)
    (y : β) (hy : outside y ≠ 0)
    (hZ : (∑ z ∈ interior, w z) ≠ 0)
    (x : α) :
    conditionalWeight interior w outside y x =
      w x / (∑ z ∈ interior, w z) := by
  unfold conditionalWeight
  have hsum : (∑ z ∈ interior, outside y * w z) =
      outside y * (∑ z ∈ interior, w z) := by
    rw [Finset.mul_sum]
  rw [hsum]
  field_simp [hy, hZ]
  <;> ring

/-- If both exterior assignments alter only an x-independent Gibbs
factor, then the normalized local conditional kernel is identical. -/
theorem farExteriorSiteHasZeroLocalInfluence
    (interior : Finset α) (w : α → ℝ) (outside : β → ℝ)
    (y₁ y₂ : β) (hy₁ : outside y₁ ≠ 0)
    (hy₂ : outside y₂ ≠ 0)
    (hZ : (∑ z ∈ interior, w z) ≠ 0) (x : α) :
    conditionalWeight interior w outside y₁ x =
      conditionalWeight interior w outside y₂ x := by
  calc
    conditionalWeight interior w outside y₁ x =
        w x / (∑ z ∈ interior, w z) :=
      exteriorFactorCancels interior w outside y₁ hy₁ hZ x
    _ = conditionalWeight interior w outside y₂ x :=
      (exteriorFactorCancels interior w outside y₂ hy₂ hZ x).symm

#print axioms exteriorFactorCancels
#print axioms farExteriorSiteHasZeroLocalInfluence

end
end Synthesis.YMFiniteRangeGibbs
