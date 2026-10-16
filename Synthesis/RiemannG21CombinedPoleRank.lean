import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Synthesis.RiemannG21LiteralPoleParityTransversality

/-!
# G21 combined pole rank: pre-combination rank two vs post-combination rank one

The literal Weil explicit formula contains the SUM

  h(i/2) + h(-i/2).

For the real-even taper family, the two sampled pole evaluations form a
conjugate pair.  Therefore after the explicit-formula sum has actually been
formed, each sample sees

  z + conj z = 2 Re z,

which has zero odd/imagininary component.  Across an arbitrary sample set the
combined pole contribution is consequently one sample profile.

This does NOT retroactively prove that the two evaluation maps are dependent as
separate maps.  Any construction which acts on `h(i/2)` and `h(-i/2)` before
summing must retain the robust rank-two nuisance model.  Rank-one promotion is
lawful only for a consumer proved to factor through the literal combined sum.

This distinction sharpens the older fail-closed rank audit without invalidating
its four-sample fallback.
-/

noncomputable section

namespace Synthesis

/-- A conjugate pair sums to a purely real quantity. -/
theorem combinedConjugatePole_im_zero (z : ℂ) :
    (z + starRingEnd ℂ z).im = 0 := by
  simp

/-- Explicit form of the combined conjugate pair. -/
theorem combinedConjugatePole_eq_two_re (z : ℂ) :
    z + starRingEnd ℂ z = ((2*z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

/-- Once the two evaluations have actually been summed, the whole nuisance over
any sample type is represented by one combined profile. -/
theorem combinedPole_has_singleProfile
    {Sample : Type*} (positivePole : Sample → ℂ) :
    ∃ profile : Sample → ℂ,
      ∀ x, positivePole x + starRingEnd ℂ (positivePole x) = profile x := by
  exact ⟨fun x => positivePole x + starRingEnd ℂ (positivePole x), fun _ => rfl⟩

/-- In a parity decomposition whose odd coordinate is the imaginary part, the
combined conjugate pole has identically zero odd nuisance. -/
theorem combinedPole_oddParity_zero
    {Sample : Type*} (positivePole : Sample → ℂ) :
    ∀ x, (positivePole x + starRingEnd ℂ (positivePole x)).im = 0 :=
  fun x => combinedConjugatePole_im_zero (positivePole x)

/-- Source-facing attachment: this is the precise hypothesis needed to reduce
an individually rank-two pole model to the one-profile combined model. -/
structure CombinedPoleConsumerAttachment {Sample : Type*} where
  positivePole negativePole : Sample → ℂ
  consumerPole : Sample → ℂ
  negative_is_conjugate : ∀ x, negativePole x = starRingEnd ℂ (positivePole x)
  consumer_factors_through_sum :
    ∀ x, consumerPole x = positivePole x + negativePole x

/-- An attached sum-consuming pole nuisance is a single purely-even profile. -/
theorem CombinedPoleConsumerAttachment.consumer_eq_two_re
    {Sample : Type*} (A : CombinedPoleConsumerAttachment (Sample:=Sample)) :
    ∀ x, A.consumerPole x = ((2*(A.positivePole x).re : ℝ) : ℂ) := by
  intro x
  rw [A.consumer_factors_through_sum x, A.negative_is_conjugate x]
  exact combinedConjugatePole_eq_two_re _

/-- Consequently its odd parity coordinate is zero. -/
theorem CombinedPoleConsumerAttachment.consumer_im_zero
    {Sample : Type*} (A : CombinedPoleConsumerAttachment (Sample:=Sample)) :
    ∀ x, (A.consumerPole x).im = 0 := by
  intro x
  rw [A.consumer_eq_two_re x]
  simp

/-- Fail-closed boundary: conjugacy alone says nothing about a consumer that
continues to expose the two pole evaluations separately.  This tiny exact
counterexample keeps the distinction explicit. -/
theorem separateEvaluationConsumer_notDeterminedBySum :
    let z1 : ℂ := 1 + Complex.I
    let z2 : ℂ := 1 - Complex.I
    z1 + starRingEnd ℂ z1 = z2 + starRingEnd ℂ z2 ∧ z1 ≠ z2 := by
  norm_num [Complex.ext_iff]

end Synthesis
