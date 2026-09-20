import Synthesis.RiemannAdaptiveCutoffCrossingCompatibility
import Synthesis.RiemannCenteredNearPairSign
import Synthesis.RiemannCanonicalReflectionCoefficientGate

/-!
# Adaptive-cutoff / centered-near-sign incompatibility

The current high-side ingredients impose opposite cutoff requirements.

The centered finite-near sign theorem is valid only while

  J * Lambda <= pi/2.

The generic adaptive-cutoff selector in
`RiemannAdaptiveCutoffCrossingCompatibility` deliberately chooses a cutoff
past the quarter-period threshold,

  pi/2 < J * Lambda,

in order to allow arbitrarily large natural cutoffs.

These hypotheses cannot be combined.  In particular, on the canonical support

  Lambda_t = 9*pi/(4*t),

the sign window forces

  J <= 2*t/9.

Hence the existing signed-near proof cannot simply inherit a quartic or
horizontal-displacement-adaptive cutoff.  A prize-facing repair must instead
shrink the support with the displacement or prove additional signed
cancellation after the first cosine sign change.
-/

noncomputable section

open scoped Real

namespace Synthesis

theorem quarterPeriodCrossing_excludes_signWindow
    {Lambda : ℝ} {J : ℕ}
    (hcross : Real.pi / 2 < (J : ℝ) * Lambda) :
    ¬ (J : ℝ) * Lambda <= Real.pi / 2 := by
  exact not_le_of_gt hcross

theorem signWindow_excludes_quarterPeriodCrossing
    {Lambda : ℝ} {J : ℕ}
    (hwindow : (J : ℝ) * Lambda <= Real.pi / 2) :
    ¬ Real.pi / 2 < (J : ℝ) * Lambda := by
  exact not_lt_of_ge hwindow

/-- On the fixed canonical support, the cosine-sign argument permits only a
linear-in-t cutoff. -/
theorem canonical_signWindow_implies_cutoff_le
    {t : ℝ} {J : ℕ}
    (ht : 0 < t)
    (hwindow :
      (J : ℝ) * canonicalProjectiveLambda t <= Real.pi / 2) :
    (J : ℝ) <= 2 * t / 9 := by
  have hden : 0 < 4 * t := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold canonicalProjectiveLambda at hwindow
  rw [mul_div_assoc] at hwindow
  have hcross :=
    (div_le_iff₀ hden).mp hwindow
  have h9 : 9 * (J : ℝ) <= 2 * t := by
    nlinarith
  linarith

/-- Therefore any cutoff strictly larger than 2t/9 has already left the region
where `centeredFiniteNearCore_nonpos` can be invoked on the canonical
support. -/
theorem canonical_largeCutoff_excludes_signWindow
    {t : ℝ} {J : ℕ}
    (ht : 0 < t)
    (hlarge : 2 * t / 9 < (J : ℝ)) :
    ¬ (J : ℝ) * canonicalProjectiveLambda t <= Real.pi / 2 := by
  intro hwindow
  have hJ := canonical_signWindow_implies_cutoff_le ht hwindow
  linarith

/-- The existing adaptive selector cannot simultaneously furnish the hypothesis
used by the centered finite-near sign theorem. -/
theorem selected_crossing_cutoff_cannot_pay_centeredNearSign
    {Lambda eps : ℝ}
    (hLambda : 0 < Lambda) (heps : 0 < eps)
    {far : ℕ -> ℝ}
    (hfar : Filter.Tendsto far Filter.atTop (nhds 0)) :
    ∃ J : ℕ, 1 <= J
      ∧ Real.pi / 2 < (J : ℝ) * Lambda
      ∧ far J < eps
      ∧ ¬ (J : ℝ) * Lambda <= Real.pi / 2 := by
  obtain ⟨J, hJ, hcross, hsmall⟩ :=
    exists_nat_cutoff_crossing_and_small hLambda heps hfar
  exact ⟨J, hJ, hcross, hsmall,
    quarterPeriodCrossing_excludes_signWindow hcross⟩

end Synthesis
