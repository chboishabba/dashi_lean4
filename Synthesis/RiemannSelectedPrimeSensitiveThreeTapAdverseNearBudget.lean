import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseMuBound

/-!
# Fully explicit transformed adverse near-core budget

The finite adverse pair core now has two independent existing analytic inputs:

* arbitrary-endpoint literal N-mu discrepancy, with constant `C`;
* theorem-bearing `|mu(x)| <= Cmu log(x+3)`, with constant `Cmu`.

This file packages the resulting source-visible upper bound.  Nothing from the
far adverse tail is included here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Fully expanded finite-core budget. -/
def QuarticFourSignedPolePair.threeTapAdverseNearExplicitBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A R C Cmu : ℝ) : ℝ :=
  let E := C * (Real.log ((t-R)+3) + Real.log ((t+R)+4))
  let M := (1/(t/16)^2) * W.threeTapKernelAdverseAlphaSupMass eps A
  let U := Cmu * Real.log ((t+R)+3)
  (2*R) * M * U
    + E * W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
    + (2*R) * E * W.threeTapAdversePhysicalLipschitzMass eps A

theorem QuarticFourSignedPolePair.exists_threeTapAdverseNearExplicitBudget_bound :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps A R : ℝ},
        200 <= t ->
        0 <= A ->
        0 < R ->
        5 <= t-R ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapAlphaStripBound A ->
        W.threeTapPairAdverseNearAt eps R
          <= W.threeTapAdverseNearExplicitBudget eps A R C Cmu := by
  obtain ⟨C,hC,hnear⟩ :=
    QuarticFourSignedPolePair.exists_threeTapPairAdverseNearAt_rvm_bound
  obtain ⟨Cmu,hCmu,hmu⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseMuMass_bound
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps A R ht hA hR hleft W hstrip
  have hnear' := hnear ht hA hR hleft W hstrip
  have hmu' := hmu (by linarith : 0 < t) hR.le (by linarith : 1 <= t-R) W
  unfold QuarticFourSignedPolePair.threeTapAdverseNearExplicitBudget
  exact hnear'.trans (by
    linarith)

/-- Once the finite RvM core and a far-tail producer fit below the paid
threshold, one-scale resonance passes.  This is the current fully expanded
producer-facing PASS theorem. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_of_explicitNear_and_far
    {t eps A R C Cmu Bfar : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hnear :
      W.threeTapPairAdverseNearAt eps R
        <= W.threeTapAdverseNearExplicitBudget eps A R C Cmu)
    (hfar : W.threeTapPairAdverseFarAfter eps R <= Bfar)
    (hbudget :
      (1/2 : ℝ) *
        (W.threeTapAdverseNearExplicitBudget eps A R C Cmu + Bfar)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    W.threeTapResonancePaidCost eps < 0 := by
  exact W.threeTapResonancePaidCost_neg_of_near_far_bounds
    (R:=R) ht hnear hfar hbudget

/-- Same compiler directly to the near-line PASS band. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_explicitNear_and_far
    {t eps mult A R C Cmu Bfar : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hnear :
      W.threeTapPairAdverseNearAt eps R
        <= W.threeTapAdverseNearExplicitBudget eps A R C Cmu)
    (hfar : W.threeTapPairAdverseFarAfter eps R <= Bfar)
    (hbudget :
      (1/2 : ℝ) *
        (W.threeTapAdverseNearExplicitBudget eps A R C Cmu + Bfar)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a -> a < delta ->
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact W.threeTapResonancePaidCost_neg_of_explicitNear_and_far
    ht hnear hfar hbudget

end Synthesis
