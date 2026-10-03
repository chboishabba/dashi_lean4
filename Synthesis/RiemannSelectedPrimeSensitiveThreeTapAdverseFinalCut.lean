import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseTailExhaustion
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAlphaStripWeld

/-!
# Final source-written one-scale adverse max-cut

All generic one-scale machinery has now been compressed to a single scalar test
at one RvM-compatible physical ordinate cutoff R.

The finite adverse core is paid by the explicit unconditional RvM/mu budget

  Bnear_explicit(R),

and the residual is the actual nonnegative summable adverse tail

  Bfar_actual(R).

The standard critical-strip theorem gives the canonical normalized horizontal
radius A=8/t, so no separate alpha-strip hypothesis remains.

For the universal constants supplied by the existing arbitrary-endpoint RvM
and mu theorems, the strict inequality

  1/2 * (Bnear_explicit(R) + Bfar_actual(R))
    < LocalExact - Compensation

implies negative paid resonance cost and hence a near-line PASS.

No sign or numerical inequality is introduced.  This is the final analytic
one-scale decision surface exposed by the current source.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Universal source constants and the final RvM-compatible one-scale PASS
compiler, with the alpha strip supplied explicitly. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdverseFinalCut_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps A R : ℝ},
        200 <= t ->
        0 <= A ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapAlphaStripBound A ->
        W.ThreeTapRvMCompatibleCutoff R ->
        ((1/2 : ℝ) *
          (W.threeTapAdverseNearExplicitBudget eps A R C Cmu
            + W.threeTapPairAdverseFarAfter eps R)
          < W.threeTapAdaptiveLocalExact eps
              - W.threeTapResonanceCompensation eps) ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hnear⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseNearExplicitBudget_bound
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps A R ht hA W hstrip hcompat hscalar
  rcases hcompat with ⟨hR,hleft⟩
  have hnearBound :
      W.threeTapPairAdverseNearAt eps R
        <= W.threeTapAdverseNearExplicitBudget eps A R C Cmu :=
    hnear ht hA hR hleft W hstrip
  exact W.threeTapResonancePaidCost_neg_of_explicitNear_and_far
    ht hnearBound le_rfl hscalar

/-- Canonical one-scale cut.  The only variable analytic choice remaining is
the RvM-compatible ordinate cutoff R; A is fixed to 8/t by the zero strip. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdverseCanonicalFinalCut_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps R : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapRvMCompatibleCutoff R ->
        ((1/2 : ℝ) *
          (W.threeTapAdverseNearExplicitBudget eps
              (threeTapCanonicalAlphaRadius t) R C Cmu
            + W.threeTapPairAdverseFarAfter eps R)
          < W.threeTapAdaptiveLocalExact eps
              - W.threeTapResonanceCompensation eps) ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hcut⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseFinalCut_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps R ht W hcompat hscalar
  exact hcut ht
    (threeTapCanonicalAlphaRadius_nonneg (by linarith : 0 < t))
    W (W.threeTapAlphaStripBound_canonical (by linarith : 0 < t))
    hcompat hscalar

/-- Direct near-line PASS version of the canonical final scalar cut. -/
theorem QuarticFourSignedPolePair.exists_threeTapAdverseCanonicalFinalCut_terminal_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps mult R : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapRvMCompatibleCutoff R ->
        Real.cos (t * Real.log 2) = 0 ->
        ((1/2 : ℝ) *
          (W.threeTapAdverseNearExplicitBudget eps
              (threeTapCanonicalAlphaRadius t) R C Cmu
            + W.threeTapPairAdverseFarAfter eps R)
          < W.threeTapAdaptiveLocalExact eps
              - W.threeTapResonanceCompensation eps) ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ a : ℝ, 0 < a -> a < delta ->
            0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  obtain ⟨C,Cmu,hC,hCmu,hcut⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseCanonicalFinalCut_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps mult R ht W hcompat hphase hscalar
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact hcut ht W hcompat hscalar

/-- Canonical final scalar using the source-owned strip radius A=8/t. -/
def QuarticFourSignedPolePair.ThreeTapAdverseCanonicalFinalScalar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps R C Cmu : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (W.threeTapAdverseNearExplicitBudget eps
        (threeTapCanonicalAlphaRadius t) R C Cmu
      + W.threeTapPairAdverseFarAfter eps R)
    -
  (W.threeTapAdaptiveLocalExact eps
    - W.threeTapResonanceCompensation eps)

theorem QuarticFourSignedPolePair.threeTapAdverseCanonicalFinalScalar_neg_iff
    {t eps R C Cmu : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.ThreeTapAdverseCanonicalFinalScalar eps R C Cmu < 0
      <->
    (1/2 : ℝ) *
      (W.threeTapAdverseNearExplicitBudget eps
          (threeTapCanonicalAlphaRadius t) R C Cmu
        + W.threeTapPairAdverseFarAfter eps R)
      < W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps := by
  unfold QuarticFourSignedPolePair.ThreeTapAdverseCanonicalFinalScalar
  linarith

end Synthesis
