import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFiniteAsymptotic
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapGlobalize
import Synthesis.RiemannSelectedPrimeSensitiveTwoScalePromotion

/-!
# RH max-cut frontier after analytic compression

This is the import boundary for the live analytic frontier.

One-scale resonance has now been compressed past the abstract reflection tail:

* the actual transformed pair series is split into adverse mass minus favorable
  credit;
* the adverse phase is alpha-independent before the positive cosh weight;
* the finite adverse core is welded to the literal N-mu RvM carrier through an
  absolutely-continuous Abel theorem;
* the RvM discrepancy, smooth mu term, endpoint term and variation term are
  assembled into `threeTapAdverseNearExplicitBudget`;
* the residual adverse tail is the actual summable tail after the chosen
  physical cutoff;
* the cutoff tradeoff is explicit and the canonical half-height choice R=t/2
  is compatible for t>=200;
* the finite half-height core is collapsed from M0/M1 to the single canonical
  normalized mass `threeTapCanonicalM0`;
* translation itself does not enlarge L1 mass, and radius-one projectivization
  obeys the same-object quadratic envelope `||P_g||_1 <= 8 ||g||_1^2`;
* the actual four-window witness has endpoint source mass <= 3 and finite pole
  coefficients bounded by `18*cosh(1)`, yielding the explicit uniform bound
  `M0 <= 2592*cosh(1)^2*(1+2|eps|)^2`;
* therefore the finite Route-A budget contains no remaining zeta-distribution
  input: `threeTapUniformFiniteHalfHeightBudget` is explicit and obeys a
  source-visible log-over-t envelope;
* the final producer-facing PASS surface is now exactly: explicit finite
  budget <= H, actual half-height adverse tail < H, and
  H <= LocalExact-Compensation.

Thus the first genuinely zero-distribution-specific Route-A obligation is the
actual adverse tail at the compatible half-height cutoff.  Unrestricted
summability only supplies an eta-small tail at some large cutoff and does not
place that cutoff before t-5.

After a one-scale PASS, only compact mid-strip positivity remains before the
full 0<a<=1/2 displacement statement.  A strict one-scale FAIL exposes the
already-built independent log2/log3 two-scale source.

The independent signed-fifth route is exposed by the single finite scalar
`signedFifthCorrelationGapAt = Credit - Debt + OuterBudget - 3 eps`;
eventual nonnegativity is exactly the existing signed-fifth interior target.
No RH theorem and no unpaid analytic sign are asserted here.
-/

noncomputable section
namespace Synthesis

open scoped Real

/-- Full one-scale displacement positivity immediately gives positivity of the
actual adaptive terminal margin for any selected zero whose positive horizontal
displacement lies in the critical half-strip. -/
theorem QuarticFourSignedPolePair.threeTapAllOffLineDisplacementsPositive_terminalMargin
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hglobal :
      W.ThreeTapAllOffLineDisplacementsPositive eps
        ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ))
    (hpos : 0 < heightOf rho)
    (hhalf : heightOf rho <= (1/2 : ℝ)) :
    0 < W.threeTapAdaptiveTerminalMargin eps rho := by
  rw [W.threeTapAdaptiveTerminalMargin_eq_profile]
  exact hglobal (heightOf rho) hpos hhalf

/-- The source-level research fork after the max-cut.  The left branch is a
fully globalized one-scale deformation; the right branch is the independent
signed-fifth analytic input. -/
def QuarticFourSignedPolePair.RHMaxCutRoute
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (epsTap mult : ℝ)
    (rho : Zeros) (EV epsFifth : ℝ) : Prop :=
  W.ThreeTapAllOffLineDisplacementsPositive epsTap mult
    ∨ W.SignedFifthAnalyticInput rho EV epsFifth

/-- The signed-fifth branch of the route fork lands immediately on the common
canonical terminal consumer. -/
theorem QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
    {t epsTap mult EV epsFifth : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hroute : W.RHMaxCutRoute epsTap mult rho EV epsFifth)
    (hnotThreeTap :
      ¬ W.ThreeTapAllOffLineDisplacementsPositive epsTap mult) :
    W.CanonicalTerminalPositive rho EV := by
  rcases hroute with hthree | hfifth
  · exact False.elim (hnotThreeTap hthree)
  · exact W.signedFifthAnalyticInput_compiles_terminalPositive ht rho hfifth

/-- A strict one-scale failure and t >= 300 expose the precise two-scale source
surface while leaving the signed-fifth route untouched. -/
theorem QuarticFourSignedPolePair.oneScaleFail_frontier
    {t epsTap mult e2 e3 EV epsFifth : ℝ}
    (ht : 300 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hfail : W.ThreeTapNearLineFails epsTap mult) :
    (W.ThreeTapNearLineFails epsTap mult
      ∧ W.TwoScaleEndpointSamples e2 e3)
    ∧
    (W.SignedFifthAnalyticInput rho EV epsFifth
      → W.CanonicalTerminalPositive rho EV) := by
  constructor
  · exact W.threeTapFail_promotes_twoScaleSource ht hfail
  · intro hfifth
    exact W.signedFifthAnalyticInput_compiles_terminalPositive
      (by linarith) rho hfifth

end Synthesis
