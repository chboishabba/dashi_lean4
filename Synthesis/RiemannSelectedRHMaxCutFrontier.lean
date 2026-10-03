import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMidStripMesh
import Synthesis.RiemannSelectedPrimeSensitiveTwoScalePromotion

/-!
# RH max-cut frontier after analytic compression

This is the import boundary for the live analytic frontier.

One-scale resonance has now been compressed past the abstract reflection tail:

* the actual transformed pair series is split into adverse mass minus favorable
  credit;
* the finite adverse core is welded to the literal N-mu RvM carrier through an
  absolutely-continuous Abel theorem;
* the canonical half-height cutoff R=t/2 is RvM-compatible for t>=200;
* translation does not enlarge L1 mass and radius-one projectivization obeys
  `||P_g||_1 <= 8 ||g||_1^2`;
* endpoint source mass and pole coefficients are explicitly bounded, giving
  `M0 <= 2592*cosh(1)^2*(1+2|eps|)^2`;
* the finite Route-A budget is therefore explicit O(log t/t);
* the actual transformed pair kernel has exact q^-2 decay;
* the zeta critical strip puts every actual normalized horizontal displacement
  in the fixed compact alpha interval |alpha|<=1/25 for t>=200;
* `ThreeTapUniformCurvatureBound` now names exactly the remaining compact-alpha
  curvature theorem, with no witness-width surrogate hidden in its statement;
* the subtraction-defined actual adverse far remainder is exactly a
  complementary subtype tsum and is bounded by Ccurv times the literal
  inverse-square zero tail `threeTapInverseSquareZeroTailAfter`;
* `threeTapRouteAAdverseBudget` combines the explicit finite budget and this
  inverse-square far budget, while
  `exists_threeTapRouteAAsymptoticBalancePass_constants` compiles the strict
  comparison against the gamma+pole-minus-slack floor directly to paid-cost
  negativity;
* the compensation floor is exactly
  `-(Gamma+Pole) - LocalSlack/2`;
* after a near-line PASS, the existing finite net/Lipschitz compiler closes the
  compact mid-strip once certified node margins and a derivative bound exist.

The live Route-A analytic leaves are therefore now genuinely narrow:

1. prove the actual compact-alpha curvature bound, equivalently obtain enough
   uniform witness-width/derivative control to bound the C2 oscillatory source;
2. prove an RvM estimate for the literal inverse-square tail, ideally
   `threeTapInverseSquareZeroTailAfter t (t/2) = O(log t/t)`;
3. bound the translated gamma+pole channel above by a negative gain and the
   already-paid local slack above strongly enough that

     finite + Ccurv*inverseSquareTail < G - S/2.

No RH theorem or unpaid analytic sign is asserted here.  The current smooth
signed-pole constructor is still pointwise in t on the pole-localization side;
a common high-t witness radius has not been proved merely by renaming that
quantifier.

A strict one-scale FAIL exposes the already-built independent log2/log3
two-scale source.  Route B remains the independent signed-fifth theorem:
eventual nonnegativity of
`signedFifthCorrelationGapAt = Credit - Debt + OuterBudget - 3 eps`.
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
