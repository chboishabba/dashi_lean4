import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalizationPaid
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMidStripMesh
import Synthesis.RiemannSelectedPrimeSensitiveTwoScalePromotion

/-!
# RH max-cut frontier after analytic compression

This is the import boundary for the live analytic frontier.

The branch is now best managed as three analytic routes sharing the same
terminal consumer.

## Route A1: inverse-square / three-tap

One-scale resonance has been compressed past the abstract reflection tail:

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
* the formerly pointwise-in-t pole-weight continuity has been sharpened to the
  uniform elementary estimate
  `|w_t,c(u)-w_t,c(v)| <= 19*cosh(1)*|u-v|` on [-6,6] for t>=200, |c|<=2;
* the normalized four-window determinant quantifier swap is isolated as the
  finite compiler target `UniformQuarticFourPoleDeterminantCompilerTarget`, and
  that target already compiles to one fixed-width high-t signed-pole core;
* `ThreeTapUniformCurvatureBound` names the remaining compact-alpha curvature
  theorem on the actual transformed projective profile;
* the subtraction-defined actual adverse far remainder is exactly a
  complementary subtype tsum and is bounded by Ccurv times the literal
  inverse-square zero tail `threeTapInverseSquareZeroTailAfter`;
* the arbitrary-endpoint RvM discrepancy has been converted into a literal
  count bound
  `N(A,B) <= C (B-A+1) log(B+4)` for `5 <= A < B`;
* `zetaWindowInverseSquareMass_le_count_div_sq` pays the exact carrier weld
  from a separated literal zero window to `N(A,B)/d^2`;
* positive-height right/left shell bounds are source-written, and the existing
  unconditional all-real local zero count gives unit-window inverse-square
  bounds on both sides of `t`, including negative ordinates, without changing
  the `Ncount` carrier or invoking zero reflection;
* the half-open right-shell endpoint issue at `gamma=3t/2` is now absorbed by
  the boundary-safe first source window `(3t/2-1,2t]`, whose entire mass has an
  RvM inverse-square bound with separation `t/2-1`; no separate boundary fibre
  or new carrier is introduced;
* dyadic half-height shell geometry is source-written and its numerical series
  is summed exactly:
    `sum_k ((log t + 1) + k) 2^-k / t = (2 log t + 4)/t`;
* `ThreeTapInverseSquareShellPartitionBound` is the exact remaining carrier
  surface, and its compiler proves the normalized Route-A tail bound with only
  a factor-four loss.  Thus no infinite-series algebra remains behind that cut;
* `threeTapRouteAAdverseBudget` combines the explicit finite budget and this
  inverse-square far budget, while
  `exists_threeTapRouteAAsymptoticBalancePass_constants` compiles the strict
  comparison against the gamma+pole-minus-slack floor directly to paid-cost
  negativity;
* the compensation floor is exactly
  `-(Gamma+Pole) - LocalSlack/2`;
* after a near-line PASS, the existing finite net/Lipschitz compiler closes the
  compact mid-strip once certified node margins and a derivative bound exist.

The live A1 leaves are therefore:

1. finish the literal complementary-zero carrier summation into the already-
   paid left/right source windows; the first-right-boundary defect is no longer
   part of this leaf;
2. finish fixed-width determinant transport / witness control and prove uniform
   compact-alpha curvature;
3. prove translated gamma+pole gain versus local slack strongly enough that

     finite + Ccurv*inverseSquareTail < G - S/2.

## Route A2: V4/H4/G3

The polarity problem described by the pointwise identity

  P_G3 = positive_scale * (a^4 - fourthAngular)

has now been cut past the original fail-fast wall.  The source owns:

* `literalLocalHorizontalFourthCorrectionAt_lower`, an unconditional lower H4
  envelope from the critical strip and local ordinate radius;
* `literalLocalVerticalFourthDiscrepancy_ge_neg_rvm`, which uses the absolute V4
  theorem and the nonnegative left-endpoint atom;
* `literalLocalCenteredFourthAngularAt_lower`, the correct-polarity lower bound
  on the same finite fourth-angular carrier;
* `literalLocalFourthPhaseMomentAt_ge_corrected_scalar`, which adds the mu
  reference contribution on the exact local phase carrier;
* `literalOffOrdExactAt_le_postSixthV4H4AbsorbBudgetAt`, which therefore gives
  the required same-object UPPER bound on the off-ordinate source.

So A2 is no longer blocked on orientation.  Its live theorem is the strict
scalar ABSORB comparison of the exposed post-sixth V4/H4 budget against the
common compensation/terminal threshold.  The signed sixth and FarExact terms
remain signed; no absolute replacement is silently inserted.

## Route B: signed fifth

The independent signed-fifth route now exposes exactly the roadmap scalar

  signedFifthCorrelationGapAt
    = Credit_n - Debt_n + OuterBudget - 3 eps.

`eventual gap >= 0` compiles directly to the existing
`SignedFifthInteriorTarget`.  The only unpaid Route-B research theorem is the
eventual nonnegativity of that exact scalar.

No RH theorem or unpaid analytic sign is asserted here.  In particular, there
is still no exact-head kernel receipt for this branch.  Mid-strip certification
stays downstream of a genuine near-line PASS, and J4 stays quarantined until an
actual J2=0 source exists.
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