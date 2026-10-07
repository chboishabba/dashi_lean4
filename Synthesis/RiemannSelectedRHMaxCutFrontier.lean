import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalizationPaid
import Synthesis.RiemannPostMergeAnalyticMaxCut
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMidStripMesh
import Synthesis.RiemannSelectedPrimeSensitiveTwoScalePromotion

/-!
# RH max-cut frontier after post-merge analytic compression

This is the import boundary for the live analytic frontier.

The merged architecture is frozen.  The programme is now three concrete
analytic routes sharing the same terminal consumer; no RH-equivalent terminal
certificate is counted as producer progress.

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
* the normalized four-window determinant quantifier swap is isolated as the
  finite compiler target `UniformQuarticFourPoleDeterminantCompilerTarget`, and
  that target already compiles to one fixed-width high-t signed-pole core;
* `ThreeTapUniformCurvatureBound` names the remaining compact-alpha curvature
  theorem on the actual transformed projective profile;
* the subtraction-defined actual adverse far remainder is exactly a
  complementary subtype tsum and is bounded by Ccurv times the literal
  inverse-square zero tail `threeTapInverseSquareZeroTailAfter`;
* arbitrary-endpoint and all-real local zero-count bounds own the literal right,
  positive-left, and negative-ordinate shell/window estimates;
* `threeTapHalfHeightComplement_left_or_right` proves the exact complement has
  only the two ordinate charts `gamma<=t/2` and `3t/2<=gamma`;
* the right boundary `gamma=3t/2` is owned by the first boundary-safe source
  window `(3t/2-1,2t]`, and the left first shell owns `gamma=t/2`;
* dyadic shell geometry is source-written and its numerical series is summed
  exactly:
    `sum_k ((log t + 1) + k) 2^-k / t = (2 log t + 4)/t`;
* `ThreeTapInverseSquareShellPartitionBound` is therefore the exact remaining
  carrier surface; its compiler pays all subsequent infinite-series algebra;
* `threeTapRouteAAdverseBudget` combines finite and inverse-square far budgets,
  and `exists_threeTapRouteAAsymptoticBalancePass_constants` compiles the strict
  comparison against the gamma+pole-minus-slack floor directly to paid-cost
  negativity.

The live A1 leaves are exactly:

1. assign the two exact ordinate charts to the already-paid countable
   shell/window family and sum the literal complementary-zero carrier;
2. finish fixed-width determinant transport / witness control and prove uniform
   compact-alpha curvature;
3. prove translated gamma+pole gain versus local slack strongly enough that

     finite + Ccurv*inverseSquareTail < G - S/2.

No further boundary geometry is owed.

## Route A2: V4/H4/G3

The polarity and dominant selected-sixth issues are paid.  The post-merge audit
also traces the target scalar to primitives:

  compensationTargetThreshold(W,rho)
    = 4*combinedZeroHeightDefect(W,rho)
      + integral signedOrdinateTest(W)*mu.

Thus the A2 target does not hide an abstract high-ordinate contradiction
hypothesis.

The source owns:

* the correct-polarity finite fourth-angular upper compiler;
* the selected witness certificate `-(3/20)*pi^6 <= M6_signed < 0`;
* `quarticSignedPole_terminal_M6_cap_pays_dominant_balance`;
* `postSixthTerminalLocalM6Budget_eq_debt_sub_muGain`;
* `quarticSignedPoleMuLowerEnvelope_canonical_pos` for t>=200;
* the exact strict scalar equivalence

    localPositiveDebt + FarExact
      < compensationTargetThreshold + localMuGain;

* the post-merge four-coordinate identity

    localPositiveDebt
      = verticalDebt + countDebt + sixthDebt + eighthDebt;

* `postSixthTerminalDominantHeadroom_pos`, showing every strength-floor witness
  has strict headroom after the selected dominant M6 allowance is removed.

FarExact remains signed.  Nothing above proves the remaining strict scalar.
The next quantitative theorem must bound the four explicit debt coordinates and
signed FarExact against the explicit target plus positive mu gain.  If the
normalized coefficients have the wrong sign, A2 should be retired by a no-go
theorem rather than hidden behind a stronger certificate.

## Route B: signed fifth

The exact signed scalar is

  signedFifthCorrelationGapAt
    = Credit_n - Debt_n + OuterBudget - 3 eps
    = signedFifthPhysicalCapInteriorAt n + OuterBudget - 3 eps

at sufficiently large finite cutoff.  Therefore the only genuinely signed
correlation theorem is eventual `gap >= 0`; separate credit/debt estimates are
optional.

However, `SignedFifthAnalyticInput` also requires two independent auxiliary
limits which must not be silently counted as paid:

* eventual upper-boundary decay
    `|signedFifthCapUpperBoundaryAt n| <= eps`;
* convergence of `quarticScaleOuterTerminalAt` to the canonical signed high
  residual.

`signedFifthAnalyticInput_of_eventual_direct_gap` now exposes the exact honest
compiler: positive eps + boundary decay + large-cutoff ownership + eventual
signed gap + outer convergence imply the existing Route-B analytic input.
Until boundary decay and outer convergence are independently discharged for the
selected witness, eventual `G_n >= 0` is the final signed inequality but not the
entire Route-B closure.

## Downstream

Mid-strip certification remains downstream of a genuine near-line PASS.  J4
remains quarantined until an actual J2=0 source exists.  High-zero RH and global
RH remain open.

## Trust boundary

The post-merge additions are source-written / statically inspectable unless an
exact-head workflow supplies a kernel receipt.  This file asserts neither RH
nor any unpaid analytic sign.
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
