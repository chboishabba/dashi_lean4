import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalizationPaid
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
* the arbitrary-endpoint RvM discrepancy has now been converted into a literal
  count bound
  `N(A,B) <= C (B-A+1) log(B+4)` for `5 <= A < B`;
* `zetaWindowInverseSquareMass_le_count_div_sq` now pays the exact carrier weld
  from a separated literal zero window to `N(A,B)/d^2`;
* positive-height right/left shell bounds are source-written, and the existing
  unconditional all-real local zero count now gives unit-window inverse-square
  bounds on both sides of `t`, including negative ordinates, without changing
  the `Ncount` carrier or invoking zero reflection;
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

1. finish the finite normalized-bump/determinant compiler fed by the already-
   proved uniform pole-weight Lipschitz estimate, then bound the compact-alpha
   C2 curvature of the resulting fixed-width transformed witness;
2. partition the exact complementary zero carrier into the source-written
   literal unit/dyadic windows and sum their explicit inverse-square budgets to
   prove
   `threeTapInverseSquareZeroTailAfter t (t/2) = O(log t/t)`;
3. bound the translated gamma+pole channel above by a negative gain and the
   already-paid local slack above strongly enough that

     finite + Ccurv*inverseSquareTail < G - S/2.

No RH theorem or unpaid analytic sign is asserted here.  In particular, the
uniform pole-weight modulus is paid but the final determinant compiler remains
fail-closed until kernel replay verifies that finite bookkeeping, and the
inverse-square unit/shell estimates are paid but their countable tail summation
is not yet claimed.

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
