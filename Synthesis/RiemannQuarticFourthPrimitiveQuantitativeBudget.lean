import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal

/-!
# Quantitative fourth-primitive RH budget

The fourfold integration-by-parts identity is an identity, not an r^-4 bound.
This owner calculates the exact terminal budget that any unconditional primitive
estimate must satisfy, with the physical horizontal and literal-local
corrections retained on the SAME witness.

Let r=t/16, eta=the canonical radius, and

  I_n = normalizedOuterPairedAbelAt n
      = integral_[eta,n/r] C'_W(q) r^4 D(t-rq,t+rq) dq.

The finite terminal scalar is -I_n/2 + H6 - L6.  Thus an ABSOLUTE
bound |I_n| <= E_n + B*K entails the desired terminal cut only when

  E_n + B*K < 2 * (r^6 * terminalMargin - H6 + L6).

No estimate for B is assumed/proved by these arithmetic identities.  The
original signed condition can be weaker and remains the preferred alternative
if this absolute margin is negative or too small.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : ℝ :=
  2 * (
    (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
      - W.quarticScaleHorizontalRemainder
      + W.quarticScaleCanonicalLocalCorrection
  )

theorem QuarticFourSignedPolePair.outerVerticalAbsoluteBudget_eq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) :
    W.outerVerticalAbsoluteBudget rho EV
      =
    2 * (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
      - 2 * W.quarticScaleHorizontalRemainder
      + 2 * W.quarticScaleCanonicalLocalCorrection := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  ring

theorem QuarticFourSignedPolePair.outerTerminal_lt_of_absoluteAbel_budget
    {t EV E n : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (k : ℕ)
    (hAbel : |W.normalizedOuterPairedAbelAt k| <= E)
    (hBudget : E < W.outerVerticalAbsoluteBudget rho EV) :
    W.quarticScaleOuterTerminalAt k
      < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
    QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget at *
  have hlower := (abs_le.mp hAbel).1
  linarith

theorem QuarticFourSignedPolePair.absolutePrimitiveCost_strictBudget
    {t BP K boundary : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hBudget :
      boundary + BP*K < W.outerVerticalAbsoluteBudget rho EV) :
    (1/2 : ℝ) * (boundary + BP*K)
      + W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection
      < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.outerVerticalAbsoluteBudget at hBudget
  linarith

/-- The maximal admissible *product* is well-defined without division by
an L1 mass that might vanish. The strict inequality is the actual condition,
not a standalone B4 estimate. -/
def QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (BP K : ℝ) : Prop :=
  BP*K < W.outerVerticalAbsoluteBudget rho EV

theorem QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct_iff
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) :
    W.absolutePrimitiveAdmissibleProduct rho EV BP K
      ↔
    (1/2 : ℝ) * BP*K
      + W.quarticScaleHorizontalRemainder
      - W.quarticScaleCanonicalLocalCorrection
        < (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
    QuarticFourSignedPolePair.outerVerticalAbsoluteBudget
  constructor <;> intro h <;> linarith

/-- When the fifth-derivative mass is strictly positive, the admissible
coefficient is exactly the budget divided by that SAME kernel norm. -/
theorem QuarticFourSignedPolePair.absolutePrimitiveCoefficient_lt_iff
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hK : 0 < K) :
    W.absolutePrimitiveAdmissibleProduct rho EV BP K
      ↔ BP < W.outerVerticalAbsoluteBudget rho EV / K := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
  exact (lt_div_iff₀ hK).symm

/-- A bound that is already too large at the scalar budget cannot be rescued
by simply recasting it as a polynomial-growth primitive interface. -/
theorem QuarticFourSignedPolePair.absoluteBudget_failfast
    {t BP K : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ)
    (hTooLarge : W.outerVerticalAbsoluteBudget rho EV <= BP*K) :
    ¬ W.absolutePrimitiveAdmissibleProduct rho EV BP K := by
  unfold QuarticFourSignedPolePair.absolutePrimitiveAdmissibleProduct
  exact not_lt.mpr hTooLarge

end Synthesis
