import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTerminalTest
import Synthesis.RiemannQuarticFourthPrimitiveQuantitativeBudget

/-!
# Signed fifth-cap route to the canonical terminal scalar

The signed RvM/fourfold-IBP route already compiles an eventual signed fifth-cap
lower bound to PostSixthCanonicalSignedHighCut.  This file removes the last
presentation mismatch: Route B now concludes positivity of exactly the same
canonicalTerminalMargin used by the three-tap deformation route.

No new analytic estimate is introduced.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real

theorem QuarticFourSignedPolePair.signedFifthCap_eventual_compiles_terminalMargin
    {t EV eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (heps : 0 < eps)
    (hboundary :
      ∀ᶠ n : ℕ in atTop,
        |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hsigned :
      ∀ᶠ n : ℕ in atTop,
        -W.outerVerticalAbsoluteBudget rho EV + 3*eps
          <= W.signedFifthPhysicalCapInteriorAt n)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    0 < W.canonicalTerminalMargin rho EV := by
  apply (W.canonicalTerminalMargin_pos_iff_highCut ht rho).2
  exact W.signedFifthCap_eventual_compiles_highCut
    (by linarith : 0 < t) rho heps hboundary hsigned hlim

/-- The two active RH routes now have one common terminal consumer.
This definition is only a naming surface for proof search / dependency audit. -/
def QuarticFourSignedPolePair.CanonicalTerminalPositive
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : Prop :=
  0 < W.canonicalTerminalMargin rho EV

theorem QuarticFourSignedPolePair.canonicalTerminalPositive_iff_highCut
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.CanonicalTerminalPositive rho EV
      ↔ W.PostSixthCanonicalSignedHighCut rho EV := by
  exact W.canonicalTerminalMargin_pos_iff_highCut ht rho

end Synthesis
