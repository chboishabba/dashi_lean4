import Synthesis.RiemannSelectedSignedFifthTerminalBridge

/-!
# Signed-fifth max-cut analytic input

The signed-fifth route is intentionally independent of the three-tap deformation.
Its terminal compiler already exists.  This file packages the exact outstanding
analytic data into one named proposition so proof search has a single target.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real

/-- Complete analytic input required by the existing signed-fifth terminal
compiler for a fixed witness, zero, outer budget and epsilon. -/
def QuarticFourSignedPolePair.SignedFifthAnalyticInput
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV eps : ℝ) : Prop :=
  0 < eps
  ∧
  (∀ᶠ n : ℕ in atTop,
    |W.signedFifthCapUpperBoundaryAt n| <= eps)
  ∧
  (∀ᶠ n : ℕ in atTop,
    -W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthPhysicalCapInteriorAt n)
  ∧
  Tendsto W.quarticScaleOuterTerminalAt atTop
    (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))

/-- The named signed-fifth analytic target is exactly sufficient for the common
canonical terminal consumer. -/
theorem QuarticFourSignedPolePair.signedFifthAnalyticInput_compiles_terminalPositive
    {t EV eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (h : W.SignedFifthAnalyticInput rho EV eps) :
    W.CanonicalTerminalPositive rho EV := by
  rcases h with ⟨heps, hboundary, hsigned, hlim⟩
  exact W.signedFifthCap_eventual_compiles_terminalMargin
    ht rho heps hboundary hsigned hlim

/-- Expanded theorem with the roadmap's interior lower bound visible at the
call site. -/
theorem QuarticFourSignedPolePair.signedFifthMaxCut
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
    W.CanonicalTerminalPositive rho EV := by
  exact W.signedFifthAnalyticInput_compiles_terminalPositive ht rho
    ⟨heps, hboundary, hsigned, hlim⟩

/-- The signed interior estimate is the only genuinely signed inequality inside
the packaged input; boundary decay and the existing limit remain independent
auxiliary obligations. -/
def QuarticFourSignedPolePair.SignedFifthInteriorTarget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV eps : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    -W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthPhysicalCapInteriorAt n

theorem QuarticFourSignedPolePair.signedFifthAnalyticInput_of_interiorTarget
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (heps : 0 < eps)
    (hboundary :
      ∀ᶠ n : ℕ in atTop,
        |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hinterior : W.SignedFifthInteriorTarget rho EV eps)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.SignedFifthAnalyticInput rho EV eps := by
  exact ⟨heps, hboundary, hinterior, hlim⟩

end Synthesis
