import Synthesis.RiemannSelectedSignedFifthCorrelationCut

/-!
# Signed-fifth direct gap audit

Route B should not be forced to estimate credit and debt separately if their
cancellation is the useful analytic object.  The finite correlation owner
already proves

  physicalCapInterior = Credit - Debt.

This file substitutes that identity into the exact max-cut scalar
`signedFifthCorrelationGapAt`.  Consequently the only Route-B theorem is the
direct eventual sign of

  physicalCapInterior + OuterBudget - 3 eps.

No new representation or analytic hypothesis is introduced.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real

/-- Exact direct form of the Route-B gap at every sufficiently large finite
cutoff. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationGapAt_eq_cap
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ)) :
    W.signedFifthCorrelationGapAt rho EV eps n
      =
    W.signedFifthPhysicalCapInteriorAt n
      + W.outerVerticalAbsoluteBudget rho EV
      - 3*eps := by
  unfold QuarticFourSignedPolePair.signedFifthCorrelationGapAt
  rw [W.signedFifthPhysicalCapInteriorAt_eq_credit_sub_debt ht n hn]
  ring

/-- Pointwise Route-B PASS can therefore be tested directly on the signed cap,
without splitting into positive and negative parts. -/
theorem QuarticFourSignedPolePair.signedFifthCorrelationGapAt_nonneg_iff_cap
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ)
    (hn : quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ)) :
    0 <= W.signedFifthCorrelationGapAt rho EV eps n
      ↔
    -W.outerVerticalAbsoluteBudget rho EV + 3*eps
      <= W.signedFifthPhysicalCapInteriorAt n := by
  rw [W.signedFifthCorrelationGapAt_eq_cap ht rho n hn]
  constructor <;> intro h <;> linarith

/-- Direct eventual cap inequality is sufficient for the terminal Route-B
producer. -/
theorem QuarticFourSignedPolePair.signedFifthInteriorTarget_of_eventual_cap_gap
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hlarge :
      ∀ᶠ n : ℕ in atTop,
        quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hcap :
      ∀ᶠ n : ℕ in atTop,
        -W.outerVerticalAbsoluteBudget rho EV + 3*eps
          <= W.signedFifthPhysicalCapInteriorAt n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  filter_upwards [hlarge,hcap] with n hn hc
  exact hc

end Synthesis
