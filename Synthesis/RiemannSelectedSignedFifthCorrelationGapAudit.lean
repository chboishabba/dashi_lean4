import Synthesis.RiemannSelectedSignedFifthCorrelationCut

/-!
# Signed-fifth direct gap audit

Route B should not be forced to estimate credit and debt separately if their
cancellation is the useful analytic object.  The finite correlation owner
already proves

  physicalCapInterior = Credit - Debt.

This file substitutes that identity into the exact max-cut scalar
`signedFifthCorrelationGapAt`.  Consequently the genuinely signed Route-B
producer is the direct eventual sign of

  physicalCapInterior + OuterBudget - 3 eps.

The finite-cutoff ownership condition is not an analytic premise: for fixed
`t`, natural cutoffs tend to infinity.  It is discharged below once and for all.
Boundary decay and outer-terminal convergence remain independent analytic
obligations.
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

/-- The physical lower cutoff is automatically owned eventually.  This is
Archimedean bookkeeping, not part of the Route-B analytic frontier. -/
theorem eventually_quarticSignedPoleCanonicalPhysicalHalfWidth_le_natCast
    (t : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ) := by
  obtain ⟨N,hN⟩ :=
    exists_nat_gt (quarticSignedPoleCanonicalPhysicalHalfWidth t)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) <= (n : ℝ) := by
    exact_mod_cast hn
  exact hN.le.trans hcast

/-- Direct eventual cap inequality is sufficient for the terminal Route-B
interior producer; no separate large-cutoff hypothesis is required. -/
theorem QuarticFourSignedPolePair.signedFifthInteriorTarget_of_eventual_cap_gap
    {t EV eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hcap :
      ∀ᶠ n : ℕ in atTop,
        -W.outerVerticalAbsoluteBudget rho EV + 3*eps
          <= W.signedFifthPhysicalCapInteriorAt n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  exact hcap

/-- Eventual direct gap nonnegativity gives the same interior target with the
large-cutoff ownership supplied mechanically. -/
theorem QuarticFourSignedPolePair.signedFifthInteriorTarget_of_eventual_direct_gap
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        0 <= W.signedFifthCorrelationGapAt rho EV eps n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  have hlarge :=
    eventually_quarticSignedPoleCanonicalPhysicalHalfWidth_le_natCast t
  filter_upwards [hlarge,hgap] with n hn hg
  exact (W.signedFifthCorrelationGapAt_nonneg_iff_cap
    ht rho n hn).mp hg

/-- Honest Route-B compiler after removing the purely Archimedean cutoff
premise.  Exactly three analytic producers remain visible: boundary decay,
direct signed-gap nonnegativity, and outer-terminal convergence. -/
theorem QuarticFourSignedPolePair.signedFifthAnalyticInput_of_three_producers
    {t EV eps : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (heps : 0 < eps)
    (hboundary :
      ∀ᶠ n : ℕ in atTop,
        |W.signedFifthCapUpperBoundaryAt n| <= eps)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        0 <= W.signedFifthCorrelationGapAt rho EV eps n)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.SignedFifthAnalyticInput rho EV eps := by
  exact W.signedFifthAnalyticInput_of_interiorTarget
    rho heps hboundary
    (W.signedFifthInteriorTarget_of_eventual_direct_gap ht rho hgap)
    hlim

end Synthesis
