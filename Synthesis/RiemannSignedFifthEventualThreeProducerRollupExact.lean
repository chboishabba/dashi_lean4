import Synthesis.RiemannSelectedSignedFifthCorrelationGapAudit

/-!
# Clay RH Route B — no unnecessary large-cutoff hypothesis

Original owner: RiemannSelectedSignedFifthCorrelationGapAudit, PR #50.
The current Clay rollup retains its existing theorem signature. This
follow-on pays the elementary Archimedean cutoff premise directly and
exposes exactly three *physical* analytic producers:
  eventual signed cap gap, upper-boundary decay, outer-terminal limit.
This is a proof of the conditional source compiler, NOT the unknown
physical eventual sign or RH.

Source attribution: classical Archimedean bound and finite original
Riemann signed-fifth zero-cap algebra; DASHI source implementation.
Pinned Lean/mathlib kernel check and transitive axiom audit pending.
-/

noncomputable section
namespace Synthesis
open MeasureTheory Set Filter
open scoped Real

theorem signedFifthRollupCutoffEventuallyOwned (t : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      quarticSignedPoleCanonicalPhysicalHalfWidth t ≤ (n : ℝ) := by
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (quarticSignedPoleCanonicalPhysicalHalfWidth t)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact hN.le.trans hc

theorem QuarticFourSignedPolePair.signedFifthRollupInterior_of_eventualGap
    {t EV eps : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) (rho : Zeros)
    (hgap : ∀ᶠ n : ℕ in atTop,
      0 ≤ W.signedFifthCorrelationGapAt rho EV eps n) :
    W.SignedFifthInteriorTarget rho EV eps := by
  have hlarge := signedFifthRollupCutoffEventuallyOwned t
  filter_upwards [hlarge,hgap] with n hn hg
  exact (W.signedFifthCorrelationGapAt_nonneg_iff_cap
    ht rho n hn).mp hg

theorem QuarticFourSignedPolePair.signedFifthRollupAnalyticInput_of_three
    {t EV eps : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) (rho : Zeros)
    (heps : 0 < eps)
    (hboundary : ∀ᶠ n : ℕ in atTop,
      |W.signedFifthCapUpperBoundaryAt n| ≤ eps)
    (hgap : ∀ᶠ n : ℕ in atTop,
      0 ≤ W.signedFifthCorrelationGapAt rho EV eps n)
    (hlim : Tendsto W.quarticScaleOuterTerminalAt atTop
      (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.SignedFifthAnalyticInput rho EV eps := by
  exact W.signedFifthAnalyticInput_of_interiorTarget
    rho heps hboundary
    (W.signedFifthRollupInterior_of_eventualGap ht rho hgap)
    hlim

end Synthesis
