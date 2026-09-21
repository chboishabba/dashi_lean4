import Synthesis.RiemannGammaCenteredKernelBridge
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact-support wrapper for the literal centered Gamma kernel identity

The underlying Gamma theorem only needs a support-radius witness in order to
invoke the existing Gamma integrability API.  Any compactly supported real taper
has such a witness.

This file removes that bookkeeping parameter:

  gammaResp (h_r) t 0
    = - integral h_r(u) cos(tu) K(|u|)

for every even compactly supported C^2 taper g.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Real

namespace Synthesis

theorem exists_support_radius_of_hasCompactSupport
    {g : ℝ → ℝ} (hcompact : HasCompactSupport g) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ u, g u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨Λ, hΛpos, hsub⟩ :=
    hcompact.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  refine ⟨Λ, hΛpos, ?_⟩
  intro u hu
  have husupp : u ∈ Function.support g := by
    exact hu
  have hutsu : u ∈ tsupport g :=
    subset_tsupport g husupp
  have huball := hsub hutsu
  simpa [Metric.mem_closedBall, Real.dist_eq] using huball

theorem gammaResp_centered_archKernel_exact_compact
    {g : ℝ → ℝ}
    (hgC2 : ContDiff ℝ 2 g)
    (hcompact : HasCompactSupport g)
    (heven : ∀ u, g (-u)=g u)
    (r t : ℝ) :
    gammaResp (gammaCenteredTaper g r) t 0
      =
    - ∫ u : ℝ,
      gammaCenteredTaper g r u
        * Real.cos (t*u) * gammaArchKernel |u| := by
  obtain ⟨Λ, hΛ, hsupp⟩ :=
    exists_support_radius_of_hasCompactSupport hcompact
  exact gammaResp_centered_archKernel_exact
    hgC2 hcompact heven hsupp hΛ.le r t

end Synthesis
