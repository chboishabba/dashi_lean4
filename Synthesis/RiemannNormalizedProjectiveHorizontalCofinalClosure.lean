import Synthesis.RiemannNormalizedProjectiveHorizontalArbitraryCutoff

/-!
# Cofinal closure of the signed horizontal reduction

The arbitrary-cutoff theorem has reduced the literal off-ordinate horizontal
tsum to

  finiteUnfavourableMiddle(J) + vanishingFar(J).

This file closes the limiting step exactly.  No absolute value is put back on
the finite middle.

If the finite unfavourable middle is nonpositive for all sufficiently large
cutoffs, then the complete literal horizontal tsum is nonpositive.  Thus the
remaining horizontal obstruction is genuinely finite/local: one must prove a
signed theorem for the cofinal finite middle carriers, not improve the already
vanishing far tail.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

/--
Cofinal finite-middle compiler.

The theorem is deliberately stated with an eventual hypothesis rather than
"for every J": only a cofinal family of finite carriers is needed.
-/
theorem offOrdProjectiveHorizontal_tsum_nonpos_of_eventually_refinedMiddle_nonpos
    {t : ℝ} (ht : 18 ≤ t)
    (hmiddle :
      ∀ᶠ J : ℕ in atTop,
        (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
          normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) ≤ 0) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) ≤ 0 := by
  obtain ⟨A, K, hA1, hK0, hbound, hfar⟩ :=
    exists_offOrdProjectiveHorizontal_cutoff_reduction ht
  apply le_of_tendsto hfar
  filter_upwards [hmiddle, eventually_ge_atTop (1 : ℕ)] with J hmid hJ
  have hb := hbound J hJ
  linarith

/-- A convenient pointwise version for callers which prove every cutoff. -/
theorem offOrdProjectiveHorizontal_tsum_nonpos_of_refinedMiddle_nonpos
    {t : ℝ} (ht : 18 ≤ t)
    (hmiddle :
      ∀ J : ℕ, 1 ≤ J →
        (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
          normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) ≤ 0) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) ≤ 0 := by
  apply offOrdProjectiveHorizontal_tsum_nonpos_of_eventually_refinedMiddle_nonpos ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with J hJ
  exact hmiddle J hJ

end Synthesis
