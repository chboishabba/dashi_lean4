import Synthesis.RiemannRadiusZeroPoleCorrection
import Zeta23Bridge.LiteralWeilEvenChannelTaper

/-!
# Radius-zero pole sign for the canonical positive taper

The strengthened positive taper constructor now exports both

  poleEvenResp g t r = 0

at the selected pole-killing radius and

  0 < poleEvenResp g t 0

at radius zero.

Therefore the final even-cone pole coordinate at radius zero is strictly
negative:

  ell(Q_pole(0)) = -4 poleEvenResp(g,t,0) < 0.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem exists_canonical_taper_with_negative_radiusZero_pole
    {t : ℝ} (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ),
      ContDiff ℝ 2 g
      ∧ HasCompactSupport g
      ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r
      ∧ (∀ u, 0 ≤ g u)
      ∧ (∀ u, g u ≠ 0 → 2 * r * |u| < Real.pi / 2)
      ∧ poleEvenResp g t r = 0
      ∧ 0 < poleEvenResp g t 0
      ∧ evenConeFunctional (poleVec (sampleFam g t 0)) < 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ (∀ u, g u ≠ 0 → |u| < 9 * Real.pi / (4 * |t|)) := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hwin, -, hpole, hpole0, hA, hsupp⟩ :=
    exists_positive_taper_poleEven_zero_with_radiusZero_sign ht
  refine ⟨g, r, hgs, hgc, heven, hr, hnn, hwin, hpole, hpole0, ?_, hA, hsupp⟩
  exact radiusZero_pole_correction_negative_of_unweighted_positive
    hgs.continuous hgc heven hpole0

end Synthesis
