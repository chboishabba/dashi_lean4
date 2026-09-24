import Mathlib
import RequestProject.NavierStokes.WholeSpaceL2InteractionIntegrability

/-!
# Whole-space bounded-weight interaction integrability

The A lane's high-frequency envelope carries an inverse-power multiplier.  Once
that multiplier is restricted to the physical high region it is uniformly
bounded, so no new convolution theorem is required: the stronger unweighted
L²×L² -> L¹ fixed-output theorem already proved in this project survives any
measurable bounded scalar multiplier.

This file isolates that reusable analytic step.  A concrete inverse-sixth
multiplier therefore only has to discharge measurability and its elementary
high-region bound.
-/

open MeasureTheory

namespace RequestProject.NavierStokes

section WeightedInteraction

variable {E E' F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Any measurable uniformly bounded scalar multiplier preserves the physical
fixed-output L¹ interaction supplied by the L²×L² convolution theorem. -/
theorem integrable_fixedOutput_bilinear_weighted_of_bound
    (L : E →L[ℝ] E' →L[ℝ] F)
    (f : R3 → E)
    (g : R3 → E')
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (ξ : R3)
    (w : R3 → ℝ)
    (hw_meas : AEStronglyMeasurable w volume)
    (C : ℝ)
    (hw_bound : ∀ᵐ η ∂volume, ‖w η‖ ≤ C) :
    Integrable
      (fun η : R3 => w η • L (f η) (g (ξ - η)))
      volume := by
  exact
    (integrable_fixedOutput_bilinear_of_memLp_two L f g hf hg ξ).smul_of_top_right
      C hw_meas hw_bound

/-- Unit-bounded specialization, matching the usual high-frequency
inverse-power envelope after the high-region cutoff. -/
theorem integrable_fixedOutput_bilinear_weighted_unit
    (L : E →L[ℝ] E' →L[ℝ] F)
    (f : R3 → E)
    (g : R3 → E')
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (ξ : R3)
    (w : R3 → ℝ)
    (hw_meas : AEStronglyMeasurable w volume)
    (hw_bound : ∀ᵐ η ∂volume, ‖w η‖ ≤ (1 : ℝ)) :
    Integrable
      (fun η : R3 => w η • L (f η) (g (ξ - η)))
      volume :=
  integrable_fixedOutput_bilinear_weighted_of_bound
    L f g hf hg ξ w hw_meas 1 hw_bound

end WeightedInteraction

end RequestProject.NavierStokes
