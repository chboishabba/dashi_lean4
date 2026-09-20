import Mathlib
import RequestProject.NavierStokes.WholeSpaceL1Tail

/-!
# Whole-space Navier–Stokes L² interaction integrability

For a fixed output frequency ξ, the quadratic interaction integrand

  η ↦ L (f η) (g (ξ - η))

is Bochner-integrable whenever both Fourier legs are L² and L is a continuous
bilinear map.  This is the literal whole-space convolution integrability leaf
needed by the independent R³ A lane.

The proof uses Mathlib's conjugate-exponent convolution theorem with p=q=2.
It also immediately gives vanishing L¹ mass of the interaction outside
expanding Euclidean balls.
-/

open Filter MeasureTheory
open scoped Topology

namespace RequestProject.NavierStokes

section L2Interaction

variable {E E' F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed-output bilinear Fourier interaction is L¹ in the interaction variable. -/
theorem integrable_fixedOutput_bilinear_of_memLp_two
    (L : E →L[ℝ] E' →L[ℝ] F)
    (f : R3 → E)
    (g : R3 → E')
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (ξ : R3) :
    Integrable (fun η : R3 => L (f η) (g (ξ - η))) volume := by
  have hconv : ConvolutionExists f g L volume :=
    ConvolutionExists.of_memLp_memLp L hf hg
  exact (hconv ξ).integrable

/-- The physical L¹ tail of the fixed-output bilinear interaction vanishes. -/
theorem fixedOutput_bilinear_normTail_tendsto_zero
    (L : E →L[ℝ] E' →L[ℝ] F)
    (f : R3 → E)
    (g : R3 → E')
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (ξ : R3) :
    Tendsto
      (fun n : ℕ =>
        ∫ η : R3 in (Metric.closedBall (0 : R3) n)ᶜ,
          ‖L (f η) (g (ξ - η))‖)
      atTop
      (nhds 0) :=
  normIntegral_compl_closedBall_tendsto_zero
    (fun η : R3 => L (f η) (g (ξ - η)))
    (integrable_fixedOutput_bilinear_of_memLp_two L f g hf hg ξ)

end L2Interaction

end RequestProject.NavierStokes
