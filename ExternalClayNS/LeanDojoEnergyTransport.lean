import LeanDojoSolutionTransport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact whole-space energy transport

LeanDojo writes the kinetic-energy density as the sum of squared Euclidean
coordinates.  The comparator writes the same density as `‖u‖^2` and packages
square-integrability through `MemLp`.  On `EuclideanSpace ℝ (Fin 3)` these are
literally the same scalar function.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

/-- Coordinate-square energy is exactly Euclidean norm-square energy. -/
theorem euclidean_sum_sq_eq_norm_sq (v : Space3) :
    (∑ i : Fin 3, (v i) ^ 2) = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq v]
  simp [PiLp.inner_apply, RCLike.inner_apply, pow_two]

/-- LeanDojo's energy integral is the comparator's norm-square integral. -/
theorem energyIntegral_eq_integral_norm_sq
    (u : VelocityField 3) (t : ℝ) :
    energy_integral u t =
      ∫ x : Space3, ‖u (spacetime_point t x)‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards with x
  exact euclidean_sum_sq_eq_norm_sq (u (spacetime_point t x))

/-- A fixed nonnegative-time slice of a LeanDojo smooth solution is smooth,
therefore strongly measurable. -/
theorem leanDojoVelocitySlice_aestronglyMeasurable
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable
      (fun x : Space3 => sol.velocity (spacetime_point t x)) := by
  have hsmooth : ContDiff ℝ ∞
      (fun x : Space3 => sol.velocity (spacetime_point t x)) := by
    apply sol.velocity_smooth.comp_contDiff
    · fun_prop
    · intro x
      simpa [global_spacetime_domain, spacetime_point] using ht
  exact hsmooth.continuous.aestronglyMeasurable

/-- LeanDojo finite energy supplies actual vector-valued `L²` membership on
all nonnegative-time slices. -/
theorem leanDojoFiniteEnergy_memLp_velocity
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (h7 : FiniteEnergy sol.velocity)
    (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun x : Space3 => sol.velocity (spacetime_point t x)) 2 := by
  rcases h7 with ⟨C, _hCpos, hC⟩
  rcases hC t ht with ⟨hfinite, _hbound⟩
  have hmeas := leanDojoVelocitySlice_aestronglyMeasurable sol t ht
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  exact hfinite.congr
    (Filter.Eventually.of_forall fun x =>
      euclidean_sum_sq_eq_norm_sq
        (sol.velocity (spacetime_point t x)))

/-- Comparator's scalar norm field is therefore in `L²`. -/
theorem leanDojoFiniteEnergy_memLp_norm
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (h7 : FiniteEnergy sol.velocity)
    (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun x : Space3 =>
      ‖leanVelocityToComparator sol.velocity x t‖) 2 := by
  simpa [leanVelocityToComparator, leanFieldToComparator] using
    (leanDojoFiniteEnergy_memLp_velocity sol h7 t ht).norm

/-- The uniform energy bound is definitionally the same numerical integral. -/
theorem leanDojoFiniteEnergy_globalBound
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (h7 : FiniteEnergy sol.velocity) :
    ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t →
      (∫ x : Space3,
        ‖leanVelocityToComparator sol.velocity x t‖ ^ 2) < E := by
  rcases h7 with ⟨C, _hCpos, hC⟩
  refine ⟨C, ?_⟩
  intro t ht
  have hb := (hC t ht).2
  rw [energyIntegral_eq_integral_norm_sq] at hb
  simpa [leanVelocityToComparator, leanFieldToComparator] using hb

/-- All whole-space energy fields required by the comparator are now produced
from LeanDojo's literal Fefferman condition (7). -/
theorem leanDojoFiniteEnergy_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (h7 : FiniteEnergy sol.velocity) :
    (∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Space3 =>
        ‖leanVelocityToComparator sol.velocity x t‖) 2) ∧
    (∃ E : ℝ, ∀ t : ℝ, 0 ≤ t →
      (∫ x : Space3,
        ‖leanVelocityToComparator sol.velocity x t‖ ^ 2) < E) :=
  ⟨leanDojoFiniteEnergy_memLp_norm sol h7,
    leanDojoFiniteEnergy_globalBound sol h7⟩

end DASHILiteralClayNS
