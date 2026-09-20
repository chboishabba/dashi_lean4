import Mathlib
import RequestProject.NavierStokes.WholeSpaceL1BochnerCompletion

/-!
# Whole-space Navier–Stokes physical L¹ tails

This module discharges a concrete analytic leaf of the independent R³ A lane.

For every Bochner-integrable whole-space field f : ℝ³ → E, the physical
L¹ mass outside expanding Euclidean balls tends to zero.

This is a theorem on the literal Lebesgue carrier, not an abstract cubature
hypothesis. It supplies the tail fact required by the existing core/tail
boundary-defect compiler.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RequestProject.NavierStokes

section L1Tail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm mass of any Bochner-integrable field on R3 vanishes outside expanding closed balls. -/
theorem normIntegral_compl_closedBall_tendsto_zero
    (f : R3 → E)
    (hf : Integrable f volume) :
    Tendsto
      (fun n : ℕ =>
        ∫ x : R3 in (Metric.closedBall (0 : R3) n)ᶜ, ‖f x‖)
      atTop
      (nhds 0) := by
  have hnorm : Integrable (fun x : R3 => ‖f x‖) volume := hf.norm
  have hmono :
      Monotone (fun n : ℕ => Metric.closedBall (0 : R3) n) := by
    intro m n hmn
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hinside :
      Tendsto
        (fun n : ℕ =>
          ∫ x : R3 in Metric.closedBall (0 : R3) n, ‖f x‖)
        atTop
        (nhds (∫ x : R3, ‖f x‖)) := by
    simpa only [Metric.iUnion_closedBall_nat, setIntegral_univ] using
      (tendsto_setIntegral_of_monotone
        (f := fun x : R3 => ‖f x‖)
        (μ := volume)
        (s := fun n : ℕ => Metric.closedBall (0 : R3) n)
        (fun _ => Metric.measurableSet_closedBall)
        hmono
        hnorm.integrableOn)
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          (∫ x : R3, ‖f x‖) -
            ∫ x : R3 in Metric.closedBall (0 : R3) n, ‖f x‖)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.sub hinside)
  apply hdiff.congr'
  filter_upwards [] with n
  exact
    (setIntegral_compl
      (Metric.measurableSet_closedBall :
        MeasurableSet (Metric.closedBall (0 : R3) n))
      hnorm).symm

end L1Tail

/-- The coherent six-real-coordinate representation of C³ has vanishing norm tail whenever the literal convolution integrand is Bochner-integrable. -/
theorem coherentVectorNormTail_tendsto_zero
    (integrand : R3 → Complex3RealCoordinates)
    (hintegrable : Integrable integrand volume) :
    Tendsto
      (fun n : ℕ =>
        ∫ η : R3 in (Metric.closedBall (0 : R3) n)ᶜ,
          ‖integrand η‖)
      atTop
      (nhds 0) :=
  normIntegral_compl_closedBall_tendsto_zero integrand hintegrable

end RequestProject.NavierStokes
