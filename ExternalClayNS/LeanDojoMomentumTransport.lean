import LeanDojoSecondDerivativeTransport
import LeanDojoDivergenceTransport
import LeanDojoBoundaryResidualContinuity

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

def leanPressureToClay (p : PressureField 3) : ClaySpec.Pressure :=
  Function.uncurry (leanPressureToComparator p)

def leanForceToClay (f : ForceField 3) : ClaySpec.Force :=
  Function.uncurry (leanFieldToComparator f)

@[simp] theorem leanVelocityToClay_apply (u : VelocityField 3) (q : SpaceTime) :
    leanVelocityToClay u q = u (pairToLeanSpacetime q) := rfl

@[simp] theorem leanPressureToClay_apply (p : PressureField 3) (q : SpaceTime) :
    leanPressureToClay p q = p (pairToLeanSpacetime q) := rfl

@[simp] theorem leanForceToClay_apply (f : ForceField 3) (q : SpaceTime) :
    leanForceToClay f q = f (pairToLeanSpacetime q) := rfl

theorem clayConvection_pullback_eq_leanDojo
    {u : VelocityField 3}
    (hu : ContDiffOn ℝ ∞ u (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    ClaySpec.convectionComponent (leanVelocityToClay u) i q =
      ∑ j : Fin 3,
        u (pairToLeanSpacetime q) j *
          partial_deriv (n := 4) j.succ (fun y => u y i)
            (pairToLeanSpacetime q) := by
  unfold ClaySpec.convectionComponent
  apply Finset.sum_congr rfl
  intro j _hj
  rw [leanVelocityToClay_apply]
  rw [clayPartialSpace_pullback_eq_leanDojo
    (leanComponentSmooth hu i) q hq j]

theorem clayLaplacian_pullback_eq_leanDojo
    {u : VelocityField 3}
    (hu : ContDiffOn ℝ ∞ u (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    ClaySpec.spatialLaplacianComponent (leanVelocityToClay u) i q =
      ∑ j : Fin 3,
        partial_deriv (n := 4) j.succ
          (fun y => partial_deriv (n := 4) j.succ (fun z => u z i) y)
          (pairToLeanSpacetime q) := by
  unfold ClaySpec.spatialLaplacianComponent
  apply Finset.sum_congr rfl
  intro j _hj
  exact claySecondPartial_pullback_eq_leanDojo
    (leanComponentSmooth hu i) q hq j

theorem leanDojoMomentum_positive_to_clay
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    clayMomentumResidualComponent nse.viscosity
      (leanVelocityToClay sol.velocity)
      (leanPressureToClay sol.pressure)
      (leanForceToClay nse.external_force) i q = 0 := by
  let z : Spacetime3 := pairToLeanSpacetime q
  have hz : z ∈ interior_spacetime_domain 3 := by
    simpa [z, interior_spacetime_domain] using hq
  have hmom := sol.momentum_equation z hz
  have hi := congrArg (fun v : Space3 => v i) hmom
  simp only [material_derivative, pressure_gradient, viscous_term,
    EuclideanCoordinateSpace.of_fun_apply] at hi
  have htime :
      ClaySpec.partialTime (fun w => leanVelocityToClay sol.velocity w i) q =
        partial_deriv (n := 4) (0 : Fin 4) (fun y => sol.velocity y i) z := by
    simpa [leanVelocityToClay, z] using
      clayPartialTime_pullback_eq_leanDojo
        (leanComponentSmooth sol.velocity_smooth i) q hq
  have hconv := clayConvection_pullback_eq_leanDojo sol.velocity_smooth q hq i
  have hlap := clayLaplacian_pullback_eq_leanDojo sol.velocity_smooth q hq i
  have hp :
      ClaySpec.partialSpace i (leanPressureToClay sol.pressure) q =
        partial_deriv (n := 4) i.succ sol.pressure z := by
    simpa [leanPressureToClay, z] using
      clayPartialSpace_pullback_eq_leanDojo sol.pressure_smooth q hq i
  unfold clayMomentumResidualComponent
  rw [htime, hconv, hlap, hp]
  simp only [leanForceToClay_apply, z]
  linarith

theorem leanDojoMomentum_to_clayEquationOne
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (hf : ContDiffOn ℝ ∞ nse.external_force (global_spacetime_domain 3)) :
    ClaySpec.EquationOne nse.viscosity
      (leanVelocityToClay sol.velocity)
      (leanPressureToClay sol.pressure)
      (leanForceToClay nse.external_force) := by
  have hu : ContDiffOn ℝ ∞ (leanVelocityToClay sol.velocity) nonnegativeTime :=
    contDiffOn_leanFieldToComparator sol.velocity_smooth
  have hp : ContDiffOn ℝ ∞ (leanPressureToClay sol.pressure) nonnegativeTime :=
    contDiffOn_leanFieldToComparator sol.pressure_smooth
  have hforce : ContDiffOn ℝ ∞ (leanForceToClay nse.external_force) nonnegativeTime :=
    contDiffOn_leanFieldToComparator hf
  exact equationOne_of_positive nse.viscosity hu hp hforce
    (fun q hq i => leanDojoMomentum_positive_to_clay sol q hq i)

end DASHILiteralClayNS
