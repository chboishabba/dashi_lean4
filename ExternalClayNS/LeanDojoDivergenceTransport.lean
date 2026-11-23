import LeanDojoDifferentialTransport
import LeanDojoBoundaryResidualContinuity

noncomputable section

open ClaySpec
open NavierStokes
open Set

namespace DASHILiteralClayNS

theorem leanComponentSmooth
    {u : VelocityField 3}
    (hu : ContDiffOn ℝ ∞ u (global_spacetime_domain 3))
    (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z => u z i) (global_spacetime_domain 3) := by
  simpa [Function.comp_def] using
    hu.continuousLinearMap (EuclideanSpace.proj i)

def leanVelocityToClay (u : VelocityField 3) : ClaySpec.Velocity :=
  Function.uncurry (leanVelocityToComparator u)

theorem clayDivergence_pullback_eq_leanDojo
    {u : VelocityField 3}
    (hu : ContDiffOn ℝ ∞ u (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) :
    ClaySpec.divergence (leanVelocityToClay u) q =
      NavierStokes.divergence u (pairToLeanSpacetime q) := by
  unfold ClaySpec.divergence NavierStokes.divergence leanVelocityToClay
  apply Finset.sum_congr rfl
  intro i _hi
  exact clayPartialSpace_pullback_eq_leanDojo
    (leanComponentSmooth hu i) q hq i

theorem continuousOn_clayDivergence
    {u : ClaySpec.Velocity}
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime) :
    ContinuousOn (ClaySpec.divergence u) nonnegativeTime := by
  unfold ClaySpec.divergence
  apply continuousOn_finset_sum
  intro i _hi
  exact continuousOn_partialSpace (SemanticGap.component_smooth hu i) i

theorem equationTwo_of_positive
    {u : ClaySpec.Velocity}
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime)
    (hpos : ∀ q : SpaceTime, 0 < q.2 → ClaySpec.divergence u q = 0) :
    ClaySpec.EquationTwo u := by
  intro q hq
  have hs : ContinuousOn (fun t : ℝ => ClaySpec.divergence u (q.1, t)) (Ici 0) := by
    apply (continuousOn_clayDivergence hu).comp
      (continuousOn_const.prodMk continuousOn_id)
    intro t ht
    exact ht
  exact eq_of_pos_eq_of_continuousOn_Ici hs continuousOn_const
    (fun t ht => hpos (q.1, t) ht) hq

theorem leanDojoIncompressible_to_clay
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) :
    ClaySpec.EquationTwo (leanVelocityToClay sol.velocity) := by
  have hu : ContDiffOn ℝ ∞ (leanVelocityToClay sol.velocity) nonnegativeTime :=
    contDiffOn_leanFieldToComparator sol.velocity_smooth
  apply equationTwo_of_positive hu
  intro q hq
  rw [clayDivergence_pullback_eq_leanDojo sol.velocity_smooth q hq]
  exact sol.incompressible (pairToLeanSpacetime q) (by simpa using hq)

end DASHILiteralClayNS
