import LeanDojoBoundaryExtension
import Gap
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Continuity of the pulled-back Navier--Stokes residual

This pays the analytic-topological step needed to extend LeanDojo's positive-time
PDE to the comparator/frozen-Clay closed half-space.  No PDE estimate enters:
it is a consequence of C-infinity smoothness and continuity of first/second
within derivatives.
-/

noncomputable section

open ClaySpec
open MeasureTheory Set

namespace DASHILiteralClayNS

/-- Every fixed directional derivative word of a smooth field is continuous on
the closed product half-space. -/
theorem continuousOn_iteratedDirectionalWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E}
    (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (dirs : List SpaceTime) :
    ContinuousOn (iteratedDirectionalWithin dirs g) nonnegativeTime := by
  have hjet : ContinuousOn
      (iteratedFDerivWithin ℝ dirs.length g nonnegativeTime)
      nonnegativeTime :=
    hg.continuousOn_iteratedFDerivWithin (by simp)
      SemanticGap.uniqueDiffOn_nonnegativeTime
  let ev :
      ContinuousMultilinearMap ℝ (fun _ : Fin dirs.length => SpaceTime) E →L[ℝ] E :=
    ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin dirs.length => SpaceTime) E dirs.get
  have hev : ContinuousOn
      (fun z => ev (iteratedFDerivWithin ℝ dirs.length g nonnegativeTime z))
      nonnegativeTime :=
    ev.continuous.continuousOn.comp hjet (mapsTo_univ _ _)
  refine hev.congr ?_
  intro z hz
  exact (SemanticGap.iteratedDirectionalWithin_eq_iteratedFDerivWithin
    hg dirs z hz).symm

/-- A single spatial Clay partial of a smooth scalar field is continuous. -/
theorem continuousOn_partialSpace
    {g : SpaceTime → ℝ}
    (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (i : Fin 3) :
    ContinuousOn (partialSpace i g) nonnegativeTime := by
  simpa [partialSpace, iteratedDirectionalWithin] using
    continuousOn_iteratedDirectionalWithin hg [spatialDirection i]

/-- A single Clay time partial is continuous. -/
theorem continuousOn_partialTime
    {g : SpaceTime → ℝ}
    (hg : ContDiffOn ℝ ∞ g nonnegativeTime) :
    ContinuousOn (partialTime g) nonnegativeTime := by
  simpa [partialTime, iteratedDirectionalWithin] using
    continuousOn_iteratedDirectionalWithin hg [timeDirection]

/-- A repeated spatial second derivative is continuous. -/
theorem continuousOn_secondPartialSpace
    {g : SpaceTime → ℝ}
    (hg : ContDiffOn ℝ ∞ g nonnegativeTime)
    (i : Fin 3) :
    ContinuousOn (fun z => partialSpace i (partialSpace i g) z)
      nonnegativeTime := by
  have h := continuousOn_iteratedDirectionalWithin hg
    [spatialDirection i, spatialDirection i]
  simpa [partialSpace, iteratedDirectionalWithin] using h

/-- The scalar momentum residual whose vanishing is Clay equation (1). -/
def clayMomentumResidualComponent
    (ν : ℝ) (u : Velocity) (p : Pressure) (f : Force)
    (i : Fin 3) (z : SpaceTime) : ℝ :=
  partialTime (fun w => u w i) z + convectionComponent u i z -
    (ν * spatialLaplacianComponent u i z - partialSpace i p z + f z i)

/-- The complete Clay momentum residual is continuous on the closed half-space
whenever velocity, pressure and force are smooth there. -/
theorem continuousOn_clayMomentumResidualComponent
    (ν : ℝ) {u : Velocity} {p : Pressure} {f : Force}
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime)
    (hp : ContDiffOn ℝ ∞ p nonnegativeTime)
    (hf : ContDiffOn ℝ ∞ f nonnegativeTime)
    (i : Fin 3) :
    ContinuousOn (clayMomentumResidualComponent ν u p f i)
      nonnegativeTime := by
  have hui (j : Fin 3) :
      ContDiffOn ℝ ∞ (fun z => u z j) nonnegativeTime :=
    SemanticGap.component_smooth hu j
  have hfi : ContDiffOn ℝ ∞ (fun z => f z i) nonnegativeTime :=
    SemanticGap.component_smooth hf i
  have htime := continuousOn_partialTime (hui i)
  have hconv : ContinuousOn (fun z => convectionComponent u i z)
      nonnegativeTime := by
    unfold convectionComponent
    fun_prop
  have hlap : ContinuousOn (fun z => spatialLaplacianComponent u i z)
      nonnegativeTime := by
    unfold spatialLaplacianComponent
    apply continuousOn_finset_sum
    intro j _hj
    exact continuousOn_secondPartialSpace (hui i) j
  have hpress := continuousOn_partialSpace hp i
  have hforce : ContinuousOn (fun z => f z i) nonnegativeTime :=
    hfi.continuousOn
  unfold clayMomentumResidualComponent
  exact (htime.add hconv).sub
    (((continuousOn_const.mul hlap).sub hpress).add hforce)

/-- Restricting the residual to one spatial point produces a continuous function
on the closed nonnegative time line. -/
theorem continuousOn_clayMomentumResidual_timeSlice
    (ν : ℝ) {u : Velocity} {p : Pressure} {f : Force}
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime)
    (hp : ContDiffOn ℝ ∞ p nonnegativeTime)
    (hf : ContDiffOn ℝ ∞ f nonnegativeTime)
    (i : Fin 3) (x : R3) :
    ContinuousOn (fun t : ℝ => clayMomentumResidualComponent ν u p f i (x, t))
      (Ici 0) := by
  apply (continuousOn_clayMomentumResidualComponent ν hu hp hf i).comp
    (continuousOn_const.prodMk continuousOn_id)
  intro t ht
  exact ht

/-- Positive-time Clay equation (1) extends to time zero solely by smoothness. -/
theorem equationOne_of_positive
    (ν : ℝ) {u : Velocity} {p : Pressure} {f : Force}
    (hu : ContDiffOn ℝ ∞ u nonnegativeTime)
    (hp : ContDiffOn ℝ ∞ p nonnegativeTime)
    (hf : ContDiffOn ℝ ∞ f nonnegativeTime)
    (hpos : ∀ z : SpaceTime, 0 < z.2 → ∀ i : Fin 3,
      clayMomentumResidualComponent ν u p f i z = 0) :
    EquationOne ν u p f := by
  intro z hz i
  have hcont := continuousOn_clayMomentumResidual_timeSlice
    ν hu hp hf i z.1
  have hall : ∀ t : ℝ, 0 ≤ t →
      clayMomentumResidualComponent ν u p f i (z.1, t) = 0 := by
    intro t ht
    exact eq_of_pos_eq_of_continuousOn_Ici hcont continuousOn_const
      (fun s hs => hpos (z.1, s) hs i) ht
  have hres := hall z.2 hz
  unfold clayMomentumResidualComponent at hres
  linarith

end DASHILiteralClayNS
