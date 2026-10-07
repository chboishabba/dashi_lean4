import Adapter
import Problems.NavierStokes.Millennium

/-!
# Direct comparator -> exact LeanDojo Fefferman C max-cut

The released comparator theorem and the pinned LeanDojo target quantify over the
same spatial carrier but use different spacetime representations.  This file
removes the previous opaque proposition-level `ClayOptionC ↔ FeffermanC` seam.

The only remaining obligations are the three concrete transports below:

1. comparator initial-data hypotheses -> LeanDojo condition (4) + divergence;
2. comparator force hypotheses -> LeanDojo condition (5) after the fixed
   pair-spacetime -> time-first `Fin 4` packing below;
3. a LeanDojo global smooth finite-energy solution -> the comparator solution
   on the original curried force, again through the fixed carrier map.

No fluid estimate is introduced here.  If these representation lemmas are
inhabited, the already-proved comparator C theorem composes directly to the
exact pinned `MillenniumNavierStokes.FeffermanC` proposition.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-- Fixed representation map from the comparator's curried `(x,t)` force to
LeanDojo's time-first ambient `Fin 4` spacetime field. -/
noncomputable def comparatorForceToLeanDojo
    (f : R3 → ℝ → R3) : ForceField 3 :=
  fun z => f (NavierStokes.space z) (NavierStokes.time z)

/-- Read a LeanDojo ambient velocity field on the comparator's curried carrier. -/
noncomputable def leanDojoVelocityToComparator
    (u : VelocityField 3) : R3 → ℝ → R3 :=
  fun x t => u (NavierStokes.spacetime_point t x)

/-- Read a LeanDojo ambient pressure field on the comparator's curried carrier. -/
noncomputable def leanDojoPressureToComparator
    (p : PressureField 3) : R3 → ℝ → ℝ :=
  fun x t => p (NavierStokes.spacetime_point t x)

/-- Initial-data representation obligation only.  The carrier itself is already
literally `EuclideanSpace ℝ (Fin 3)` on both sides. -/
def ComparatorInitialToLeanDojo : Prop :=
  ∀ u₀ : R3 → R3,
    NavierStokes.Comparator.InitialVelocityConditionDecay u₀ →
      NavierStokesOnR3.SmoothRapidDecayInitial u₀ ∧
      NavierStokesOnR3.DivergenceFreeInitial u₀

/-- Force representation obligation only. -/
def ComparatorForceToLeanDojo : Prop :=
  ∀ f : R3 → ℝ → R3,
    NavierStokes.Comparator.ForceConditionDecay f →
      NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLeanDojo f)

/-- Solution representation obligation only.  This is intentionally stated on
an actual LeanDojo `GlobalSmoothSolution` and returns the exact comparator
solution structure consumed by the released contradiction theorem. -/
def LeanDojoSolutionToComparator : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (comparatorForceToLeanDojo f))),
      NavierStokesOnR3.FiniteEnergy sol.velocity →
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn
          ν u₀ f
          (leanDojoVelocityToComparator sol.velocity)
          (leanDojoPressureToComparator sol.pressure)

/-- The exact representation frontier.  Unlike the old statement weld, every
field is a concrete carrier/predicate transport that can be attacked
independently and reused in an audit. -/
structure LeanDojoCTransportFrontier : Prop where
  initial : ComparatorInitialToLeanDojo
  force : ComparatorForceToLeanDojo
  solution : LeanDojoSolutionToComparator

/-- Composition theorem: the released comparator C theorem plus only the three
representation transports above proves the literal pinned LeanDojo Fefferman C
proposition. -/
theorem leanDojoFeffermanC_of_transport
    (w : LeanDojoCTransportFrontier) :
    MillenniumNavierStokes.FeffermanC := by
  intro ν ν_pos
  obtain ⟨u₀, f, hu₀, hf, hno⟩ :=
    SemanticGapAdapter.openAIComparatorOptionC ν ν_pos
  have hinit := w.initial u₀ hu₀
  refine ⟨u₀, comparatorForceToLeanDojo f,
    hinit.1, hinit.2, w.force f hf, ?_⟩
  intro hdiv hExists
  apply hno
  rcases hExists with ⟨sol, _hsmooth, henergy⟩
  exact ⟨leanDojoVelocityToComparator sol.velocity,
    leanDojoPressureToComparator sol.pressure,
    w.solution ν ν_pos u₀ f hdiv sol henergy⟩

#print axioms leanDojoFeffermanC_of_transport

end DASHILiteralClayNS
