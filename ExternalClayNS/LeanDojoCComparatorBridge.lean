import Adapter
import LeanDojoSameObject
import LeanDojoCoordinateLinearEquiv
import LeanDojoBoundaryExtension
import Problems.NavierStokes.Millennium

/-!
# Direct released comparator -> exact LeanDojo Fefferman C max-cut

The live external-target base now owns the canonical spacetime equivalence,
field round-trips, smooth pullbacks, boundary-extension lemma, initial divergence
transport, and the complete condition-(4) comparator -> LeanDojo decay theorem.
This file consumes those owners rather than duplicating them.

Exactly four representation leaves remain:

1. comparator force condition (5) -> LeanDojo condition (5);
2. positive-time momentum -> closed-half-space Clay equation;
3. positive-time incompressibility -> closed-half-space Clay equation;
4. LeanDojo coordinate-square finite energy -> ClaySpec vector L2 energy.

No new Navier--Stokes estimate is introduced at this seam.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-! ## Data-side residual -/

/-- Comparator's full force-jet hypothesis is stronger than LeanDojo condition
(5); only the exact coordinate/permutation derivative transport remains. -/
def ComparatorForceDecayToLeanDojo : Prop :=
  ∀ f : R3 → ℝ → R3,
    NavierStokes.Comparator.ForceConditionDecay f →
      NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLean f)

/-! ## Solution-side residuals -/

/-- Transport LeanDojo's positive-time momentum equation into the frozen
pair-coordinate equation on the closed half-space. `LeanDojoBoundaryExtension`
already pays the generic topological t=0 extension principle. -/
def LeanDojoMomentumToClay : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (comparatorForceToLean f))),
      ClaySpec.EquationOne ν
        (Function.uncurry (leanVelocityToComparator sol.velocity))
        (Function.uncurry (leanPressureToComparator sol.pressure))
        (SemanticGap.uncurryField f)

/-- Same transport for incompressibility, including the already-isolated smooth
boundary extension from positive to nonnegative time. -/
def LeanDojoIncompressibleToClay : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (comparatorForceToLean f))),
      ClaySpec.EquationTwo
        (Function.uncurry (leanVelocityToComparator sol.velocity))

/-- Identify LeanDojo's coordinate-square finite-energy representation with the
frozen vector-valued `MemLp`/norm-square representation. -/
def LeanDojoEnergyToClay : Prop :=
  ∀ (u : VelocityField 3),
    NavierStokesOnR3.FiniteEnergy u →
      ClaySpec.BoundedEnergy
        (Function.uncurry (leanVelocityToComparator u))

/-- Initial condition is already exact under the canonical same-object map. -/
theorem leanDojoInitialCondition_to_clay
    {ν : ℝ} {ν_pos : ν > 0}
    {u₀ : NavierStokesOnR3.InitialVelocity}
    {f : R3 → ℝ → R3}
    {hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀}
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (comparatorForceToLean f))) :
    ClaySpec.EquationThree u₀
      (Function.uncurry (leanVelocityToComparator sol.velocity)) := by
  intro x
  simpa [ClaySpec.EquationThree, leanVelocityToComparator,
    leanFieldToComparator, NavierStokesOnR3.equations] using
    sol.initial_condition x

structure LeanDojoSolutionTransportFrontier : Prop where
  momentum : LeanDojoMomentumToClay
  incompressible : LeanDojoIncompressibleToClay
  energy : LeanDojoEnergyToClay

/-- Compile the three residual solution transports into the literal independent
ClaySpec solution. Smoothness uses the canonical continuous-linear equivalence. -/
theorem leanDojoSolutionToClaySpec_of_transport
    (w : LeanDojoSolutionTransportFrontier)
    {ν : ℝ} {ν_pos : ν > 0}
    {u₀ : NavierStokesOnR3.InitialVelocity}
    {f : R3 → ℝ → R3}
    {hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀}
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (comparatorForceToLean f)))
    (henergy : NavierStokesOnR3.FiniteEnergy sol.velocity) :
    ClaySpec.ClaySolutionR3 ν u₀ (SemanticGap.uncurryField f)
      (Function.uncurry (leanVelocityToComparator sol.velocity))
      (Function.uncurry (leanPressureToComparator sol.pressure)) := by
  refine ⟨?_, ?_,
    w.momentum ν ν_pos u₀ f hdiv sol,
    w.incompressible ν ν_pos u₀ f hdiv sol,
    leanDojoInitialCondition_to_clay sol,
    w.energy sol.velocity henergy⟩
  · simpa [ClaySpec.TrustBoundarySmoothOn] using
      contDiffOn_leanFieldToComparator sol.velocity_smooth
  · simpa [ClaySpec.TrustBoundarySmoothOn] using
      contDiffOn_leanFieldToComparator sol.pressure_smooth

/-! ## Exact target compiler -/

structure LeanDojoCTransportFrontier : Prop where
  force : ComparatorForceDecayToLeanDojo
  solution : LeanDojoSolutionTransportFrontier

/-- Released comparator C plus only the four residual representation transports
proves the exact pinned LeanDojo Fefferman C proposition. -/
theorem leanDojoFeffermanC_of_transport
    (w : LeanDojoCTransportFrontier) :
    MillenniumNavierStokes.FeffermanC := by
  change NavierStokesOnR3.Breakdown
  rw [NavierStokesOnR3.Breakdown.iff_no_finite_energy_solution]
  intro ν ν_pos
  obtain ⟨u₀, f, hu₀, hf, hno⟩ :=
    SemanticGapAdapter.openAIComparatorOptionC ν ν_pos
  have hinit := comparatorInitialDecayData_to_leanDojo hu₀
  have hforce := w.force f hf
  refine ⟨u₀, comparatorForceToLean f,
    hinit.1, hinit.2, hforce, ?_⟩
  intro hdiv hExists
  apply hno
  rcases hExists with ⟨sol, henergy⟩
  have hClay := leanDojoSolutionToClaySpec_of_transport w.solution sol henergy
  have hComparator := SemanticGap.claySolutionR3_to_comparator hClay
  rw [SemanticGap.curryField_uncurryField] at hComparator
  exact ⟨_, _, hComparator⟩

#print axioms leanDojoInitialCondition_to_clay
#print axioms leanDojoSolutionToClaySpec_of_transport
#print axioms leanDojoFeffermanC_of_transport

end DASHILiteralClayNS
