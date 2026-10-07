import Adapter
import LeanDojoCarrierGeometry
import Problems.NavierStokes.Millennium

/-!
# Direct ClaySpec -> exact LeanDojo Fefferman C max-cut

The released comparator theorem is already welded to the independently frozen
`ClaySpec` representation by `Gap.lean`:

* comparator data -> `ClaySpec.AdmissibleDataR3`;
* `ClaySpec.ClaySolutionR3` -> the exact comparator solution structure.

`LeanDojoCarrierGeometry` additionally pays the literal spatial carrier,
pair-spacetime packing round-trip, domain membership, smooth pullback, and
initial-divergence identity. The external acceptance seam therefore does not
reopen any of those facts.

No fluid estimate is introduced here. Every residual below is a representation,
coordinate-derivative, boundary-extension, or energy-carrier transport.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-! ## Data-side residuals -/

/-- Condition-(4) derivative-packaging transport only. Smoothness is already a
literal common predicate and divergence is paid separately by
`clayInitialDivergenceFree_to_leanDojo`. -/
def ClayInitialDecayToLeanDojo : Prop :=
  ∀ u₀ : R3 → R3,
    ContDiff ℝ ∞ u₀ →
    ClaySpec.InitialRapidDecay u₀ →
      NavierStokesOnR3.SmoothRapidDecayInitial u₀

/-- Condition-(5) representation transport only, after `Gap.lean` has already
proved the ClaySpec force smoothness and derivative-decay clauses. -/
def ClayForceToLeanDojo : Prop :=
  ∀ f : R3 → ℝ → R3,
    ClaySpec.TrustBoundarySmoothOn (SemanticGap.uncurryField f) →
    ClaySpec.ForceRapidDecayR3 (SemanticGap.uncurryField f) →
      NavierStokesOnR3.SmoothRapidDecayForce (pairFieldToLeanDojo f)

/-! ## Solution-side residuals -/

/-- Transport LeanDojo's positive-time momentum equation into ClaySpec equation
(1) on the closed half-space. The only non-definitional analytic content here
is the smooth boundary extension from `t > 0` to `t = 0`. -/
def LeanDojoMomentumToClay : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (pairFieldToLeanDojo f))),
      ClaySpec.EquationOne ν
        (leanDojoFieldToPair sol.velocity)
        (leanDojoFieldToPair sol.pressure)
        (SemanticGap.uncurryField f)

/-- Transport LeanDojo incompressibility from the open half-space to ClaySpec's
closed-half-space equation (2), again exposing boundary extension explicitly. -/
def LeanDojoIncompressibleToClay : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (pairFieldToLeanDojo f))),
      ClaySpec.EquationTwo (leanDojoFieldToPair sol.velocity)

/-- Translate LeanDojo's finite-energy representation (coordinate square sum)
into ClaySpec's vector-valued `MemLp` plus norm-square integral representation. -/
def LeanDojoEnergyToClay : Prop :=
  ∀ (u : VelocityField 3),
    NavierStokesOnR3.FiniteEnergy u →
      ClaySpec.BoundedEnergy (leanDojoFieldToPair u)

/-- The initial condition is not residual: it follows directly from the fixed
pair/ambient round-trip and the `GlobalSmoothSolution` initial condition. -/
theorem leanDojoInitialCondition_to_clay
    {ν : ℝ} {ν_pos : ν > 0}
    {u₀ : NavierStokesOnR3.InitialVelocity}
    {f : R3 → ℝ → R3}
    {hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀}
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (pairFieldToLeanDojo f))) :
    ClaySpec.EquationThree u₀ (leanDojoFieldToPair sol.velocity) := by
  intro x
  simpa [ClaySpec.EquationThree, leanDojoFieldToPair,
    NavierStokesOnR3.equations] using sol.initial_condition x

/-- Exact solution-side representation frontier, after removing smoothness,
initial condition, and all already-paid comparator/ClaySpec semantics. -/
structure LeanDojoSolutionTransportFrontier : Prop where
  momentum : LeanDojoMomentumToClay
  incompressible : LeanDojoIncompressibleToClay
  energy : LeanDojoEnergyToClay

/-- Compile the three residual solution-side representation facts into the
literal independent ClaySpec solution object. -/
theorem leanDojoSolutionToClaySpec_of_transport
    (w : LeanDojoSolutionTransportFrontier)
    {ν : ℝ} {ν_pos : ν > 0}
    {u₀ : NavierStokesOnR3.InitialVelocity}
    {f : R3 → ℝ → R3}
    {hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀}
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (pairFieldToLeanDojo f)))
    (henergy : NavierStokesOnR3.FiniteEnergy sol.velocity) :
    ClaySpec.ClaySolutionR3 ν u₀ (SemanticGap.uncurryField f)
      (leanDojoFieldToPair sol.velocity)
      (leanDojoFieldToPair sol.pressure) := by
  refine ⟨leanDojoSmooth_to_pair sol.velocity_smooth,
    leanDojoSmooth_to_pair sol.pressure_smooth,
    w.momentum ν ν_pos u₀ f hdiv sol,
    w.incompressible ν ν_pos u₀ f hdiv sol,
    leanDojoInitialCondition_to_clay sol,
    w.energy sol.velocity henergy⟩

/-! ## Exact target compiler -/

/-- Exact post-archaeology representation frontier. Comparator semantics,
spatial carrier identity, domain round-trip, smooth pullback, initial divergence
and solution initial condition are already paid. Exactly five transport leaves
remain: conditions (4), (5), momentum boundary/coordinate transport,
incompressibility boundary/coordinate transport, and energy representation. -/
structure LeanDojoCTransportFrontier : Prop where
  initialDecay : ClayInitialDecayToLeanDojo
  force : ClayForceToLeanDojo
  solution : LeanDojoSolutionTransportFrontier

/-- The released comparator C theorem, already-paid same-object welds, and only
the five residual transports above compose to the exact pinned Fefferman C
target. LeanDojo's own equivalence removes condition (6) from the contradiction
branch because `GlobalSmoothSolution` already carries it. -/
theorem leanDojoFeffermanC_of_transport
    (w : LeanDojoCTransportFrontier) :
    MillenniumNavierStokes.FeffermanC := by
  change NavierStokesOnR3.Breakdown
  rw [NavierStokesOnR3.Breakdown.iff_no_finite_energy_solution]
  intro ν ν_pos
  obtain ⟨u₀, f, hu₀, hf, hno⟩ :=
    SemanticGapAdapter.openAIComparatorOptionC ν ν_pos
  have hClayData := SemanticGap.admissibleDataR3_of_comparator hu₀ hf
  rcases hClayData with ⟨huSmooth, huDiv, huRapid, hfSmooth, hfRapid⟩
  have hinit := w.initialDecay u₀ huSmooth huRapid
  have hdiv := clayInitialDivergenceFree_to_leanDojo u₀ huDiv
  have hforce := w.force f hfSmooth hfRapid
  refine ⟨u₀, pairFieldToLeanDojo f, hinit, hdiv, hforce, ?_⟩
  intro hdiv' hExists
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
