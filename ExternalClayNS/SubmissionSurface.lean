import ProvenanceAudit
import NavierStokes.PeriodicPaperTheorem
import NavierStokes.ComparatorR3Theorem

/-!
# Clay-facing submission surface for alternatives C and D

This module intentionally contains no new PDE machinery.  It exposes the two
source-backed routes on the independently frozen Clay specification, together
with the exact fixed-viscosity witness packages a referee needs to inspect.

The mathematical burden behind these declarations remains the upstream source
proof itself.  This file is an audit/capstone surface, not an assertion that a
referee audit has been completed merely because Lean accepts the composition.
-/

noncomputable section

open ClaySpec

namespace DASHILiteralClayNS.SubmissionSurface

/-- Exact Clay-C witness package at fixed positive viscosity. -/
structure ClayCSubmissionWitness (ν : ℝ) (hν : 0 < ν) : Prop where
  initialVelocity : InitialVelocity
  forcing : Force
  initialSmooth : ContDiff ℝ ∞ initialVelocity
  initialDivergenceFree : InitialDivergenceFree initialVelocity
  initialRapidDecay : InitialRapidDecay initialVelocity
  forcingSmooth : TrustBoundarySmoothOn forcing
  forcingRapidDecay : ForceRapidDecayR3 forcing
  excludesGlobalSmoothBoundedEnergy :
    ¬ ∃ u : Velocity, ∃ p : Pressure,
      ClaySolutionR3 ν initialVelocity forcing u p

/-- Exact Clay-D witness package at fixed positive viscosity, including the
pressure-periodicity erratum through `ClaySolutionPeriodic`. -/
structure ClayDSubmissionWitness (ν : ℝ) (hν : 0 < ν) : Prop where
  initialVelocity : InitialVelocity
  forcing : Force
  initialSmooth : ContDiff ℝ ∞ initialVelocity
  initialDivergenceFree : InitialDivergenceFree initialVelocity
  initialPeriodic : SpatiallyPeriodicInitial initialVelocity
  forcingSmooth : TrustBoundarySmoothOn forcing
  forcingPeriodic : SpatiallyPeriodic forcing
  forcingRapidTimeDecayAllDerivatives : ForceRapidDecayPeriodic forcing
  excludesGlobalSmoothPeriodic :
    ¬ ∃ u : Velocity, ∃ p : Pressure,
      ClaySolutionPeriodic ν initialVelocity forcing u p

theorem clayCSubmissionWitness
    (ν : ℝ) (hν : 0 < ν) : ClayCSubmissionWitness ν hν := by
  let w := DASHILiteralClayNS.literalClayC_clauseAudit ν hν
  exact {
    initialVelocity := w.initialVelocity
    forcing := w.forcing
    initialSmooth := w.initialSmooth
    initialDivergenceFree := w.initialDivergenceFree
    initialRapidDecay := w.initialRapidDecay
    forcingSmooth := w.forcingSmooth
    forcingRapidDecay := w.forcingRapidDecay
    excludesGlobalSmoothBoundedEnergy := w.noGlobalSmoothBoundedEnergySolution
  }

theorem clayDSubmissionWitness
    (ν : ℝ) (hν : 0 < ν) : ClayDSubmissionWitness ν hν := by
  let w := DASHILiteralClayNS.literalClayD_clauseAudit ν hν
  exact {
    initialVelocity := w.initialVelocity
    forcing := w.forcing
    initialSmooth := w.initialSmooth
    initialDivergenceFree := w.initialDivergenceFree
    initialPeriodic := w.initialPeriodic
    forcingSmooth := w.forcingSmooth
    forcingPeriodic := w.forcingPeriodic
    forcingRapidTimeDecayAllDerivatives := w.forcingRapidTimeDecayAllDerivatives
    excludesGlobalSmoothPeriodic := w.noGlobalSmoothPeriodicSolution
  }

/-- Repackaging the fixed-viscosity C submission witnesses is exactly Clay C. -/
theorem clayOptionC_of_submissionWitnesses
    (h : ∀ ν : ℝ, ∀ hν : 0 < ν, ClayCSubmissionWitness ν hν) :
    ClaySpec.ClayOptionC := by
  intro ν hν
  let w := h ν hν
  exact ⟨w.initialVelocity, w.forcing,
    ⟨w.initialSmooth, w.initialDivergenceFree, w.initialRapidDecay,
      w.forcingSmooth, w.forcingRapidDecay⟩,
    w.excludesGlobalSmoothBoundedEnergy⟩

/-- Repackaging the fixed-viscosity D submission witnesses is exactly Clay D. -/
theorem clayOptionD_of_submissionWitnesses
    (h : ∀ ν : ℝ, ∀ hν : 0 < ν, ClayDSubmissionWitness ν hν) :
    ClaySpec.ClayOptionD := by
  intro ν hν
  let w := h ν hν
  exact ⟨w.initialVelocity, w.forcing,
    ⟨w.initialSmooth, w.initialDivergenceFree, w.initialPeriodic,
      w.forcingSmooth, w.forcingPeriodic,
      w.forcingRapidTimeDecayAllDerivatives⟩,
    w.excludesGlobalSmoothPeriodic⟩

/-- Clay-facing endpoint via the independently audited C surface. -/
theorem submissionClayC : ClaySpec.ClayOptionC :=
  clayOptionC_of_submissionWitnesses clayCSubmissionWitness

/-- Clay-facing endpoint via the independently audited D surface. -/
theorem submissionClayD : ClaySpec.ClayOptionD :=
  clayOptionD_of_submissionWitnesses clayDSubmissionWitness

/--
The upstream periodic source theorem used by the D route, restated verbatim at
its paper-facing boundary.  Keeping this theorem visible here prevents the
submission surface from obscuring the provenance chain.
-/
theorem pinnedPeriodicPaperCorollary :
    NavierStokes.PeriodicPaper.breakdownStatement :=
  NavierStokes.PeriodicPaper.periodic_corollary

/-- The upstream whole-space source theorem used by the C route. -/
theorem pinnedWholeSpaceTheorem :
    NavierStokesR3.ProblemStatement.breakdownStatement :=
  NavierStokesR3.theorem_1_1

#print axioms NavierStokes.PeriodicPaper.periodic_corollary
#print axioms NavierStokesR3.theorem_1_1
#print axioms clayCSubmissionWitness
#print axioms clayDSubmissionWitness
#print axioms submissionClayC
#print axioms submissionClayD

end DASHILiteralClayNS.SubmissionSurface
