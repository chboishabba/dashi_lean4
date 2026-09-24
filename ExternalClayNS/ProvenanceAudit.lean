import ClauseAudit
import NavierStokes.ComparatorSolution
import NavierStokes.ComparatorR3Theorem
import NavierStokes.ComparatorTheorem

/-!
# Goal-1 C/D provenance audit

This file makes the source-backed part of the Clay-facing argument mechanically
inspectable at the pinned `openai/NavierStokesAndEuler` revision selected by
`lakefile.toml`.

It deliberately does not re-prove standard analysis.  Instead it records the
actual upstream theorem spine at the comparator boundary and then rechecks the
independent ClaySpec adapters.  The trailing `#print axioms` commands are the
build-time trust receipt: if an upstream theorem acquires a non-foundational
axiom, it is visible here rather than hidden behind `literalClayC/D`.
-/

noncomputable section

namespace DASHILiteralClayNS.ProvenanceAudit

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Upstream whole-space comparator theorem, restated without changing its
proposition. -/
theorem pinnedComparatorC (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p,
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) :=
  NavierStokes.Comparator.navier_stokes_breakdown_R3 ν hν

/-- The immediate bridge theorem used by the upstream comparator theorem. -/
theorem pinnedBridgeC (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p,
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) :=
  NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3 ν hν

/-- Upstream periodic comparator theorem, including the comparator's pressure
periodicity requirement through its solution predicate. -/
theorem pinnedComparatorD (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p,
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) :=
  NavierStokes.Comparator.navier_stokes_breakdown_periodic ν hν

/-- The immediate periodic bridge theorem used by the upstream comparator
theorem. -/
theorem pinnedBridgeD (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p,
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) :=
  NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic ν hν

/-- Independent-spec endpoint for C, kept separate from the upstream comparator
surface. -/
theorem pinnedSourceToClayC : ClaySpec.ClayOptionC :=
  SemanticGapAdapter.openAI_to_ClayOptionC

/-- Independent-spec endpoint for D. -/
theorem pinnedSourceToClayD : ClaySpec.ClayOptionD :=
  SemanticGapAdapter.openAI_to_ClayOptionD

/-- Clause-audited C endpoint from the same pinned source theorem. -/
theorem pinnedSourceToClauseAuditedC : DASHILiteralClayNS.ClayOptionC :=
  DASHILiteralClayNS.literalClayC_roundTrip

/-- Clause-audited D endpoint from the same pinned source theorem. -/
theorem pinnedSourceToClauseAuditedD : DASHILiteralClayNS.ClayOptionD :=
  DASHILiteralClayNS.literalClayD_roundTrip

#print axioms NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms SemanticGapAdapter.openAI_to_ClayOptionC
#print axioms DASHILiteralClayNS.literalClayC_roundTrip
#print axioms pinnedSourceToClauseAuditedC

#print axioms NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
#print axioms SemanticGapAdapter.openAI_to_ClayOptionD
#print axioms DASHILiteralClayNS.literalClayD_roundTrip
#print axioms pinnedSourceToClauseAuditedD

end DASHILiteralClayNS.ProvenanceAudit
