import LiteralABCD

/-!
# Clause-by-clause Clay A/B/C/D audit surface

This file makes the Clay-facing proof layer explicit.

* A and B remain the two independent theorem targets.
* C and D are unpacked into concrete witness records whose fields correspond
  directly to the admissibility and nonexistence clauses in the independent
  `ClaySpec` statement.

The point is not to add another semantic wrapper.  The records below expose the
actual witnesses delivered by the source-backed C/D theorems, clause by clause,
so downstream paper/audit code can inspect exactly which Fefferman hypotheses
have been discharged.
-/

noncomputable section

open ClaySpec

namespace DASHILiteralClayNS

/-- The independent Clay-facing obligations that are not supplied by the
source-backed breakdown proof. -/
def IndependentOptionA : Prop := ClayOptionA
def IndependentOptionB : Prop := ClayOptionB

/-- Clause-level witness package for Fefferman alternative C at a fixed
viscosity. -/
structure ClauseAuditC (ν : ℝ) (hν : 0 < ν) : Prop where
  initialVelocity : InitialVelocity
  forcing : Force
  initialSmooth : ContDiff ℝ ∞ initialVelocity
  initialDivergenceFree : InitialDivergenceFree initialVelocity
  initialRapidDecay : InitialRapidDecay initialVelocity
  forcingSmooth : TrustBoundarySmoothOn forcing
  forcingRapidDecay : ForceRapidDecayR3 forcing
  noGlobalSmoothBoundedEnergySolution :
    ¬ ∃ u : Velocity, ∃ p : Pressure,
      ClaySolutionR3 ν initialVelocity forcing u p

/-- Clause-level witness package for Fefferman alternative D at a fixed
viscosity, including pressure periodicity through `ClaySolutionPeriodic`. -/
structure ClauseAuditD (ν : ℝ) (hν : 0 < ν) : Prop where
  initialVelocity : InitialVelocity
  forcing : Force
  initialSmooth : ContDiff ℝ ∞ initialVelocity
  initialDivergenceFree : InitialDivergenceFree initialVelocity
  initialPeriodic : SpatiallyPeriodicInitial initialVelocity
  forcingSmooth : TrustBoundarySmoothOn forcing
  forcingPeriodic : SpatiallyPeriodic forcing
  forcingRapidTimeDecayAllDerivatives : ForceRapidDecayPeriodic forcing
  noGlobalSmoothPeriodicSolution :
    ¬ ∃ u : Velocity, ∃ p : Pressure,
      ClaySolutionPeriodic ν initialVelocity forcing u p

/-- Any literal C proof canonically yields the clause-by-clause fixed-viscosity
audit package. -/
theorem clauseAuditC_of_ClayOptionC
    (hC : ClayOptionC) (ν : ℝ) (hν : 0 < ν) :
    ClauseAuditC ν hν := by
  obtain ⟨u₀, f, hdata, hno⟩ := hC ν hν
  rcases hdata with ⟨hs, hdiv, hrapid, hfs, hfrapid⟩
  exact {
    initialVelocity := u₀
    forcing := f
    initialSmooth := hs
    initialDivergenceFree := hdiv
    initialRapidDecay := hrapid
    forcingSmooth := hfs
    forcingRapidDecay := hfrapid
    noGlobalSmoothBoundedEnergySolution := hno
  }

/-- Any literal D proof canonically yields the clause-by-clause fixed-viscosity
audit package. -/
theorem clauseAuditD_of_ClayOptionD
    (hD : ClayOptionD) (ν : ℝ) (hν : 0 < ν) :
    ClauseAuditD ν hν := by
  obtain ⟨u₀, f, hdata, hno⟩ := hD ν hν
  rcases hdata with ⟨hs, hdiv, hperiodic, hfs, hfperiodic, hfdecay⟩
  exact {
    initialVelocity := u₀
    forcing := f
    initialSmooth := hs
    initialDivergenceFree := hdiv
    initialPeriodic := hperiodic
    forcingSmooth := hfs
    forcingPeriodic := hfperiodic
    forcingRapidTimeDecayAllDerivatives := hfdecay
    noGlobalSmoothPeriodicSolution := hno
  }

/-- Source-backed C, now exposed exactly as the official clause-level witness
package for every positive viscosity. -/
theorem literalClayC_clauseAudit
    (ν : ℝ) (hν : 0 < ν) :
    ClauseAuditC ν hν :=
  clauseAuditC_of_ClayOptionC literalClayC ν hν

/-- Source-backed D, now exposed exactly as the official clause-level witness
package for every positive viscosity. -/
theorem literalClayD_clauseAudit
    (ν : ℝ) (hν : 0 < ν) :
    ClauseAuditD ν hν :=
  clauseAuditD_of_ClayOptionD literalClayD ν hν

/-- Repackaging a clause-level C audit loses no mathematical content. -/
theorem ClayOptionC_of_clauseAudits
    (h : ∀ ν : ℝ, ∀ hν : 0 < ν, ClauseAuditC ν hν) :
    ClayOptionC := by
  intro ν hν
  let w := h ν hν
  exact ⟨w.initialVelocity, w.forcing,
    ⟨w.initialSmooth, w.initialDivergenceFree, w.initialRapidDecay,
      w.forcingSmooth, w.forcingRapidDecay⟩,
    w.noGlobalSmoothBoundedEnergySolution⟩

/-- Repackaging a clause-level D audit loses no mathematical content. -/
theorem ClayOptionD_of_clauseAudits
    (h : ∀ ν : ℝ, ∀ hν : 0 < ν, ClauseAuditD ν hν) :
    ClayOptionD := by
  intro ν hν
  let w := h ν hν
  exact ⟨w.initialVelocity, w.forcing,
    ⟨w.initialSmooth, w.initialDivergenceFree, w.initialPeriodic,
      w.forcingSmooth, w.forcingPeriodic,
      w.forcingRapidTimeDecayAllDerivatives⟩,
    w.noGlobalSmoothPeriodicSolution⟩

theorem literalClayC_roundTrip : ClayOptionC :=
  ClayOptionC_of_clauseAudits literalClayC_clauseAudit

theorem literalClayD_roundTrip : ClayOptionD :=
  ClayOptionD_of_clauseAudits literalClayD_clauseAudit

/-- The Clay-facing status split: C/D are actual source-backed theorem terms;
A/B stay named as independent original-analysis targets. -/
structure ClayFacingStatus : Prop where
  sourceBackedC : ClayOptionC
  sourceBackedD : ClayOptionD

theorem currentClayFacingStatus : ClayFacingStatus :=
  ⟨literalClayC_roundTrip, literalClayD_roundTrip⟩

#print axioms literalClayC_clauseAudit
#print axioms literalClayD_clauseAudit
#print axioms literalClayC_roundTrip
#print axioms literalClayD_roundTrip
#print axioms currentClayFacingStatus

end DASHILiteralClayNS
