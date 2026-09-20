import ClaySpec
import LiteralABCD

/-!
# Agda-facing concrete semantic contract for literal Clay A/B/C/D

This file freezes the exact Mathlib/ClaySpec meanings behind the Agda
NSConcreteFeffermanSemanticsExact contract.

Agda represents histories as time-first functions
  Time → R3 → ...
whereas ClaySpec represents them on SpaceTime = R3 × ℝ.  The conversions below
are explicit bijections, and every semantic predicate is defined by transport
through those conversions.  This gives the cross-prover reconstruction lane a
single theorem-level target instead of a list of prose correspondences.
-/

noncomputable section

open MeasureTheory Set
open ClaySpec

namespace AgdaConcreteClayContract

abbrev Time := ℝ
abbrev R3Point := R3
abbrev R3Vector := R3

abbrev SpatialVectorField := R3Point → R3Vector
abbrev SpatialScalarField := R3Point → ℝ
abbrev VelocityHistory := Time → SpatialVectorField
abbrev PressureHistory := Time → SpatialScalarField
abbrev ForcingHistory := Time → SpatialVectorField

def toVelocity (u : VelocityHistory) : ClaySpec.Velocity :=
  fun z => u z.2 z.1

def fromVelocity (u : ClaySpec.Velocity) : VelocityHistory :=
  fun t x => u (x, t)

def toPressure (p : PressureHistory) : ClaySpec.Pressure :=
  fun z => p z.2 z.1

def fromPressure (p : ClaySpec.Pressure) : PressureHistory :=
  fun t x => p (x, t)

def toForce (f : ForcingHistory) : ClaySpec.Force :=
  fun z => f z.2 z.1

def fromForce (f : ClaySpec.Force) : ForcingHistory :=
  fun t x => f (x, t)

@[simp] theorem from_to_velocity (u : VelocityHistory) :
    fromVelocity (toVelocity u) = u := by
  funext t x
  rfl

@[simp] theorem to_from_velocity (u : ClaySpec.Velocity) :
    toVelocity (fromVelocity u) = u := by
  funext z
  rcases z with ⟨x,t⟩
  rfl

@[simp] theorem from_to_pressure (p : PressureHistory) :
    fromPressure (toPressure p) = p := by
  funext t x
  rfl

@[simp] theorem to_from_pressure (p : ClaySpec.Pressure) :
    toPressure (fromPressure p) = p := by
  funext z
  rcases z with ⟨x,t⟩
  rfl

@[simp] theorem from_to_force (f : ForcingHistory) :
    fromForce (toForce f) = f := by
  funext t x
  rfl

@[simp] theorem to_from_force (f : ClaySpec.Force) :
    toForce (fromForce f) = f := by
  funext z
  rcases z with ⟨x,t⟩
  rfl

def PositiveReal (ν : ℝ) : Prop := 0 < ν
def NonnegativeTime (t : Time) : Prop := 0 ≤ t

def SmoothSpatialVector (u₀ : SpatialVectorField) : Prop :=
  ContDiff ℝ ∞ u₀

def SmoothVelocityHistory (u : VelocityHistory) : Prop :=
  ClaySpec.TrustBoundarySmoothOn (toVelocity u)

def SmoothPressureHistory (p : PressureHistory) : Prop :=
  ClaySpec.TrustBoundarySmoothOn (toPressure p)

def SmoothForcingHistory (f : ForcingHistory) : Prop :=
  ClaySpec.TrustBoundarySmoothOn (toForce f)

def DivergenceFreeSpatial (u₀ : SpatialVectorField) : Prop :=
  ClaySpec.InitialDivergenceFree u₀

def DivergenceFreeHistory (u : VelocityHistory) : Prop :=
  ClaySpec.EquationTwo (toVelocity u)

def RapidSpatialDecay (u₀ : SpatialVectorField) : Prop :=
  ClaySpec.InitialRapidDecay u₀

def RapidSpaceTimeDecay (f : ForcingHistory) : Prop :=
  ClaySpec.ForceRapidDecayR3 (toForce f)

def BoundedKineticEnergy (u : VelocityHistory) : Prop :=
  ClaySpec.BoundedEnergy (toVelocity u)

def UnitPeriodicSpatialVector (u₀ : SpatialVectorField) : Prop :=
  ClaySpec.SpatiallyPeriodicInitial u₀

def UnitPeriodicVelocity (u : VelocityHistory) : Prop :=
  ClaySpec.SpatiallyPeriodic (toVelocity u)

def UnitPeriodicPressure (p : PressureHistory) : Prop :=
  ClaySpec.SpatiallyPeriodic (toPressure p)

def UnitPeriodicForcing (f : ForcingHistory) : Prop :=
  ClaySpec.SpatiallyPeriodic (toForce f)

def RapidTimeDecayAllForcingDerivatives (f : ForcingHistory) : Prop :=
  ClaySpec.ForceRapidDecayPeriodic (toForce f)

def AttainsInitialDatum
    (u : VelocityHistory) (u₀ : SpatialVectorField) : Prop :=
  ClaySpec.EquationThree u₀ (toVelocity u)

def SolvesForcedNS
    (ν : ℝ) (u : VelocityHistory) (p : PressureHistory)
    (_u₀ : SpatialVectorField) (f : ForcingHistory) : Prop :=
  ClaySpec.EquationOne ν (toVelocity u) (toPressure p) (toForce f)

def zeroForcing : ForcingHistory := fun _ _ => 0

def SolvesUnforcedNS
    (ν : ℝ) (u : VelocityHistory) (p : PressureHistory)
    (u₀ : SpatialVectorField) : Prop :=
  SolvesForcedNS ν u p u₀ zeroForcing

structure EuclideanGlobalSolution
    (ν : ℝ) (u₀ : SpatialVectorField) : Prop where
  velocity : VelocityHistory
  pressure : PressureHistory
  velocitySmooth : SmoothVelocityHistory velocity
  pressureSmooth : SmoothPressureHistory pressure
  solvesMomentumEquation : SolvesUnforcedNS ν velocity pressure u₀
  incompressible : DivergenceFreeHistory velocity
  initialTrace : AttainsInitialDatum velocity u₀
  boundedEnergy : BoundedKineticEnergy velocity

structure EuclideanForcedGlobalSolution
    (ν : ℝ) (u₀ : SpatialVectorField) (f : ForcingHistory) : Prop where
  velocity : VelocityHistory
  pressure : PressureHistory
  velocitySmooth : SmoothVelocityHistory velocity
  pressureSmooth : SmoothPressureHistory pressure
  solvesEquation : SolvesForcedNS ν velocity pressure u₀ f
  incompressible : DivergenceFreeHistory velocity
  initialTrace : AttainsInitialDatum velocity u₀
  boundedEnergy : BoundedKineticEnergy velocity

structure PeriodicForcedGlobalSolution
    (ν : ℝ) (u₀ : SpatialVectorField) (f : ForcingHistory) : Prop where
  velocity : VelocityHistory
  pressure : PressureHistory
  velocitySmooth : SmoothVelocityHistory velocity
  pressureSmooth : SmoothPressureHistory pressure
  velocityPeriodic : UnitPeriodicVelocity velocity
  pressurePeriodic : UnitPeriodicPressure pressure
  solvesEquation : SolvesForcedNS ν velocity pressure u₀ f
  incompressible : DivergenceFreeHistory velocity
  initialTrace : AttainsInitialDatum velocity u₀

def AgdaStyleClayOptionA : Prop :=
  ∀ ν : ℝ, PositiveReal ν →
    ∀ u₀ : SpatialVectorField,
      SmoothSpatialVector u₀ →
      DivergenceFreeSpatial u₀ →
      RapidSpatialDecay u₀ →
      EuclideanGlobalSolution ν u₀

def AgdaStyleClayOptionB : Prop :=
  ∀ ν : ℝ, PositiveReal ν →
    ∀ u₀ : SpatialVectorField,
      SmoothSpatialVector u₀ →
      DivergenceFreeSpatial u₀ →
      UnitPeriodicSpatialVector u₀ →
      ∃ u : VelocityHistory, ∃ p : PressureHistory,
        SmoothVelocityHistory u ∧
        SmoothPressureHistory p ∧
        UnitPeriodicVelocity u ∧
        UnitPeriodicPressure p ∧
        SolvesUnforcedNS ν u p u₀ ∧
        DivergenceFreeHistory u ∧
        AttainsInitialDatum u u₀

def AgdaStyleClayOptionC : Prop :=
  ∀ ν : ℝ, PositiveReal ν →
    ∃ u₀ : SpatialVectorField, ∃ f : ForcingHistory,
      SmoothSpatialVector u₀ ∧
      DivergenceFreeSpatial u₀ ∧
      RapidSpatialDecay u₀ ∧
      SmoothForcingHistory f ∧
      RapidSpaceTimeDecay f ∧
      ¬ EuclideanForcedGlobalSolution ν u₀ f

def AgdaStyleClayOptionD : Prop :=
  ∀ ν : ℝ, PositiveReal ν →
    ∃ u₀ : SpatialVectorField, ∃ f : ForcingHistory,
      SmoothSpatialVector u₀ ∧
      DivergenceFreeSpatial u₀ ∧
      UnitPeriodicSpatialVector u₀ ∧
      SmoothForcingHistory f ∧
      UnitPeriodicForcing f ∧
      RapidTimeDecayAllForcingDerivatives f ∧
      ¬ PeriodicForcedGlobalSolution ν u₀ f

theorem euclideanGlobalSolution_iff_claySolutionR3
    (ν : ℝ) (u₀ : SpatialVectorField) :
    (∃ s : EuclideanGlobalSolution ν u₀, True) ↔
      ∃ u : ClaySpec.Velocity, ∃ p : ClaySpec.Pressure,
        ClaySpec.ClaySolutionR3 ν u₀ (fun _ => 0) u p := by
  constructor
  · rintro ⟨s, -⟩
    refine ⟨toVelocity s.velocity, toPressure s.pressure, ?_⟩
    exact ⟨s.velocitySmooth, s.pressureSmooth, s.solvesMomentumEquation,
      s.incompressible, s.initialTrace, s.boundedEnergy⟩
  · rintro ⟨u,p,h⟩
    rcases h with ⟨hu,hp,heq,hdiv,hinit,henergy⟩
    refine ⟨{
      velocity := fromVelocity u
      pressure := fromPressure p
      velocitySmooth := by simpa [SmoothVelocityHistory]
      pressureSmooth := by simpa [SmoothPressureHistory]
      solvesMomentumEquation := by
        simpa [SolvesUnforcedNS, SolvesForcedNS, zeroForcing, toForce]
      incompressible := by simpa [DivergenceFreeHistory]
      initialTrace := by simpa [AttainsInitialDatum]
      boundedEnergy := by simpa [BoundedKineticEnergy]
    }, trivial⟩


theorem AgdaStyleClayOptionA_iff_Literal :
    AgdaStyleClayOptionA ↔ DASHILiteralClayNS.ClayOptionA := by
  constructor
  · intro h ν hν u₀ hdata
    obtain s := h ν hν u₀ hdata.1 hdata.2.1 hdata.2.2
    refine ⟨toVelocity s.velocity, toPressure s.pressure, ?_⟩
    exact ⟨s.velocitySmooth, s.pressureSmooth, s.solvesMomentumEquation,
      s.incompressible, s.initialTrace, s.boundedEnergy⟩
  · intro h ν hν u₀ hs hd hr
    obtain ⟨u,p,hsol⟩ := h ν hν u₀ ⟨hs,hd,hr⟩
    rcases hsol with ⟨hu,hp,heq,hdiv,hinit,henergy⟩
    exact {
      velocity := fromVelocity u
      pressure := fromPressure p
      velocitySmooth := by simpa [SmoothVelocityHistory]
      pressureSmooth := by simpa [SmoothPressureHistory]
      solvesMomentumEquation := by
        simpa [SolvesUnforcedNS, SolvesForcedNS, zeroForcing, toForce]
      incompressible := by simpa [DivergenceFreeHistory]
      initialTrace := by simpa [AttainsInitialDatum]
      boundedEnergy := by simpa [BoundedKineticEnergy]
    }

theorem AgdaStyleClayOptionB_iff_Literal :
    AgdaStyleClayOptionB ↔ DASHILiteralClayNS.ClayOptionB := by
  constructor
  · intro h ν hν u₀ hdata
    obtain ⟨u,p,hu,hp,huper,hpper,heq,hdiv,hinit⟩ :=
      h ν hν u₀ hdata.1 hdata.2.1 hdata.2.2
    refine ⟨toVelocity u, toPressure p, ?_⟩
    exact ⟨hu,hp,heq,hdiv,hinit,huper,hpper⟩
  · intro h ν hν u₀ hs hd hper
    obtain ⟨u,p,hsol⟩ := h ν hν u₀ ⟨hs,hd,hper⟩
    rcases hsol with ⟨hu,hp,heq,hdiv,hinit,huper,hpper⟩
    refine ⟨fromVelocity u, fromPressure p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [SmoothVelocityHistory]
    · simpa [SmoothPressureHistory]
    · simpa [UnitPeriodicVelocity]
    · simpa [UnitPeriodicPressure]
    · simpa [SolvesUnforcedNS, SolvesForcedNS, zeroForcing, toForce]
    · simpa [DivergenceFreeHistory]
    · simpa [AttainsInitialDatum]

theorem AgdaStyleClayOptionC_iff_ClaySpec :
    AgdaStyleClayOptionC ↔ ClaySpec.ClayOptionC := by
  constructor
  · intro h ν hν
    obtain ⟨u₀,f,hs,hd,hr,hfs,hfr,hno⟩ := h ν hν
    refine ⟨u₀, toForce f, ⟨hs,hd,hr,hfs,hfr⟩, ?_⟩
    rintro ⟨u,p,hsol⟩
    apply hno
    refine {
      velocity := fromVelocity u
      pressure := fromPressure p
      velocitySmooth := by simpa [SmoothVelocityHistory] using hsol.1
      pressureSmooth := by simpa [SmoothPressureHistory] using hsol.2.1
      solvesEquation := by
        simpa [SolvesForcedNS] using hsol.2.2.1
      incompressible := by
        simpa [DivergenceFreeHistory] using hsol.2.2.2.1
      initialTrace := by
        simpa [AttainsInitialDatum] using hsol.2.2.2.2.1
      boundedEnergy := by
        simpa [BoundedKineticEnergy] using hsol.2.2.2.2.2
    }
  · intro h ν hν
    obtain ⟨u₀,f,hdata,hno⟩ := h ν hν
    refine ⟨u₀, fromForce f, hdata.1, hdata.2.1, hdata.2.2.1,
      hdata.2.2.2.1, ?_, ?_⟩
    · simpa [RapidSpaceTimeDecay] using hdata.2.2.2.2
    · intro s
      apply hno
      refine ⟨toVelocity s.velocity, toPressure s.pressure, ?_⟩
      exact ⟨s.velocitySmooth, s.pressureSmooth, s.solvesEquation,
        s.incompressible, s.initialTrace, s.boundedEnergy⟩

theorem AgdaStyleClayOptionD_iff_ClaySpec :
    AgdaStyleClayOptionD ↔ ClaySpec.ClayOptionD := by
  constructor
  · intro h ν hν
    obtain ⟨u₀,f,hs,hd,hper,hfs,hfper,hdec,hno⟩ := h ν hν
    refine ⟨u₀, toForce f, ⟨hs,hd,hper,hfs,hfper,hdec⟩, ?_⟩
    rintro ⟨u,p,hsol⟩
    apply hno
    refine {
      velocity := fromVelocity u
      pressure := fromPressure p
      velocitySmooth := by simpa [SmoothVelocityHistory] using hsol.1
      pressureSmooth := by simpa [SmoothPressureHistory] using hsol.2.1
      velocityPeriodic := by
        simpa [UnitPeriodicVelocity] using hsol.2.2.2.2.2.1
      pressurePeriodic := by
        simpa [UnitPeriodicPressure] using hsol.2.2.2.2.2.2
      solvesEquation := by
        simpa [SolvesForcedNS] using hsol.2.2.1
      incompressible := by
        simpa [DivergenceFreeHistory] using hsol.2.2.2.1
      initialTrace := by
        simpa [AttainsInitialDatum] using hsol.2.2.2.2.1
    }
  · intro h ν hν
    obtain ⟨u₀,f,hdata,hno⟩ := h ν hν
    refine ⟨u₀, fromForce f, hdata.1, hdata.2.1, hdata.2.2.1,
      hdata.2.2.2.1, ?_, ?_, ?_⟩
    · simpa [UnitPeriodicForcing] using hdata.2.2.2.2.2.1
    · simpa [RapidTimeDecayAllForcingDerivatives] using hdata.2.2.2.2.2.2
    · intro s
      apply hno
      refine ⟨toVelocity s.velocity, toPressure s.pressure, ?_⟩
      exact ⟨s.velocitySmooth, s.pressureSmooth, s.solvesEquation,
        s.incompressible, s.initialTrace, s.velocityPeriodic, s.pressurePeriodic⟩

theorem literalClayC_agdaContract : AgdaStyleClayOptionC :=
  AgdaStyleClayOptionC_iff_ClaySpec.mpr
    DASHILiteralClayNS.literalClayC

theorem literalClayD_agdaContract : AgdaStyleClayOptionD :=
  AgdaStyleClayOptionD_iff_ClaySpec.mpr
    DASHILiteralClayNS.literalClayD

theorem literalAnyOneViaAgdaContractC :
    DASHILiteralClayNS.AnyOneClayResolution :=
  DASHILiteralClayNS.AnyOneClayResolution.resolvedC
    (AgdaStyleClayOptionC_iff_ClaySpec.mp literalClayC_agdaContract)

theorem literalAnyOneViaAgdaContractD :
    DASHILiteralClayNS.AnyOneClayResolution :=
  DASHILiteralClayNS.AnyOneClayResolution.resolvedD
    (AgdaStyleClayOptionD_iff_ClaySpec.mp literalClayD_agdaContract)

#print axioms AgdaStyleClayOptionA_iff_Literal
#print axioms AgdaStyleClayOptionB_iff_Literal
#print axioms AgdaStyleClayOptionC_iff_ClaySpec
#print axioms AgdaStyleClayOptionD_iff_ClaySpec
#print axioms literalClayC_agdaContract
#print axioms literalClayD_agdaContract

end AgdaConcreteClayContract
