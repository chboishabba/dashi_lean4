import AgdaMirror.Dynamics.SingularBasinReduction

namespace AgdaMirror.Dynamics.SingularBasinFiniteWitness

open AgdaMirror.Dynamics.SingularBasinReduction
namespace NF := AgdaMirror.IntersectionalNonFactorability

inductive FullState where
  | target
  | funnel
  | outside
  deriving DecidableEq, Repr

inductive ReducedState where
  | target
  | other
  deriving DecidableEq, Repr

open FullState ReducedState

def project : FullState → ReducedState
  | .target => .target
  | .funnel => .other
  | .outside => .other

def fullInBasin : FullState → Prop
  | .target => True
  | .funnel => True
  | .outside => False

def reducedInBasin : ReducedState → Prop
  | .target => True
  | .other => False

def finiteReduction : BasinReduction FullState ReducedState :=
  { project := project
    fullInBasin := fullInBasin
    reducedInBasin := reducedInBasin }

def finiteFailure : BasinReductionFailure finiteReduction :=
  { witness := .funnel
    fullMember := trivial
    reducedExcluded := by simp [finiteReduction, reducedInBasin, project] }

theorem finiteReduction_not_preserving :
    ¬ BasinPreserving finiteReduction :=
  failure_refutes_preservation finiteFailure

def finiteCollision : BasinProjectionCollision finiteReduction :=
  { inside := .funnel
    outside := .outside
    sameReducedState := rfl
    insideFullBasin := trivial
    outsideFullBasin := by simp [finiteReduction, fullInBasin] }

theorem finiteFullBasin_not_factors_through_projection :
    ¬ NF.FactorsThrough
      finiteReduction.project
      (fun x => decide (finiteReduction.fullInBasin x)) :=
  basin_collision_refutes_factorisation finiteCollision

end AgdaMirror.Dynamics.SingularBasinFiniteWitness
