import Mathlib
import Integration.JInvariant369ConsolidatedNextStage

namespace Integration.JInvariant369ZeroToThirteenTetralemmaQualification

open Integration.JInvariant369ConsolidatedNextStage
open Integration.StageTwelveGrothendieckRelation

/-! Finite Lean mirror of the broader 0..13 / tetralemma / sixfold layer. -/

inductive Rank013
  | r0 | r1 | r2 | r3 | r4 | r5 | r6
  | r7 | r8 | r9 | r10 | r11 | r12 | r13
  deriving DecidableEq, Repr

def rankToNat : Rank013 → Nat
  | .r0 => 0 | .r1 => 1 | .r2 => 2 | .r3 => 3
  | .r4 => 4 | .r5 => 5 | .r6 => 6 | .r7 => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13

def ternaryDigits013 : Rank013 → Nat × Nat × Nat
  | .r0 => (0,0,0) | .r1 => (1,0,0) | .r2 => (2,0,0)
  | .r3 => (0,1,0) | .r4 => (1,1,0) | .r5 => (2,1,0)
  | .r6 => (0,2,0) | .r7 => (1,2,0) | .r8 => (2,2,0)
  | .r9 => (0,0,1) | .r10 => (1,0,1) | .r11 => (2,0,1)
  | .r12 => (0,1,1) | .r13 => (1,1,1)

def ternaryPlaceValue (d : Nat × Nat × Nat) : Nat :=
  d.1 + 3*d.2.1 + 9*d.2.2

theorem ternary013_exact (r : Rank013) :
    ternaryPlaceValue (ternaryDigits013 r) = rankToNat r := by
  cases r <;> norm_num [ternaryPlaceValue, ternaryDigits013, rankToNat]

theorem rank12_is_110 :
    ternaryDigits013 .r12 = (0,1,1) := rfl

theorem rank13_is_111 :
    ternaryDigits013 .r13 = (1,1,1) := rfl

theorem rank12_three_plus_nine : 12 = 3 + 9 := by norm_num
theorem rank13_one_plus_three_plus_nine : 13 = 1 + 3 + 9 := by norm_num
theorem rank12_profiles : 3^12 = 531441 := by norm_num
theorem rank13_profiles : 3^13 = 1594323 := by norm_num

inductive StageRole
  | root | unit | relationOpened | localClosure
  | tetralemmaInterpolation | decisionGate | reflexiveClosure
  | orbitProliferation | gluingResidual | systemicClosure
  | scalePromoted | crossScaleFresh | relationOpenedAtScale
  deriving DecidableEq, Repr

def stageRole (s : Fin 13) : StageRole :=
  match s.val with
  | 0 => .root
  | 1 => .unit
  | 2 => .relationOpened
  | 3 => .localClosure
  | 4 => .tetralemmaInterpolation
  | 5 => .decisionGate
  | 6 => .reflexiveClosure
  | 7 => .orbitProliferation
  | 8 => .gluingResidual
  | 9 => .systemicClosure
  | 10 => .scalePromoted
  | 11 => .crossScaleFresh
  | 12 => .relationOpenedAtScale
  | _ => .root

theorem stage4_tetralemma :
    stageRole (4 : Fin 13) = .tetralemmaInterpolation := rfl
theorem stage6_reflexive :
    stageRole (6 : Fin 13) = .reflexiveClosure := rfl
theorem stage9_systemic :
    stageRole (9 : Fin 13) = .systemicClosure := rfl
theorem stage12_relation_at_scale :
    stageRole (12 : Fin 13) = .relationOpenedAtScale := rfl

inductive SupportBit | unsupported | supported
  deriving DecidableEq, Repr

structure SupportSquare where
  support : SupportBit
  counterSupport : SupportBit
  deriving DecidableEq, Repr

inductive TetralemmaPosition
  | positionOnly | counterpositionOnly | bothSupported | neitherEstablished
  deriving DecidableEq, Repr

def classifySupportSquare : SupportSquare → TetralemmaPosition
  | ⟨.supported, .unsupported⟩ => .positionOnly
  | ⟨.unsupported, .supported⟩ => .counterpositionOnly
  | ⟨.supported, .supported⟩ => .bothSupported
  | ⟨.unsupported, .unsupported⟩ => .neitherEstablished

inductive SixfoldStatus
  | affirmed | denied | affirmedAndDenied | inexpressible
  | underdetermined | scopeExceeded
  deriving DecidableEq, Repr

structure QualifiedCarrier (Carrier : Type) where
  retained : Carrier
  support : SupportSquare
  position : TetralemmaPosition
  positionExact : position = classifySupportSquare support
  sixfold : SixfoldStatus

theorem qualification_retains_carrier {Carrier : Type}
    (x : Carrier) (s : SupportSquare) (status : SixfoldStatus) :
    (QualifiedCarrier.mk x s (classifySupportSquare s) rfl status).retained = x := rfl

structure QualifiedConsolidated369State (Base : Type) where
  consolidated : Consolidated369State Base
  rank : Rank013
  stage : Fin 13
  logical : QualifiedCarrier (Fin 27)

theorem qualification_does_not_rewrite_state {Base : Type}
    (x : Consolidated369State Base) (r : Rank013) (s : Fin 13)
    (q : QualifiedCarrier (Fin 27)) :
    (QualifiedConsolidated369State.mk x r s q).consolidated = x := rfl

inductive Rank12EqualsStage12SemanticIdentity : Prop
inductive TetralemmaEqualsTernary27Carrier : Prop
inductive SixfoldEqualsModularPhase6 : Prop
inductive Rank13CreatesStage13Semantics : Prop

theorem rank12_not_stage12_identity :
    ¬ Rank12EqualsStage12SemanticIdentity := by intro h; cases h
theorem tetralemma_not_ternary27 :
    ¬ TetralemmaEqualsTernary27Carrier := by intro h; cases h
theorem sixfold_not_phase6 :
    ¬ SixfoldEqualsModularPhase6 := by intro h; cases h
theorem rank13_not_stage13_semantics :
    ¬ Rank13CreatesStage13Semantics := by intro h; cases h

structure Boundary where
  exactRows0to13 : Bool
  rank12Address110 : Bool
  rank13Address111 : Bool
  rank12Profiles531441 : Bool
  rank13Profiles1594323 : Bool
  stage4TetralemmaRole : Bool
  stage6ReflexiveRole : Bool
  stage9SystemicRole : Bool
  stage12RelationRole : Bool
  tetralemmaRetainsCarrier : Bool
  sixfoldRetainsTetralemmaLayer : Bool
  qualificationRetainsConsolidatedState : Bool
  rank12EqualsStage12ByMeaning : Bool
  tetralemmaEqualsTernaryCarrier : Bool
  sixfoldEqualsModularPhase6 : Bool
  rank13CreatesStage13Semantics : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exactRows0to13 := true
  rank12Address110 := true
  rank13Address111 := true
  rank12Profiles531441 := true
  rank13Profiles1594323 := true
  stage4TetralemmaRole := true
  stage6ReflexiveRole := true
  stage9SystemicRole := true
  stage12RelationRole := true
  tetralemmaRetainsCarrier := true
  sixfoldRetainsTetralemmaLayer := true
  qualificationRetainsConsolidatedState := true
  rank12EqualsStage12ByMeaning := false
  tetralemmaEqualsTernaryCarrier := false
  sixfoldEqualsModularPhase6 := false
  rank13CreatesStage13Semantics := false

end Integration.JInvariant369ZeroToThirteenTetralemmaQualification
