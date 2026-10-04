import Integration.OggSSP2BM22CompletionTenCandidate

/-!
# M22:2 outer-involution Completion10 runtime receipt

This mirrors the executed DASHI AtlasRep screen for the actual characteristic-two
10-dimensional M22:2 modules.

Finite result:
* both 10-dimensional M22:2 modules restrict to the actual M22 10a/10b modules;
* in each module an outer involution class has class size 1386 and centralizer
  order 640;
* rank(g-I)=5 and dim Fix(g)=5;
* a literal basis of five swapped pairs spans all ten dimensions;
* there are exactly two such module/class matches.

Semantic boundary: this is a finite-module fact.  It does not identify either
module as an actual subquotient of the 2B Tate fibre and does not identify the
outer involution with the action on that actual Tate subquotient.
-/

namespace Integration.OggSSP2BM22d2Completion10RuntimeReceipt

namespace C := Integration.OggSSP2BM22CompletionTenCandidate

inductive M22d2TenModuleKind
  | tenA
  | tenB
  deriving DecidableEq, Repr, Fintype

structure OuterCompletionCandidate where
  moduleKind : M22d2TenModuleKind
  restrictsToActualM22Ten : Bool
  involutionIsOuter : Bool
  classSize : ℕ
  centralizerOrder : ℕ
  rankGMinusI : ℕ
  fixedDimension : ℕ
  fiveSwapPairsVerified : Bool
  tenVectorsSpanWholeModule : Bool
  deriving Repr

def tenAOuterCompletionCandidate : OuterCompletionCandidate where
  moduleKind := .tenA
  restrictsToActualM22Ten := true
  involutionIsOuter := true
  classSize := 1386
  centralizerOrder := 640
  rankGMinusI := 5
  fixedDimension := 5
  fiveSwapPairsVerified := true
  tenVectorsSpanWholeModule := true

def tenBOuterCompletionCandidate : OuterCompletionCandidate where
  moduleKind := .tenB
  restrictsToActualM22Ten := true
  involutionIsOuter := true
  classSize := 1386
  centralizerOrder := 640
  rankGMinusI := 5
  fixedDimension := 5
  fiveSwapPairsVerified := true
  tenVectorsSpanWholeModule := true

abbrev outerJ2x5MatchCount : ℕ := 2

theorem outerJ2x5MatchCount_is_two : outerJ2x5MatchCount = 2 := rfl

theorem tenA_has_J2x5_fingerprint :
    tenAOuterCompletionCandidate.rankGMinusI = 5 ∧
    tenAOuterCompletionCandidate.fixedDimension = 5 := by
  decide

theorem tenB_has_J2x5_fingerprint :
    tenBOuterCompletionCandidate.rankGMinusI = 5 ∧
    tenBOuterCompletionCandidate.fixedDimension = 5 := by
  decide

theorem both_runtime_candidates_have_literal_five_pair_basis :
    tenAOuterCompletionCandidate.fiveSwapPairsVerified = true ∧
    tenBOuterCompletionCandidate.fiveSwapPairsVerified = true := by
  decide

structure RuntimeStatus where
  finiteCompletionPhaseCandidatePaid : Bool
  actualTwoBTateSubquotientIdentified : Bool
  actualTateActionIntertwinerIdentified : Bool
  deriving Repr

def canonicalRuntimeStatus : RuntimeStatus where
  finiteCompletionPhaseCandidatePaid := true
  actualTwoBTateSubquotientIdentified := false
  actualTateActionIntertwinerIdentified := false

/-- Promotion firewall: the finite J2^5 receipt is not itself the missing
same-object Tate identification. -/
inductive FiniteJ2x5ConstructsActualTateAction : Prop

theorem finite_J2x5_does_not_construct_actual_Tate_action :
    ¬ FiniteJ2x5ConstructsActualTateAction := by
  intro h
  cases h

end Integration.OggSSP2BM22d2Completion10RuntimeReceipt
