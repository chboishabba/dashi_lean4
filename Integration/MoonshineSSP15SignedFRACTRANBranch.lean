import Integration.MoonshineNeutralCuspRelationCrossPollination
import Mathlib

namespace Integration.MoonshineSSP15SignedFRACTRANBranch

open Integration.MoonshineNeutralCuspRelationCrossPollination

inductive SSPPrime
  | p2 | p3 | p5 | p7 | p11 | p13 | p17 | p19 | p23 | p29 | p31 | p41 | p47 | p59 | p71
  deriving DecidableEq, Repr

abbrev InternalLane := Mode5 × BalancedPhase

def primeToInternal : SSPPrime → InternalLane
  | .p2 => (.m09,.negative)
  | .p3 => (.m09,.zero)
  | .p5 => (.m09,.positive)
  | .p7 => (.m18,.negative)
  | .p11 => (.m18,.zero)
  | .p13 => (.m18,.positive)
  | .p17 => (.m27,.negative)
  | .p19 => (.m27,.zero)
  | .p23 => (.m27,.positive)
  | .p29 => (.m36,.negative)
  | .p31 => (.m36,.zero)
  | .p41 => (.m36,.positive)
  | .p47 => (.m45,.negative)
  | .p59 => (.m45,.zero)
  | .p71 => (.m45,.positive)

def internalToPrime : InternalLane → SSPPrime
  | (.m09,.negative) => .p2
  | (.m09,.zero) => .p3
  | (.m09,.positive) => .p5
  | (.m18,.negative) => .p7
  | (.m18,.zero) => .p11
  | (.m18,.positive) => .p13
  | (.m27,.negative) => .p17
  | (.m27,.zero) => .p19
  | (.m27,.positive) => .p23
  | (.m36,.negative) => .p29
  | (.m36,.zero) => .p31
  | (.m36,.positive) => .p41
  | (.m45,.negative) => .p47
  | (.m45,.zero) => .p59
  | (.m45,.positive) => .p71

theorem internal_prime_roundtrip (p : SSPPrime) :
    internalToPrime (primeToInternal p) = p := by cases p <;> rfl

theorem prime_internal_roundtrip (l : InternalLane) :
    primeToInternal (internalToPrime l) = l := by
  rcases l with ⟨m,p⟩
  cases m <;> cases p <;> rfl

inductive SignedMultiplicity
  | neg (magnitude : Nat)
  | zero
  | pos (magnitude : Nat)
  deriving DecidableEq, Repr

def phaseToUnitMultiplicity : BalancedPhase → SignedMultiplicity
  | .negative => .neg 1
  | .zero => .zero
  | .positive => .pos 1

def coarseMultiplicity : SignedMultiplicity → BalancedPhase
  | .neg _ => .negative
  | .zero => .zero
  | .pos _ => .positive

theorem phase_coarse_roundtrip (p : BalancedPhase) :
    coarseMultiplicity (phaseToUnitMultiplicity p) = p := by
  cases p <;> rfl

structure PointedSignedLane where
  selectedPrime : SSPPrime
  signedMultiplicity : SignedMultiplicity
  deriving Repr

def internalToPointed : InternalLane → PointedSignedLane
  | l => ⟨internalToPrime l, phaseToUnitMultiplicity l.2⟩

def pointedToCoarseInternal : PointedSignedLane → InternalLane
  | s =>
      let l := primeToInternal s.selectedPrime
      (l.1, coarseMultiplicity s.signedMultiplicity)

theorem internal_pointed_coarse_roundtrip (l : InternalLane) :
    pointedToCoarseInternal (internalToPointed l) = l := by
  rcases l with ⟨m,p⟩
  cases m <;> cases p <;> rfl

abbrev SSPValuation := SSPPrime → SignedMultiplicity

def pointedValuation (s : PointedSignedLane) : SSPValuation :=
  fun p => if p = s.selectedPrime then s.signedMultiplicity else .zero

theorem pointed_valuation_own_lane (s : PointedSignedLane) :
    pointedValuation s s.selectedPrime = s.signedMultiplicity := by
  simp [pointedValuation]

def neutralPointed (p : SSPPrime) : PointedSignedLane := ⟨p,.zero⟩

theorem neutral_valuation_is_zero (selected observed : SSPPrime) :
    pointedValuation (neutralPointed selected) observed = .zero := by
  simp [pointedValuation, neutralPointed]
  split <;> rfl

theorem neutral_p2_p3_same_valuation :
    pointedValuation (neutralPointed .p2) =
      pointedValuation (neutralPointed .p3) := by
  funext p
  simp [pointedValuation, neutralPointed]
  split <;> split <;> rfl

theorem selected_neutral_lane_not_recoverable_from_valuation :
    ¬ Function.Injective (fun p : SSPPrime => pointedValuation (neutralPointed p)) := by
  intro h
  have hp := h neutral_p2_p3_same_valuation
  cases hp

inductive WeaveInstruction
  | introducePrime (p : SSPPrime)
  | introduceInversePrime (p : SSPPrime)
  | introduceInvariantUnit
  | refineAt369
  deriving DecidableEq, Repr

structure WeaveEffect where
  positivePrimeTokens : Nat
  inversePrimeTokens : Nat
  invariantTokens : Nat
  refinementSteps : Nat
  deriving DecidableEq, Repr

def emptyEffect : WeaveEffect := ⟨0,0,0,0⟩

def applyInstruction : WeaveInstruction → WeaveEffect → WeaveEffect
  | .introducePrime _, e => {e with positivePrimeTokens := e.positivePrimeTokens + 1}
  | .introduceInversePrime _, e => {e with inversePrimeTokens := e.inversePrimeTokens + 1}
  | .introduceInvariantUnit, e => {e with invariantTokens := e.invariantTokens + 1}
  | .refineAt369, e => {e with refinementSteps := e.refinementSteps + 1}

def executeProgram : List WeaveInstruction → WeaveEffect
  | [] => emptyEffect
  | i::rest => rest.foldl (fun e j => applyInstruction j e) (applyInstruction i emptyEffect)

structure PointedSignedFRACTRANSeed where
  pointedLane : PointedSignedLane
  valuation : SSPValuation
  valuationMatches : valuation = pointedValuation pointedLane
  program : List WeaveInstruction

def seedFromInternal (l : InternalLane) (program : List WeaveInstruction) :
    PointedSignedFRACTRANSeed :=
  ⟨internalToPointed l, pointedValuation (internalToPointed l), rfl, program⟩

def executeSeed (s : PointedSignedFRACTRANSeed) : WeaveEffect :=
  executeProgram s.program

inductive ChosenCarrierBijectionIsSemanticIdentity : Prop

theorem chosen_bijection_not_semantic_identity :
    ¬ ChosenCarrierBijectionIsSemanticIdentity := by
  intro h; cases h

structure Boundary where
  fiveTimesThreeInternalCarrierPaid : Bool
  chosenFifteenToFifteenBijectionPaid : Bool
  chosenBijectionSemanticIdentity : Bool
  pointedNeutralSupportRetained : Bool
  fullValuationCompilationPaid : Bool
  valuationAloneRecoversNeutralLane : Bool
  fractranInstructionLanguageMirrored : Bool
  seedExecutionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fiveTimesThreeInternalCarrierPaid := true
  chosenFifteenToFifteenBijectionPaid := true
  chosenBijectionSemanticIdentity := false
  pointedNeutralSupportRetained := true
  fullValuationCompilationPaid := true
  valuationAloneRecoversNeutralLane := false
  fractranInstructionLanguageMirrored := true
  seedExecutionPaid := true

end Integration.MoonshineSSP15SignedFRACTRANBranch
