import Mathlib
import Integration.RiemannSSP15SignedProvenanceBridge

/-!
# RH/SSP15 producer-role signed FRACTRAN mirror

Finite Lean mirror of the existing Agda SignedSSPFRACTRANWeave semantics used
by the RH/SSP15 bridge.

Role compilation:
* origin -> inverse selected-prime token
* j      -> empty arithmetic program
* s      -> positive selected-prime token

The pointed seed keeps the selected prime even when the neutral j programme and
coarse valuation are both silent.
-/

namespace Integration.RiemannSSP15SignedFRACTRAN

open Integration.RiemannSSP15DepthFiveRoleCodec
open Integration.RiemannSSP15ChosenGridTransversality
open Integration.RiemannSSP15SignedProvenanceBridge

inductive SignedInstruction
  | introducePrime (prime : Prime15)
  | introduceInversePrime (prime : Prime15)
  deriving DecidableEq, Repr

def roleProgram : RHSSP15RoleCode → List SignedInstruction
  | (m,.origin) => [.introduceInversePrime (roleCodeToPrime (m,.origin))]
  | (_,.j) => []
  | (m,.s) => [.introducePrime (roleCodeToPrime (m,.s))]

inductive FibreOrientation
  | inverse | mediated | forward
  deriving DecidableEq, Repr

def orientationOfRole : RHDepthFiveRole → FibreOrientation
  | .origin => .inverse
  | .j => .mediated
  | .s => .forward

def complexityRank : Prime15 → Nat
  | .p2 => 0
  | .p3 => 1
  | .p5 => 2
  | .p7 => 3
  | .p11 => 4
  | .p13 => 5
  | .p17 => 6
  | .p19 => 7
  | .p23 => 8
  | .p29 => 9
  | .p31 => 10
  | .p41 => 11
  | .p47 => 12
  | .p59 => 13
  | .p71 => 14

structure HyperformLane where
  prime : Prime15
  declaredComplexityRank : Nat
  rankCertificate : declaredComplexityRank = complexityRank prime
  address369 : Nat × Nat × Nat
  orientation : FibreOrientation

def canonicalAddress369 : Nat × Nat × Nat := (3,6,9)

def hyperformLane (c : RHSSP15RoleCode) : HyperformLane :=
  let p := roleCodeToPrime c
  ⟨p, complexityRank p, rfl, canonicalAddress369, orientationOfRole c.2⟩

theorem hyperform_lane_prime_exact (c : RHSSP15RoleCode) :
    (hyperformLane c).prime = roleCodeToPrime c := rfl

theorem origin_hyperform_orientation_inverse (m : Mode5) :
    (hyperformLane (m,.origin)).orientation = .inverse := rfl

theorem j_hyperform_orientation_mediated (m : Mode5) :
    (hyperformLane (m,.j)).orientation = .mediated := rfl

theorem s_hyperform_orientation_forward (m : Mode5) :
    (hyperformLane (m,.s)).orientation = .forward := rfl

theorem hyperform_address_is_369 (c : RHSSP15RoleCode) :
    (hyperformLane c).address369 = (3,6,9) := rfl

structure Effect where
  positivePrimeTokens : Nat
  inversePrimeTokens : Nat
  deriving DecidableEq, Repr

def emptyEffect : Effect := ⟨0,0⟩

def applyInstruction : SignedInstruction → Effect → Effect
  | .introducePrime _, e =>
      ⟨e.positivePrimeTokens + 1, e.inversePrimeTokens⟩
  | .introduceInversePrime _, e =>
      ⟨e.positivePrimeTokens, e.inversePrimeTokens + 1⟩

def executeProgram : List SignedInstruction → Effect → Effect
  | [], e => e
  | i :: rest, e => executeProgram rest (applyInstruction i e)

structure PointedSeed where
  roleCode : RHSSP15RoleCode
  pointed : PointedSigned
  program : List SignedInstruction
  pointed_is_compiled : pointed = roleCodeToPointed roleCode

def seed (c : RHSSP15RoleCode) : PointedSeed :=
  ⟨c, roleCodeToPointed c, roleProgram c, rfl⟩

def executeSeed (s : PointedSeed) : Effect :=
  executeProgram s.program emptyEffect

theorem origin_has_one_inverse (m : Mode5) :
    (executeSeed (seed (m,.origin))).inversePrimeTokens = 1 := by
  cases m <;> rfl

theorem origin_has_no_positive (m : Mode5) :
    (executeSeed (seed (m,.origin))).positivePrimeTokens = 0 := by
  cases m <;> rfl

theorem j_program_empty (m : Mode5) :
    (seed (m,.j)).program = [] := by
  cases m <;> rfl

theorem j_effect_empty (m : Mode5) :
    executeSeed (seed (m,.j)) = emptyEffect := by
  cases m <;> rfl

theorem s_has_one_positive (m : Mode5) :
    (executeSeed (seed (m,.s))).positivePrimeTokens = 1 := by
  cases m <;> rfl

theorem s_has_no_inverse (m : Mode5) :
    (executeSeed (seed (m,.s))).inversePrimeTokens = 0 := by
  cases m <;> rfl

theorem j_selected_primes_exact :
    ((seed (.mode09,.j)).pointed.selectedPrime,
     (seed (.mode18,.j)).pointed.selectedPrime,
     (seed (.mode27,.j)).pointed.selectedPrime,
     (seed (.mode36,.j)).pointed.selectedPrime,
     (seed (.mode45,.j)).pointed.selectedPrime)
    =
    (.p3,.p11,.p19,.p31,.p59) := rfl

theorem all_j_execution_effects_coincide (m₁ m₂ : Mode5) :
    executeSeed (seed (m₁,.j)) = executeSeed (seed (m₂,.j)) := by
  rw [j_effect_empty, j_effect_empty]

theorem pointed_seed_reopens_role_code (c : RHSSP15RoleCode) :
    primeToRoleCode (seed c).pointed.selectedPrime = c := by
  simpa [seed] using prime_after_role_code c

theorem five_neutral_states_same_effect :
    executeSeed (seed (.mode09,.j)) = executeSeed (seed (.mode18,.j)) ∧
    executeSeed (seed (.mode18,.j)) = executeSeed (seed (.mode27,.j)) ∧
    executeSeed (seed (.mode27,.j)) = executeSeed (seed (.mode36,.j)) ∧
    executeSeed (seed (.mode36,.j)) = executeSeed (seed (.mode45,.j)) := by
  repeat' constructor <;> apply all_j_execution_effects_coincide

inductive PromotionError
  | emptyJProgramRecoversSelectedPrime
  | signedExecutionCreatesAnalyticIdentity
  deriving DecidableEq, Repr

structure Boundary where
  signedHyperformLaneOwned : Bool
  rolePolarityOrientationOwned : Bool
  canonical369AddressOwned : Bool
  originInverseInstructionOwned : Bool
  jEmptyProgramOwned : Bool
  sPositiveInstructionOwned : Bool
  neutralSelectedPrimeRetained : Bool
  fiveNeutralEffectsCollapse : Bool
  pointedSeedReopensRoleCode : Bool
  signedExecutionPromotedToAnalyticIdentity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  signedHyperformLaneOwned := true
  rolePolarityOrientationOwned := true
  canonical369AddressOwned := true
  originInverseInstructionOwned := true
  jEmptyProgramOwned := true
  sPositiveInstructionOwned := true
  neutralSelectedPrimeRetained := true
  fiveNeutralEffectsCollapse := true
  pointedSeedReopensRoleCode := true
  signedExecutionPromotedToAnalyticIdentity := false

end Integration.RiemannSSP15SignedFRACTRAN
