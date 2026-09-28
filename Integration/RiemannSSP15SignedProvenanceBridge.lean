import Mathlib
import Integration.RiemannSSP15DepthFiveRoleCodec
import Integration.RiemannSSP15ChosenGridTransversality

/-!
# RH/SSP15 pointed signed provenance bridge

Lean mirror of the finite provenance phenomenon already owned in Agda.

A chosen RH role code determines:
* one of the 15 chosen prime labels;
* a unit signed multiplicity from its role;
* a pointed signed state retaining both.

The selected prime reopens the original 15-state code exactly.  By contrast,
all five j-role states have zero signed multiplicity and compile to the same
zero valuation, so the coarse valuation cannot recover their mode/provenance.
-/

namespace Integration.RiemannSSP15SignedProvenanceBridge

open Integration.RiemannSSP15DepthFiveRoleCodec
open Integration.RiemannSSP15ChosenGridTransversality

def primeToRoleCode : Prime15 → RHSSP15RoleCode
  | .p2 => (.mode09,.origin)
  | .p3 => (.mode09,.j)
  | .p5 => (.mode09,.s)
  | .p7 => (.mode18,.origin)
  | .p11 => (.mode18,.j)
  | .p13 => (.mode18,.s)
  | .p17 => (.mode27,.origin)
  | .p19 => (.mode27,.j)
  | .p23 => (.mode27,.s)
  | .p29 => (.mode36,.origin)
  | .p31 => (.mode36,.j)
  | .p41 => (.mode36,.s)
  | .p47 => (.mode45,.origin)
  | .p59 => (.mode45,.j)
  | .p71 => (.mode45,.s)

theorem prime_after_role_code (c : RHSSP15RoleCode) :
    primeToRoleCode (roleCodeToPrime c) = c := by
  rcases c with ⟨m,r⟩
  cases m <;> cases r <;> rfl

theorem role_code_after_prime (p : Prime15) :
    roleCodeToPrime (primeToRoleCode p) = p := by
  cases p <;> rfl

inductive SignedUnit
  | negativeOne | zero | positiveOne
  deriving DecidableEq, Repr, Fintype

def roleToSignedUnit : RHDepthFiveRole → SignedUnit
  | .origin => .negativeOne
  | .j => .zero
  | .s => .positiveOne

structure PointedSigned where
  selectedPrime : Prime15
  multiplicity : SignedUnit
  deriving DecidableEq, Repr

def roleCodeToPointed (c : RHSSP15RoleCode) : PointedSigned :=
  ⟨roleCodeToPrime c, roleToSignedUnit c.2⟩

def pointedToCoarseRoleCode (p : PointedSigned) : RHSSP15RoleCode :=
  let c := primeToRoleCode p.selectedPrime
  (c.1,
    match p.multiplicity with
    | .negativeOne => .origin
    | .zero => .j
    | .positiveOne => .s)

theorem role_code_pointed_roundtrip (c : RHSSP15RoleCode) :
    pointedToCoarseRoleCode (roleCodeToPointed c) = c := by
  rcases c with ⟨m,r⟩
  cases m <;> cases r <;> rfl

def zeroValuation : Prime15 → SignedUnit := fun _ => .zero

def pointedValuation (p : PointedSigned) : Prime15 → SignedUnit :=
  fun observed => if observed = p.selectedPrime then p.multiplicity else .zero

theorem pointed_valuation_own_lane (p : PointedSigned) :
    pointedValuation p p.selectedPrime = p.multiplicity := by
  simp [pointedValuation]

def jRoleCode (m : Mode5) : RHSSP15RoleCode := (m,.j)

theorem j_role_pointed_zero (m : Mode5) :
    (roleCodeToPointed (jRoleCode m)).multiplicity = .zero := rfl

theorem j_role_valuation_is_zero (m : Mode5) :
    pointedValuation (roleCodeToPointed (jRoleCode m)) = zeroValuation := by
  funext observed
  simp [pointedValuation, zeroValuation, jRoleCode, roleCodeToPointed]
  split <;> rfl

theorem distinct_neutral_codes_same_valuation :
    jRoleCode .mode09 ≠ jRoleCode .mode18 ∧
    pointedValuation (roleCodeToPointed (jRoleCode .mode09)) =
      pointedValuation (roleCodeToPointed (jRoleCode .mode18)) := by
  constructor
  · decide
  · rw [j_role_valuation_is_zero, j_role_valuation_is_zero]

def jColumnNeutralPrimes : List Prime15 :=
  [roleCodeToPrime (.mode09,.j),
   roleCodeToPrime (.mode18,.j),
   roleCodeToPrime (.mode27,.j),
   roleCodeToPrime (.mode36,.j),
   roleCodeToPrime (.mode45,.j)]

theorem j_column_neutral_primes_exact :
    jColumnNeutralPrimes = [.p3,.p11,.p19,.p31,.p59] := rfl

theorem five_neutral_j_states_share_zero_valuation :
    pointedValuation (roleCodeToPointed (jRoleCode .mode09)) =
      pointedValuation (roleCodeToPointed (jRoleCode .mode18)) ∧
    pointedValuation (roleCodeToPointed (jRoleCode .mode18)) =
      pointedValuation (roleCodeToPointed (jRoleCode .mode27)) ∧
    pointedValuation (roleCodeToPointed (jRoleCode .mode27)) =
      pointedValuation (roleCodeToPointed (jRoleCode .mode36)) ∧
    pointedValuation (roleCodeToPointed (jRoleCode .mode36)) =
      pointedValuation (roleCodeToPointed (jRoleCode .mode45)) := by
  constructor
  · rw [j_role_valuation_is_zero, j_role_valuation_is_zero]
  constructor
  · rw [j_role_valuation_is_zero, j_role_valuation_is_zero]
  constructor
  · rw [j_role_valuation_is_zero, j_role_valuation_is_zero]
  · rw [j_role_valuation_is_zero, j_role_valuation_is_zero]

inductive PromotionError
  | zeroValuationRecoversSelectedMode
  | chosenPrimeAssignmentIsExternalArithmeticCanonicality
  | rhRoleIsSignedMultiplicitySemantics
  deriving DecidableEq, Repr

structure Boundary where
  chosenPrimeBijectionMirrored : Bool
  pointedRoleCodeRoundtripOwned : Bool
  unitSignedRoleIndexingOwned : Bool
  neutralJRoleValuationLossOwned : Bool
  coarseValuationRecoversMode : Bool
  externalArithmeticCanonicalityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  chosenPrimeBijectionMirrored := true
  pointedRoleCodeRoundtripOwned := true
  unitSignedRoleIndexingOwned := true
  neutralJRoleValuationLossOwned := true
  coarseValuationRecoversMode := false
  externalArithmeticCanonicalityClaimed := false

end Integration.RiemannSSP15SignedProvenanceBridge
