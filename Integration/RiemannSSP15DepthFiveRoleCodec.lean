import Mathlib

/-!
# RH depth-five role / SSP15 5×3 indexing codec

Lean parity surface for the Agda SSP15 role codec.

This module intentionally mirrors only the finite carrier:
  five modes × three RH provenance roles ≃ five modes × three balanced phases.

It does not construct an Ogg-prime assignment or claim semantic identity between
RH roles and SSP15 phases.
-/

namespace Integration.RiemannSSP15DepthFiveRoleCodec

inductive Mode5
  | mode09 | mode18 | mode27 | mode36 | mode45
  deriving DecidableEq, Repr, Fintype

inductive RHDepthFiveRole
  | origin | j | s
  deriving DecidableEq, Repr, Fintype

inductive BalancedPhase
  | negative | zero | positive
  deriving DecidableEq, Repr, Fintype

def roleToPhase : RHDepthFiveRole → BalancedPhase
  | .origin => .negative
  | .j => .zero
  | .s => .positive

def phaseToRole : BalancedPhase → RHDepthFiveRole
  | .negative => .origin
  | .zero => .j
  | .positive => .s

theorem role_after_phase (p : BalancedPhase) :
    roleToPhase (phaseToRole p) = p := by
  cases p <;> rfl

theorem phase_after_role (r : RHDepthFiveRole) :
    phaseToRole (roleToPhase r) = r := by
  cases r <;> rfl

def rolePhaseEquiv : RHDepthFiveRole ≃ BalancedPhase where
  toFun := roleToPhase
  invFun := phaseToRole
  left_inv := phase_after_role
  right_inv := role_after_phase

abbrev RHSSP15RoleCode := Mode5 × RHDepthFiveRole
abbrev SSP15InternalLane := Mode5 × BalancedPhase

def encodeRoleCode : RHSSP15RoleCode → SSP15InternalLane
  | (m,r) => (m, roleToPhase r)

def decodeRoleCode : SSP15InternalLane → RHSSP15RoleCode
  | (m,p) => (m, phaseToRole p)

theorem decode_encode (c : RHSSP15RoleCode) :
    decodeRoleCode (encodeRoleCode c) = c := by
  rcases c with ⟨m,r⟩
  simp [encodeRoleCode, decodeRoleCode, phase_after_role]

theorem encode_decode (l : SSP15InternalLane) :
    encodeRoleCode (decodeRoleCode l) = l := by
  rcases l with ⟨m,p⟩
  simp [encodeRoleCode, decodeRoleCode, role_after_phase]

def roleCodeEquiv : RHSSP15RoleCode ≃ SSP15InternalLane where
  toFun := encodeRoleCode
  invFun := decodeRoleCode
  left_inv := decode_encode
  right_inv := encode_decode

theorem role_code_cardinality :
    Fintype.card RHSSP15RoleCode = 15 := by
  native_decide

theorem ssp15_lane_cardinality :
    Fintype.card SSP15InternalLane = 15 := by
  native_decide

inductive UnitSignedMultiplicity
  | negativeOne | zero | positiveOne
  deriving DecidableEq, Repr, Fintype

def roleToUnitMultiplicity : RHDepthFiveRole → UnitSignedMultiplicity
  | .origin => .negativeOne
  | .j => .zero
  | .s => .positiveOne

def coarseMultiplicity : RHSSP15RoleCode → UnitSignedMultiplicity
  | (_,r) => roleToUnitMultiplicity r

theorem j_role_coarse_erases_mode (m₁ m₂ : Mode5) :
    coarseMultiplicity (m₁,.j) = coarseMultiplicity (m₂,.j) := rfl

theorem distinct_modes_exist :
    (Mode5.mode09 : Mode5) ≠ .mode18 := by decide

theorem coarse_zero_does_not_recover_mode :
    ∃ a b : RHSSP15RoleCode,
      a ≠ b ∧ coarseMultiplicity a = coarseMultiplicity b := by
  refine ⟨(.mode09,.j), (.mode18,.j), ?_, rfl⟩
  decide

inductive PromotionError
  | rolePhaseIndexingIsSemanticIdentity
  | fifteenCountCreatesOggPrimeAssignment
  | coarseMultiplicityRecoversMode
  deriving DecidableEq, Repr

structure Boundary where
  fiveByThreeCodecOwned : Bool
  exactRoundtripOwned : Bool
  cardinalityFifteenOwned : Bool
  neutralRoleModeLossOwned : Bool
  rolePhaseSemanticIdentityClaimed : Bool
  oggPrimeAssignmentConstructedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fiveByThreeCodecOwned := true
  exactRoundtripOwned := true
  cardinalityFifteenOwned := true
  neutralRoleModeLossOwned := true
  rolePhaseSemanticIdentityClaimed := false
  oggPrimeAssignmentConstructedHere := false

end Integration.RiemannSSP15DepthFiveRoleCodec
