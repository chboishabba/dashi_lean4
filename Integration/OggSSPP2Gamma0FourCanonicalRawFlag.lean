import Mathlib
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation

/-!
# Canonical raw Gamma_0(4) flag at p = 2

External source context already used by
OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation:

for a supersingular elliptic curve over an algebraic closure of F_p, the
Drinfeld cyclic subgroup of order p^r is unique and is ker(F^r).

Specialising at p = 2 gives the canonical nested raw flag

  ker(F) ⊂ ker(F²),

with ranks 2 and 4 respectively.

This file records that finite source-facing flag.  It does NOT construct the
full finite-flat subgroup schemes inside a concrete Weierstrass family or the
local-model/inertia marking that distinguishes the ten residual states.
-/

namespace Integration.OggSSPP2Gamma0FourCanonicalRawFlag

namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation

inductive SupersingularRawOrderTwoSubgroup
  | kerFrobenius
  deriving DecidableEq, Repr, Fintype

abbrev SupersingularRawOrderFourSubgroup :=
  Unique.SupersingularRawGamma0FourSubgroup

theorem raw_order_two_subgroup_type_has_one_state :
    Fintype.card SupersingularRawOrderTwoSubgroup = 1 := by
  decide

theorem raw_order_four_subgroup_type_has_one_state :
    Fintype.card SupersingularRawOrderFourSubgroup = 1 :=
  Unique.raw_subgroup_type_has_one_state

structure RawGamma0FourFlag where
  orderTwo : SupersingularRawOrderTwoSubgroup
  orderFour : SupersingularRawOrderFourSubgroup

  orderTwoIsKerFrobenius :
    orderTwo = .kerFrobenius

  orderFourIsKerFrobeniusSquared :
    orderFour = .kerFrobeniusSquared

  /--
  Source-backed nesting statement ker(F) ⊂ ker(F²), kept as an attributed
  source proposition rather than reconstructed group-scheme inclusion.
  -/
  orderTwoSubflagOfOrderFour : Prop
  orderTwoSubflagOfOrderFourProof :
    orderTwoSubflagOfOrderFour

/--
Canonical source-attribution realization of the raw flag.

The nesting proposition is intentionally the proposition True: this term is an
attribution receipt for the externally sourced subgroup inclusion, not a Lean
construction of finite-flat group schemes.
-/
def canonicalRawFlag : RawGamma0FourFlag where
  orderTwo := .kerFrobenius
  orderFour := .kerFrobeniusSquared
  orderTwoIsKerFrobenius := rfl
  orderFourIsKerFrobeniusSquared := rfl
  orderTwoSubflagOfOrderFour := True
  orderTwoSubflagOfOrderFourProof := trivial

theorem canonical_order_two_is_ker_frobenius :
    canonicalRawFlag.orderTwo = .kerFrobenius :=
  rfl

theorem canonical_order_four_is_ker_frobenius_squared :
    canonicalRawFlag.orderFour = .kerFrobeniusSquared :=
  rfl

theorem raw_flag_choice_is_unique
    (flag : RawGamma0FourFlag) :
    flag.orderTwo = canonicalRawFlag.orderTwo ∧
      flag.orderFour = canonicalRawFlag.orderFour := by
  constructor
  · cases flag.orderTwo
    rfl
  · cases flag.orderFour
    rfl

theorem raw_flag_count_does_not_explain_ten_states :
    Fintype.card SupersingularRawOrderTwoSubgroup *
        Fintype.card SupersingularRawOrderFourSubgroup ≠
      10 := by
  decide

inductive Residual
  | missingConcreteFiniteFlatFlagRealization
  | missingLocalModelOrInertiaMarkingOverCanonicalFlag
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingConcreteFiniteFlatFlagRealization

structure Boundary where
  uniqueRawOrderTwoSubgroupRecorded : Bool
  uniqueRawOrderFourSubgroupReused : Bool
  rawKerFInsideKerF2FlagRecorded : Bool
  rawFlagChoiceUnique : Bool
  rawFlagExplainsTenResidualStates : Bool
  concreteFiniteFlatGroupSchemeInclusionConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  uniqueRawOrderTwoSubgroupRecorded := true
  uniqueRawOrderFourSubgroupReused := true
  rawKerFInsideKerF2FlagRecorded := true
  rawFlagChoiceUnique := true
  rawFlagExplainsTenResidualStates := false
  concreteFiniteFlatGroupSchemeInclusionConstructed := false

end Integration.OggSSPP2Gamma0FourCanonicalRawFlag
