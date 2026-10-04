import Mathlib
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation

/-!
# Canonical ker(F) subset ker(F²) source flag at p=2

The bad-prime Gamma_0(4) source does not offer a free choice among many
order-four cyclic subgroup schemes on the supersingular fibre.  The raw
order-four object is uniquely ker(F²).

Likewise the natural order-two stage of the Frobenius tower is ker(F), with
ker(F) subset ker(F²).

This module removes arbitrary finite subgroup labels from the formal source
contract.  It keeps the actual finite-flat/group-scheme meaning proof-bearing:
a source authority must certify finite flatness, the subflag relation and the
Gamma_0(4) semantics.

No ten-state residual information is inferred from this one raw flag.
-/

namespace Integration.OggSSPP2KerFSubflagFiniteFlatSource

namespace Gamma := Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation

inductive OrderTwoFrobeniusSubgroup
  | kerFrobenius
  deriving DecidableEq, Repr, Fintype

abbrev OrderFourFrobeniusSubgroup :=
  Unique.SupersingularRawGamma0FourSubgroup

theorem order_two_choice_count_is_one :
    Fintype.card OrderTwoFrobeniusSubgroup = 1 := by decide

theorem order_four_choice_count_is_one :
    Fintype.card OrderFourFrobeniusSubgroup = 1 :=
  Unique.raw_subgroup_type_has_one_state

structure Authority where
  kerFFiniteFlat : Prop
  kerFFiniteFlatProof : kerFFiniteFlat

  kerF2FiniteFlat : Prop
  kerF2FiniteFlatProof : kerF2FiniteFlat

  kerFSubflagKerF2 : Prop
  kerFSubflagKerF2Proof : kerFSubflagKerF2

  gammaZeroFourSemantics : Prop
  gammaZeroFourSemanticsProof : gammaZeroFourSemantics

  sourceReference : String

def finiteFlatDatum
    {EllipticObject : Type}
    (selectedEllipticObject : EllipticObject)
    (authority : Authority) :
    Gamma.Gamma0FourFiniteFlatDatum where
  EllipticObject := EllipticObject
  OrderFourSubgroup := OrderFourFrobeniusSubgroup
  OrderTwoSubgroup := OrderTwoFrobeniusSubgroup

  selectedEllipticObject := selectedEllipticObject
  selectedOrderFourSubgroup := .kerFrobeniusSquared
  selectedOrderTwoSubgroup := .kerFrobenius

  orderFourRank := 4
  orderFourRankIsFour := rfl
  orderTwoRank := 2
  orderTwoRankIsTwo := rfl

  orderTwoSubflagOfOrderFour := authority.kerFSubflagKerF2
  orderTwoSubflagOfOrderFourProof := authority.kerFSubflagKerF2Proof

  finiteFlatAtCharacteristicTwo := authority.kerF2FiniteFlat
  finiteFlatAtCharacteristicTwoProof := authority.kerF2FiniteFlatProof

  gammaZeroLevelFourSemantics := authority.gammaZeroFourSemantics
  gammaZeroLevelFourSemanticsProof := authority.gammaZeroFourSemanticsProof

  sourceReference := authority.sourceReference

theorem selected_order_four_is_kerF2
    {EllipticObject : Type}
    (E : EllipticObject)
    (authority : Authority) :
    (finiteFlatDatum E authority).selectedOrderFourSubgroup =
      .kerFrobeniusSquared :=
  rfl

theorem selected_order_two_is_kerF
    {EllipticObject : Type}
    (E : EllipticObject)
    (authority : Authority) :
    (finiteFlatDatum E authority).selectedOrderTwoSubgroup =
      .kerFrobenius :=
  rfl

structure Boundary where
  orderFourChoiceCollapsedToUniqueKerF2 : Bool
  orderTwoChoiceCollapsedToKerF : Bool
  subflagStillProofBearing : Bool
  finiteFlatMeaningStillProofBearing : Bool
  gamma0FourMeaningStillProofBearing : Bool
  tenStateResidualInferredFromRawFlag : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  orderFourChoiceCollapsedToUniqueKerF2 := true
  orderTwoChoiceCollapsedToKerF := true
  subflagStillProofBearing := true
  finiteFlatMeaningStillProofBearing := true
  gamma0FourMeaningStillProofBearing := true
  tenStateResidualInferredFromRawFlag := false

end Integration.OggSSPP2KerFSubflagFiniteFlatSource
