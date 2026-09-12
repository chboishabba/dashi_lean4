import Mathlib
import AgdaMirror.Algebra.FiniteQuaternionStrictCover

/-!
# Lean mirror of `DASHI/Algebra/ContinuousSpin31LorentzCover.agda`

This is an authority-preserving interface for the continuous
`Spin(3,1) → SO⁺(3,1)` cover.  Topological, smooth, connectedness, exact-kernel,
local-triviality, Lie-algebra, and metric-preservation obligations are explicit
fields.  The checked finite `Q8 → V4` model is not used to manufacture these
continuous obligations.
-/

namespace AgdaMirror.ContinuousSpin31LorentzCover

open AgdaMirror.FiniteQuaternionStrictCover

structure TopologicalGroup where
  Carrier : Type
  identity : Carrier
  product : Carrier → Carrier → Carrier
  inverse : Carrier → Carrier
  OpenSet : Type
  isOpen : OpenSet → Prop
  contains : OpenSet → Carrier → Prop
  groupLaws : Prop
  groupLawsProof : groupLaws
  topologyLaws : Prop
  topologyLawsProof : topologyLaws
  multiplicationContinuous : Prop
  multiplicationContinuousProof : multiplicationContinuous
  inverseContinuous : Prop
  inverseContinuousProof : inverseContinuous

structure SmoothGroupMap (domain codomain : TopologicalGroup) where
  map : domain.Carrier → codomain.Carrier
  homomorphism : ∀ left right,
    map (domain.product left right) = codomain.product (map left) (map right)
  identityPreserved : map domain.identity = codomain.identity
  continuous : Prop
  continuousProof : continuous
  smooth : Prop
  smoothProof : smooth

structure TwoSheetedCover (domain codomain : TopologicalGroup)
    (rho : SmoothGroupMap domain codomain) where
  Preimage : codomain.Carrier → Type
  exactPreimage : ∀ target, Preimage target
  plusOne : domain.Carrier
  minusOne : domain.Carrier
  plusAndMinusDistinct : Prop
  plusAndMinusDistinctProof : plusAndMinusDistinct
  kernelExactlyPlusMinusOne : domain.Carrier → Prop
  Fiber : codomain.Carrier → Type
  fiberHasExactlyTwoPoints : codomain.Carrier → Prop
  evenlyCoveredNeighborhood : codomain.Carrier → Prop
  localHomeomorphism : Prop
  localHomeomorphismProof : localHomeomorphism
  coveringMap : Prop
  coveringMapProof : coveringMap

structure ContinuousSpin31LorentzCover where
  Spin31 : TopologicalGroup
  SOPlus31 : TopologicalGroup
  rho : SmoothGroupMap Spin31 SOPlus31
  cover : TwoSheetedCover Spin31 SOPlus31 rho
  spin31IsConnectedDoubleCover : Prop
  spin31IsConnectedDoubleCoverProof : spin31IsConnectedDoubleCover
  targetIsProperOrthochronousLorentzGroup : Prop
  targetIsProperOrthochronousLorentzGroupProof :
    targetIsProperOrthochronousLorentzGroup
  lieAlgebraMapIsIsomorphism : Prop
  lieAlgebraMapIsIsomorphismProof : lieAlgebraMapIsIsomorphism
  actionPreservesMinkowskiQuadraticForm : Prop
  actionPreservesMinkowskiQuadraticFormProof :
    actionPreservesMinkowskiQuadraticForm
  orientationAndTimeOrientationPreserved : Prop
  orientationAndTimeOrientationPreservedProof :
    orientationAndTimeOrientationPreserved
  algebraicSurface : StrictSpinDoubleCoverProof
  spinCarrierAgreement : algebraicSurface.base.Spin = Spin31.Carrier
  lorentzCarrierAgreement : algebraicSurface.base.SO = SOPlus31.Carrier
  algebraicAndContinuousMapsAgree : Prop
  algebraicAndContinuousMapsAgreeProof : algebraicAndContinuousMapsAgree

def continuousSpinAlgebraicSurface (surface : ContinuousSpin31LorentzCover) :
    StrictSpinDoubleCoverProof := surface.algebraicSurface

/-- The interface itself carries no Clay/theorem promotion. -/
def clayPromotion : Bool := false

end AgdaMirror.ContinuousSpin31LorentzCover
