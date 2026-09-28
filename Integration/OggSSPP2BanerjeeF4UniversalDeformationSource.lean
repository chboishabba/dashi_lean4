import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Integration.OggSSPP2OrientedInertiaTenStateRecognition
import Integration.OggSSPP2F4AntipodalStratifiedRefinement

/-!
# Banerjee F4 universal-deformation / G24 ⋊ Gal source surface

External source:
Romie Banerjee, "A modular description of ER(2)",
New York Journal of Mathematics 20 (2014), 743--758, arXiv:1212.2069.

Source-level facts recorded here:
* C : y² + y = x³ over F4 is the characteristic-two supersingular curve;
* Aut_F4(C) = G24, the binary tetrahedral group of order 24;
* Def(C,F4) -> Ell^ss_2 is an etale G24 ⋊ Gal(F4/F2)-torsor;
* by Serre--Tate,
      Def(C,F4) ≃ Spf W(F4)[[a1]];
* the universal lift has equation
      y² + a1*x*y + y = x³.

DASHI reconstruction:
* quotient the seven G24 conjugacy classes by inversion to five sectors;
* retain the Gal(F4/F2) binary sheet;
* obtain a 2 × 5 = 10 finite sector carrier;
* rechart that carrier exactly to the paid p=2 ten-state target.

The source does NOT state that this 10-state quotient is the Gamma_0(4) level
fibre, nor that the Gal sheet is the Goren--Love quadratic-orientation label.
-/

namespace Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

namespace Inertia := Integration.OggSSPP2OrientedInertiaTenStateRecognition
namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement

abbrev F4 := GaloisField 2 2
abbrev F4WittRing := WittVector 2 F4
abbrev F4DeformationBase := PowerSeries F4WittRing

noncomputable def f4Field : Field F4 := inferInstance
noncomputable def f4WittCommRing : CommRing F4WittRing := inferInstance
noncomputable def f4WittDVR : IsDiscreteValuationRing F4WittRing := inferInstance
noncomputable def f4WittLocalRing : IsLocalRing F4WittRing := inferInstance

noncomputable local instance : IsLocalRing F4WittRing :=
  f4WittLocalRing

noncomputable def f4PowerSeriesLocalRing :
    IsLocalRing F4DeformationBase :=
  inferInstance

noncomputable def f4WittTwoAdicallyComplete :
    IsAdicComplete
      (Ideal.span ({(2 : F4WittRing)} : Set F4WittRing))
      F4WittRing :=
  inferInstance

def universalParameter : F4DeformationBase :=
  PowerSeries.X

inductive GaloisSheet
  | identity
  | frobenius
  deriving DecidableEq, Repr, Fintype

theorem galois_sheet_cardinality :
    Fintype.card GaloisSheet = 2 := by decide

abbrev GaloisInertiaState :=
  GaloisSheet × Inertia.BinaryTetrahedralInversionOrbit

theorem galois_inertia_state_cardinality :
    Fintype.card GaloisInertiaState = 10 := by decide

def toTarget : GaloisInertiaState → Target.StratifiedTargetState
  | (.identity, .identity) => .fixedZero
  | (.frobenius, .identity) => .fixedOne
  | (.identity, .centralMinusOne) => .conjugate .lower .firstAxis
  | (.frobenius, .centralMinusOne) => .conjugate .upper .firstAxis
  | (.identity, .orderFour) => .conjugate .lower .secondAxis
  | (.frobenius, .orderFour) => .conjugate .upper .secondAxis
  | (.identity, .orderThreePair) => .conjugate .lower .equalSign
  | (.frobenius, .orderThreePair) => .conjugate .upper .equalSign
  | (.identity, .orderSixPair) => .conjugate .lower .oppositeSign
  | (.frobenius, .orderSixPair) => .conjugate .upper .oppositeSign

def fromTarget : Target.StratifiedTargetState → GaloisInertiaState
  | .fixedZero => (.identity, .identity)
  | .fixedOne => (.frobenius, .identity)
  | .conjugate .lower .firstAxis => (.identity, .centralMinusOne)
  | .conjugate .upper .firstAxis => (.frobenius, .centralMinusOne)
  | .conjugate .lower .secondAxis => (.identity, .orderFour)
  | .conjugate .upper .secondAxis => (.frobenius, .orderFour)
  | .conjugate .lower .equalSign => (.identity, .orderThreePair)
  | .conjugate .upper .equalSign => (.frobenius, .orderThreePair)
  | .conjugate .lower .oppositeSign => (.identity, .orderSixPair)
  | .conjugate .upper .oppositeSign => (.frobenius, .orderSixPair)

theorem source_roundtrip (s : GaloisInertiaState) :
    fromTarget (toTarget s) = s := by
  rcases s with ⟨g, i⟩
  cases g <;> cases i <;> rfl

theorem target_roundtrip (s : Target.StratifiedTargetState) :
    toTarget (fromTarget s) = s := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit =>
      cases side <;> cases orbit <;> rfl

def equivTarget : GaloisInertiaState ≃ Target.StratifiedTargetState where
  toFun := toTarget
  invFun := fromTarget
  left_inv := source_roundtrip
  right_inv := target_roundtrip

structure SourceReceipt where
  curveOverF4IsY2PlusYEqX3 : Bool
  automorphismGroupIsG24 : Bool
  universalDeformationIsG24SemidirectGaloisTorsor : Bool
  deformationBaseIsWittF4PowerSeries : Bool
  universalLiftEquationRecorded : Bool
  sourceTitle : String
  sourceLocator : String
  deriving Repr

def canonicalSourceReceipt : SourceReceipt where
  curveOverF4IsY2PlusYEqX3 := true
  automorphismGroupIsG24 := true
  universalDeformationIsG24SemidirectGaloisTorsor := true
  deformationBaseIsWittF4PowerSeries := true
  universalLiftEquationRecorded := true
  sourceTitle := "Romie Banerjee, A modular description of ER(2), NYJM 20 (2014) 743-758"
  sourceLocator := "Section 3.1, Proposition 3.1; arXiv:1212.2069"

structure Boundary where
  literalF4CarrierOwned : Bool
  literalWittF4CarrierOwned : Bool
  wittF4DVRPaid : Bool
  wittF4TwoAdicCompletenessPaid : Bool
  sourceG24ActionRecorded : Bool
  sourceGaloisC2ActionRecorded : Bool
  sourceSameDeformationTorsorRecorded : Bool
  fiveInversionOrbitQuotientIsRepositoryReconstruction : Bool
  exactTwoTimesFiveCarrierOwned : Bool
  exactRechartToPaidTenStateTarget : Bool
  galSheetIdentifiedWithQuadraticOrientation : Bool
  tenStatesIdentifiedWithGamma0FourLevelPoints : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalF4CarrierOwned := true
  literalWittF4CarrierOwned := true
  wittF4DVRPaid := true
  wittF4TwoAdicCompletenessPaid := true
  sourceG24ActionRecorded := true
  sourceGaloisC2ActionRecorded := true
  sourceSameDeformationTorsorRecorded := true
  fiveInversionOrbitQuotientIsRepositoryReconstruction := true
  exactTwoTimesFiveCarrierOwned := true
  exactRechartToPaidTenStateTarget := true
  galSheetIdentifiedWithQuadraticOrientation := false
  tenStatesIdentifiedWithGamma0FourLevelPoints := false

end Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
