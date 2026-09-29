import Mathlib
import Integration.OggSSPP2F4ActualEllipticGroup
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates

/-!
# Finite cardinality of the actual Banerjee F4 elliptic point group

Mathlib's Affine.Point currently has no general Finite/Fintype instance over
a finite coefficient ring. For this concrete curve we transport the obvious
finite structure through Mathlib's own equivalence

  Point ≃ WithZero { (x,y) // Equation x y }.

This is infrastructure, not a new arithmetic hypothesis.

The target theorem is the literal cardinality of the ACTUAL Mathlib elliptic
point group, not of DASHI's separate nine-label chart.
-/

namespace Integration.OggSSPP2F4ActualGroupCardinality

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates

open WeierstrassCurve

abbrev AffineSolution :=
  {xy : B.F4 × B.F4 //
    B.specialCurve.toAffine.Equation xy.1 xy.2}

noncomputable instance actualCurveGroupFintype :
    Fintype E.ActualCurveGroup :=
  Fintype.ofEquiv
    (WithZero AffineSolution)
    B.specialCurve.toAffine.pointEquiv.symm

theorem actual_curve_group_cardinality :
    Fintype.card E.ActualCurveGroup = 9 := by
  classical
  rw [Fintype.card_congr B.specialCurve.toAffine.pointEquiv]
  native_decide

theorem actual_curve_group_natCard :
    Nat.card E.ActualCurveGroup = 9 := by
  simpa [Nat.card_eq_fintype_card] using actual_curve_group_cardinality

structure Boundary where
  actualPointFintypeConstructed : Bool
  pointEquivUsedRatherThanLabelSurrogate : Bool
  actualGroupCardinalityNine : Bool
  groupIsomorphismToZMod3Square : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualPointFintypeConstructed := true
  pointEquivUsedRatherThanLabelSurrogate := true
  actualGroupCardinalityNine := true
  groupIsomorphismToZMod3Square := false

end Integration.OggSSPP2F4ActualGroupCardinality
