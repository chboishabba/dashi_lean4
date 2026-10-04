import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Mathlib

/-!
# Recentered 369 nine-plane as an additive C₃² module

The original Base369 triXor zero is low, whereas the origin-centred
elliptic chart and signed antipode use middle/zero.  This file uses the
literal signed-digit coordinate convention -1,0,+1 to transport the
canonical ZMod 3 addition to the existing NineSheet carrier.

The resulting maps are *genuine additive* permutations:
  Frobenius candidate : (a,b) -> (a,-b)
  elliptic shear candidate : (a,b) -> (a+b,b)
  elliptic inversion candidate : (a,b) -> (-a,-b).

They satisfy F²=1, R³=1 and F R F=R².  This is the group/action TARGET
for the actual F₄ elliptic source, not a proof that elliptic addition has
already been identified with the source-native Mathlib point group.
-/

namespace Integration.OggSSPP2RecenteredNineS3

open Integration.BalancedTernaryAntipodal369OrbitHierarchy
open Integration.OggSSPP2BalancedTernaryPuncturedPlane

abbrev Plane := NineSheet
abbrev AlgebraicPlane := ZMod 3 × ZMod 3

def signedToZMod : Trit → ZMod 3
  | .neg => -1
  | .zero => 0
  | .pos => 1

def zModToSigned (x : ZMod 3) : Trit :=
  if x = 0 then .zero
  else if x = 1 then .pos
  else .neg

theorem signed_zmod_roundtrip (t : Trit) :
    zModToSigned (signedToZMod t) = t := by
  cases t <;> decide

theorem zmod_signed_roundtrip (x : ZMod 3) :
    signedToZMod (zModToSigned x) = x := by
  fin_cases x <;> decide

def toZModPlane : Plane → AlgebraicPlane
  | (a,b) => (signedToZMod a, signedToZMod b)

def fromZModPlane : AlgebraicPlane → Plane
  | (a,b) => (zModToSigned a, zModToSigned b)

def groupPlaneEquiv : Plane ≃ AlgebraicPlane where
  toFun := toZModPlane
  invFun := fromZModPlane
  left_inv := by
    intro ⟨a,b⟩
    simp [toZModPlane, fromZModPlane, signed_zmod_roundtrip]
  right_inv := by
    intro ⟨a,b⟩
    simp [toZModPlane, fromZModPlane, zmod_signed_roundtrip]

def addSigned (a b : Trit) : Trit :=
  zModToSigned (signedToZMod a + signedToZMod b)

def addPlane : Plane → Plane → Plane
  | (a,b), (c,d) => (addSigned a c, addSigned b d)

def zeroPlane : Plane := (.zero,.zero)

def inversePlane : Plane → Plane
  | (a,b) => (antipode a, antipode b)

theorem add_plane_transported (x y : Plane) :
    toZModPlane (addPlane x y) = toZModPlane x + toZModPlane y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem zero_plane_transported :
    toZModPlane zeroPlane = 0 := by decide

theorem inverse_plane_transported (x : Plane) :
    toZModPlane (inversePlane x) = -toZModPlane x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem add_zero_plane (x : Plane) :
    addPlane x zeroPlane = x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem inverse_add_plane (x : Plane) :
    addPlane x (inversePlane x) = zeroPlane := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

def frobeniusPlane : Plane → Plane
  | (a,b) => (a,antipode b)

def shearPlane : Plane → Plane
  | (a,b) => (addSigned a b,b)

theorem frobenius_squared (x : Plane) :
    frobeniusPlane (frobeniusPlane x) = x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem shear_cubed (x : Plane) :
    shearPlane (shearPlane (shearPlane x)) = x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem frobenius_conjugates_shear (x : Plane) :
    frobeniusPlane (shearPlane (frobeniusPlane x)) =
      shearPlane (shearPlane x) := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem frobenius_additive (x y : Plane) :
    frobeniusPlane (addPlane x y) =
      addPlane (frobeniusPlane x) (frobeniusPlane y) := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem shear_additive (x y : Plane) :
    shearPlane (addPlane x y) =
      addPlane (shearPlane x) (shearPlane y) := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem frobenius_fixed_iff (x : Plane) :
    frobeniusPlane x = x ↔ x.2 = .zero := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem shear_fixed_iff (x : Plane) :
    shearPlane x = x ↔ x.2 = .zero := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem inversion_fixed_iff (x : Plane) :
    inversePlane x = x ↔ x = zeroPlane := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem frobenius_fixed_count :
    (Finset.univ.filter (fun x : Plane => frobeniusPlane x = x)).card = 3 := by
  decide

theorem shear_fixed_count :
    (Finset.univ.filter (fun x : Plane => shearPlane x = x)).card = 3 := by
  decide

theorem inversion_fixed_count :
    (Finset.univ.filter (fun x : Plane => inversePlane x = x)).card = 1 := by
  decide

structure Boundary where
  sourceNineSheetReused : Bool
  exactRecenteredZModThreeSquareEquiv : Bool
  centeredZeroIsAdditiveIdentity : Bool
  signedAntipodeIsAdditiveInverse : Bool
  FrobeniusAndShearAdditive : Bool
  s3RelationsPaid : Bool
  threeVsOneFixedProfilePaid : Bool
  actualEllipticGroupIntertwiner : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sourceNineSheetReused := true
  exactRecenteredZModThreeSquareEquiv := true
  centeredZeroIsAdditiveIdentity := true
  signedAntipodeIsAdditiveInverse := true
  FrobeniusAndShearAdditive := true
  s3RelationsPaid := true
  threeVsOneFixedProfilePaid := true
  actualEllipticGroupIntertwiner := false

end Integration.OggSSPP2RecenteredNineS3
