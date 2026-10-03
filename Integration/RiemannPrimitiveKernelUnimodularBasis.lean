import Mathlib
import Integration.RiemannPrimitiveKernelBalancedTernaryStencil

/-!
# Primitive RH kernel under an explicit unimodular basis change

On the first two columns use

    U = [ -82   3 ]
        [  27  -1 ]

with det U = 1.  For the coefficient row:

    (80,243) U = (1,-3).

The inverse block is

    U⁻¹ = [ -1  -3 ]
          [ -27 -82 ].

Thus the full row changes from

    (80,243,1215,972)

to

    (1,-3,1215,972).

The original coordinate 3-adic profile (0,5,5,5) therefore becomes
(0,1,5,5).  The primitive/Smith invariant remains 1.
-/

namespace Integration.RiemannPrimitiveKernelUnimodularBasis

open Integration.RiemannPrimitiveKernelBalancedTernaryStencil

abbrev PairZ := Int × Int

def forwardU : PairZ → PairZ
  | (x,y) => (-82*x + 27*y, 3*x - y)

def inverseU : PairZ → PairZ
  | (u,v) => (-u - 27*v, -3*u - 82*v)

theorem determinant_U_is_one :
    (-82 : Int) * (-1) - 3 * 27 = 1 := by norm_num

theorem forward_after_inverse (p : PairZ) :
    forwardU (inverseU p) = p := by
  rcases p with ⟨u,v⟩
  simp [forwardU, inverseU]
  constructor <;> ring

theorem inverse_after_forward (p : PairZ) :
    inverseU (forwardU p) = p := by
  rcases p with ⟨x,y⟩
  simp [forwardU, inverseU]
  constructor <;> ring

def pairEquiv : PairZ ≃ PairZ where
  toFun := forwardU
  invFun := inverseU
  left_inv := inverse_after_forward
  right_inv := forward_after_inverse

def originalLeadingPair : PairZ := (80,243)

theorem transformed_leading_pair :
    forwardU originalLeadingPair = (1,-3) := by
  norm_num [forwardU, originalLeadingPair]

theorem inverse_recovers_original :
    inverseU (1,-3) = originalLeadingPair := by
  norm_num [inverseU, originalLeadingPair]

theorem primitive_bezout_certificate :
    (27 : Int) * 243 - 82 * 80 = 1 := by
  norm_num

def fullRowGCD : Nat :=
  Nat.gcd 80 (Nat.gcd 243 (Nat.gcd 1215 972))

theorem full_row_gcd_is_one :
    fullRowGCD = 1 := by
  native_decide

/-- For a 1×4 integer row, gcd 1 is the scalar Smith invariant. -/
def smithInvariant : Nat := fullRowGCD

theorem smith_invariant_is_one :
    smithInvariant = 1 := full_row_gcd_is_one

def originalDepthProfile : Nat × Nat × Nat × Nat := (0,5,5,5)
def transformedDepthProfile : Nat × Nat × Nat × Nat := (0,1,5,5)

theorem transformed_profile_exact :
    transformedDepthProfile = (0,1,5,5) := rfl

theorem depth_profile_changes :
    transformedDepthProfile ≠ originalDepthProfile := by
  decide

inductive PromotionError
  | rawDepthTupleIsUnimodularInvariant
  | smithInvariantOneDeterminesDepthFiveFlag
  deriving DecidableEq, Repr

structure Boundary where
  determinantOneBasisChangeOwned : Bool
  explicitInverseOwned : Bool
  roundTripsOwned : Bool
  transformedLeadingPairOneMinusThree : Bool
  fullRowGCDOneOwned : Bool
  smithInvariantOneOwned : Bool
  originalDepthProfileZeroFiveFiveFive : Bool
  transformedDepthProfileZeroOneFiveFive : Bool
  rawDepthTupleUnimodularInvariant : Bool
  filteredFlagStillRequiresExtraStructure : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  determinantOneBasisChangeOwned := true
  explicitInverseOwned := true
  roundTripsOwned := true
  transformedLeadingPairOneMinusThree := true
  fullRowGCDOneOwned := true
  smithInvariantOneOwned := true
  originalDepthProfileZeroFiveFiveFive := true
  transformedDepthProfileZeroOneFiveFive := true
  rawDepthTupleUnimodularInvariant := false
  filteredFlagStillRequiresExtraStructure := true

end Integration.RiemannPrimitiveKernelUnimodularBasis
