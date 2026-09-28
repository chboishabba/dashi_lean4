import Mathlib

/-!
# Small-characteristic supersingular isotropy-order comparison

External arithmetic values:
* characteristic 2 unique supersingular elliptic curve: automorphism order 24;
* characteristic 3 supersingular j=0 elliptic curve: automorphism order 12.

Repository-side finite skeletons:
* affine-E6 / binary-tetrahedral dimension-square sum 24;
* rotational tetrahedral order 12.

This module records only the numerical alignment and factor-two comparison.
It does not identify the finite representation skeletons with the arithmetic
automorphism groups, the p=2 retained orientation fibre, or the missing
exponent-residual source groupoids.
-/

namespace Integration.OggSmallCharacteristicIsotropyOrderCrossPollination

inductive SmallCharacteristicPrime
  | p2
  | p3
  deriving DecidableEq, Repr

def externalSupersingularAutomorphismOrder :
    SmallCharacteristicPrime → Nat
  | .p2 => 24
  | .p3 => 12

theorem p2_external_order_is_24 :
    externalSupersingularAutomorphismOrder .p2 = 24 := rfl

theorem p3_external_order_is_12 :
    externalSupersingularAutomorphismOrder .p3 = 12 := rfl

theorem p2_order_is_twice_p3_order :
    externalSupersingularAutomorphismOrder .p2 =
      2 * externalSupersingularAutomorphismOrder .p3 := by
  decide

/-- Lean-side mirror of the existing Agda affine-E6 dimension skeleton. -/
def binaryTetrahedralDimensionSquareSum : Nat :=
  3*3 + 2*2 + 2*2 + 2*2 + 1 + 1 + 1

theorem binary_tetrahedral_dimension_square_sum_is_24 :
    binaryTetrahedralDimensionSquareSum = 24 := by decide

/-- Lean-side mirror of the existing Agda rotational tetrahedral order. -/
def rotationalTetrahedralOrder : Nat := 12

theorem rotational_tetrahedral_order_is_12 :
    rotationalTetrahedralOrder = 12 := rfl

theorem p2_external_order_matches_binary_tetrahedral_skeleton :
    externalSupersingularAutomorphismOrder .p2 =
      binaryTetrahedralDimensionSquareSum := by
  decide

theorem p3_external_order_matches_rotational_tetrahedral_skeleton :
    externalSupersingularAutomorphismOrder .p3 =
      rotationalTetrahedralOrder := by
  decide

theorem skeleton_factor_two :
    binaryTetrahedralDimensionSquareSum =
      2 * rotationalTetrahedralOrder := by
  decide

inductive ClaimOrigin
  | externalOggArithmetic
  | repositoryFormalReconstruction
  | repositoryCrossModuleInference
  deriving DecidableEq, Repr

def automorphismOrderOrigin : ClaimOrigin := .externalOggArithmetic
def skeletonComparisonOrigin : ClaimOrigin := .repositoryCrossModuleInference

inductive PromotionError
  | numericalOrderMatchIdentifiesArithmeticAutomorphismGroup
  | factorTwoIdentifiesRetainedOrientationFibre
  | isotropyOrderConstructsExponentResidualSource
  deriving DecidableEq, Repr

structure Boundary where
  p2ExternalOrder24Recorded : Bool
  p3ExternalOrder12Recorded : Bool
  repo24SkeletonMirrored : Bool
  repo12SkeletonMirrored : Bool
  factorTwoSharedNumerically : Bool
  numericalMatchPromotedToGroupIsomorphism : Bool
  factorTwoPromotedToResidualOrientation : Bool
  isotropyOrderPromotedToExponentResidualSource : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  p2ExternalOrder24Recorded := true
  p3ExternalOrder12Recorded := true
  repo24SkeletonMirrored := true
  repo12SkeletonMirrored := true
  factorTwoSharedNumerically := true
  numericalMatchPromotedToGroupIsomorphism := false
  factorTwoPromotedToResidualOrientation := false
  isotropyOrderPromotedToExponentResidualSource := false

end Integration.OggSmallCharacteristicIsotropyOrderCrossPollination
