import Mathlib

/-!
# RH primitive integer kernel as a sparse balanced-ternary stencil

This module formalizes only the exact integer arithmetic of the coefficient
vector

  (80, 243, 1215, 972).

It exposes the sparse ternary-shift form

  80   = 3^4 - 1
  243  = 3^5
  1215 = 3^7 - 3^6 - 3^5 = 3^5 * (3^2 - 3 - 1)
  972  = 3^6 + 3^5       = 3^5 * (3 + 1).

No RH, Monster, or geometric same-object claim is made here.
-/

namespace Integration.RiemannPrimitiveKernelBalancedTernaryStencil

def pow3 (n : Nat) : Nat := 3 ^ n

def poleCoefficient : Nat := pow3 4 - 1
def originCoefficient : Nat := pow3 5
def jCoefficient : Nat := pow3 7 - pow3 6 - pow3 5
def sCoefficient : Nat := pow3 6 + pow3 5

theorem pole_coefficient_is_80 : poleCoefficient = 80 := by norm_num [poleCoefficient, pow3]
theorem origin_coefficient_is_243 : originCoefficient = 243 := by norm_num [originCoefficient, pow3]
theorem j_coefficient_is_1215 : jCoefficient = 1215 := by norm_num [jCoefficient, pow3]
theorem s_coefficient_is_972 : sCoefficient = 972 := by norm_num [sCoefficient, pow3]

def jResidualStencil : Nat := pow3 2 - 3 - 1
def sResidualStencil : Nat := 3 + 1

theorem j_residual_stencil_is_five : jResidualStencil = 5 := by norm_num [jResidualStencil, pow3]
theorem s_residual_stencil_is_four : sResidualStencil = 4 := by norm_num [sResidualStencil]

theorem origin_depth_five :
    originCoefficient = pow3 5 * 1 := by
  norm_num [originCoefficient, pow3]

theorem j_depth_five :
    jCoefficient = pow3 5 * jResidualStencil := by
  norm_num [jCoefficient, jResidualStencil, pow3]

theorem s_depth_five :
    sCoefficient = pow3 5 * sResidualStencil := by
  norm_num [sCoefficient, sResidualStencil, pow3]

inductive NonzeroTernaryResidue
  | one
  | two
  deriving DecidableEq, Repr

def residueValue : NonzeroTernaryResidue → Nat
  | .one => 1
  | .two => 2

structure ExactThreeAdicDepthWitness (coefficient : Nat) where
  depth : Nat
  unit : Nat
  factorization : coefficient = pow3 depth * unit
  unitResidue : NonzeroTernaryResidue
  residueExact : unit % 3 = residueValue unitResidue

def poleDepthZero : ExactThreeAdicDepthWitness poleCoefficient where
  depth := 0
  unit := 80
  factorization := by norm_num [poleCoefficient, pow3]
  unitResidue := .two
  residueExact := by norm_num [residueValue]

def originDepthFive : ExactThreeAdicDepthWitness originCoefficient where
  depth := 5
  unit := 1
  factorization := by norm_num [originCoefficient, pow3]
  unitResidue := .one
  residueExact := by norm_num [residueValue]

def jDepthFive : ExactThreeAdicDepthWitness jCoefficient where
  depth := 5
  unit := 5
  factorization := by norm_num [jCoefficient, pow3]
  unitResidue := .two
  residueExact := by norm_num [residueValue]

def sDepthFive : ExactThreeAdicDepthWitness sCoefficient where
  depth := 5
  unit := 4
  factorization := by norm_num [sCoefficient, pow3]
  unitResidue := .one
  residueExact := by norm_num [residueValue]

def threeAdicDepthProfile : Nat × Nat × Nat × Nat :=
  (poleDepthZero.depth, originDepthFive.depth, jDepthFive.depth, sDepthFive.depth)

theorem three_adic_depth_profile_exact :
    threeAdicDepthProfile = (0, 5, 5, 5) := rfl

inductive SpikeSign
  | positive
  | negative
  deriving DecidableEq, Repr

structure SignedSpike where
  exponent : Nat
  sign : SpikeSign
  deriving DecidableEq, Repr

def poleStencil : List SignedSpike :=
  [⟨4, .positive⟩, ⟨0, .negative⟩]

def originStencil : List SignedSpike :=
  [⟨5, .positive⟩]

def jStencil : List SignedSpike :=
  [⟨7, .positive⟩, ⟨6, .negative⟩, ⟨5, .negative⟩]

def sStencil : List SignedSpike :=
  [⟨6, .positive⟩, ⟨5, .positive⟩]

theorem x_plus_one_at_three : 3 + 1 = 4 := by norm_num
theorem x_squared_minus_x_minus_one_at_three :
    3^2 - 3 - 1 = 5 := by norm_num

inductive PromotionError
  | sparseStencilProvesRH
  | polynomialAtThreeIdentifiesGoldenRatioDynamics
  | puncturedCoefficientConstructsEightyPointCarrier
  deriving DecidableEq, Repr

structure Boundary where
  decimalCoefficientVectorRecovered : Bool
  sparseSignedTernaryStencilOwned : Bool
  commonDepthFiveFactorOwned : Bool
  exactThreeAdicProfileZeroFiveFiveFiveOwned : Bool
  puncturedFourShiftOwned : Bool
  goldenPolynomialOnlyEvaluatedAtThree : Bool
  rhClosedHere : Bool
  eightyPointCarrierConstructedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  decimalCoefficientVectorRecovered := true
  sparseSignedTernaryStencilOwned := true
  commonDepthFiveFactorOwned := true
  exactThreeAdicProfileZeroFiveFiveFiveOwned := true
  puncturedFourShiftOwned := true
  goldenPolynomialOnlyEvaluatedAtThree := true
  rhClosedHere := false
  eightyPointCarrierConstructedHere := false

end Integration.RiemannPrimitiveKernelBalancedTernaryStencil
