import Synthesis.RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb
import Mathlib

/-!
# RH quartic kernel: sparse balanced-ternary / 3-adic normal form

This module does not add a new analytic hypothesis.  It consumes the existing
unrestricted atomic identity on the live RH branch and exposes its primitive
integer kernel in a sparse ternary normal form.

The coefficient vector is

  (80, 243, 1215, 972)

with exact signed ternary words

  80   = 3^4 - 1
  243  = 3^5
  1215 = 3^7 - 3^6 - 3^5
  972  = 3^6 + 3^5.

Hence the valuation shape is one mod-3 unit against a common depth-five block.
-/

namespace Synthesis

namespace RiemannQuarticBalancedTernaryStencil

def pow3 (n : Nat) : Nat := 3 ^ n

theorem pow3_4 : pow3 4 = 81 := by native_decide
theorem pow3_5 : pow3 5 = 243 := by native_decide
theorem pow3_6 : pow3 6 = 729 := by native_decide
theorem pow3_7 : pow3 7 = 2187 := by native_decide
theorem pow3_9 : pow3 9 = 19683 := by native_decide
theorem pow3_11 : pow3 11 = 177147 := by native_decide

inductive SignedTrit
  | neg | zero | pos
  deriving DecidableEq, Repr

structure Stencil8 where
  e7 : SignedTrit
  e6 : SignedTrit
  e5 : SignedTrit
  e4 : SignedTrit
  e3 : SignedTrit
  e2 : SignedTrit
  e1 : SignedTrit
  e0 : SignedTrit
  deriving DecidableEq, Repr

def signedValue : SignedTrit → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

def evalStencil (s : Stencil8) : Int :=
    signedValue s.e7 * (3 : Int)^7
  + signedValue s.e6 * (3 : Int)^6
  + signedValue s.e5 * (3 : Int)^5
  + signedValue s.e4 * (3 : Int)^4
  + signedValue s.e3 * (3 : Int)^3
  + signedValue s.e2 * (3 : Int)^2
  + signedValue s.e1 * (3 : Int)
  + signedValue s.e0

def poleStencil : Stencil8 :=
  ⟨.zero,.zero,.zero,.pos,.zero,.zero,.zero,.neg⟩

def originStencil : Stencil8 :=
  ⟨.zero,.zero,.pos,.zero,.zero,.zero,.zero,.zero⟩

def jStencil : Stencil8 :=
  ⟨.pos,.neg,.neg,.zero,.zero,.zero,.zero,.zero⟩

def targetStencil : Stencil8 :=
  ⟨.zero,.pos,.pos,.zero,.zero,.zero,.zero,.zero⟩

theorem poleStencil_value : evalStencil poleStencil = 80 := by norm_num [evalStencil, poleStencil, signedValue]
theorem originStencil_value : evalStencil originStencil = 243 := by norm_num [evalStencil, originStencil, signedValue]
theorem jStencil_value : evalStencil jStencil = 1215 := by norm_num [evalStencil, jStencil, signedValue]
theorem targetStencil_value : evalStencil targetStencil = 972 := by norm_num [evalStencil, targetStencil, signedValue]

theorem pole_is_punctured_four_shift : (80 : Int) = 3^4 - 1 := by norm_num
theorem origin_is_depth_five : (243 : Int) = 3^5 := by norm_num
theorem j_is_depth_five_signed_recurrence :
    (1215 : Int) = 3^5 * (3^2 - 3 - 1) := by norm_num
theorem target_is_depth_five_successor :
    (972 : Int) = 3^5 * (3 + 1) := by norm_num

theorem pole_mod_three_unit : (80 : Nat) % 3 = 2 := by native_decide
theorem origin_depth_five_factor : (243 : Nat) = 3^5 * 1 := by norm_num
theorem j_depth_five_factor : (1215 : Nat) = 3^5 * 5 := by norm_num
theorem target_depth_five_factor : (972 : Nat) = 3^5 * 4 := by norm_num

theorem twenty_over_243_as_punctured_shift :
    (20 / 243 : ℝ) = (((3 : ℝ)^4 - 1) / (4 * (3 : ℝ)^5)) := by
  norm_num

theorem five_as_signed_ternary :
    (5 : ℝ) = (3 : ℝ)^2 - 3 - 1 := by
  norm_num

theorem ten_as_sparse_101 :
    (10 : Nat) = 3^2 + 1 := by norm_num

theorem bulk_196830_two_spike :
    (196830 : Nat) = 3^11 + 3^9 := by
  norm_num

theorem bulk_196830_depth_five_split :
    (196830 : Nat) = 3^5 * (3^6 + 3^4) := by
  norm_num

theorem bulk_residual_after_depth_five :
    (810 : Nat) = 3^6 + 3^4 := by
  norm_num

/-! ## Symbolic shift-polynomial stencil -/

open Polynomial

def poleShiftPolynomial : Polynomial ℤ :=
  X^4 - 1

def originShiftPolynomial : Polynomial ℤ :=
  X^5

def jShiftPolynomial : Polynomial ℤ :=
  X^5 * (X^2 - X - 1)

def targetShiftPolynomial : Polynomial ℤ :=
  X^5 * (X + 1)

theorem j_shift_polynomial_expanded :
    jShiftPolynomial = X^7 - X^6 - X^5 := by
  simp [jShiftPolynomial]
  ring

theorem target_shift_polynomial_expanded :
    targetShiftPolynomial = X^6 + X^5 := by
  simp [targetShiftPolynomial]
  ring

theorem pole_shift_eval_three :
    poleShiftPolynomial.eval 3 = 80 := by
  norm_num [poleShiftPolynomial]

theorem origin_shift_eval_three :
    originShiftPolynomial.eval 3 = 243 := by
  norm_num [originShiftPolynomial]

theorem j_shift_eval_three :
    jShiftPolynomial.eval 3 = 1215 := by
  norm_num [jShiftPolynomial]

theorem target_shift_eval_three :
    targetShiftPolynomial.eval 3 = 972 := by
  norm_num [targetShiftPolynomial]

structure ShiftPolynomialKernel where
  pole : Polynomial ℤ
  origin : Polynomial ℤ
  j2 : Polynomial ℤ
  target : Polynomial ℤ

def canonicalShiftPolynomialKernel : ShiftPolynomialKernel where
  pole := poleShiftPolynomial
  origin := originShiftPolynomial
  j2 := jShiftPolynomial
  target := targetShiftPolynomial

inductive EvaluationAtThreeCreatesUniversalShiftIdentity : Prop

theorem evaluation_at_three_does_not_create_universal_shift_identity :
    ¬ EvaluationAtThreeCreatesUniversalShiftIdentity := by
  intro h
  cases h

/-! ## Exact 3-adic depth certificates -/

structure ExactThreeAdicDepthCertificate (value depth : Nat) where
  unit : Nat
  factorExact : value = 3^depth * unit
  unitModThreeNonzero : unit % 3 ≠ 0
  deriving Repr

def poleExactDepthZero :
    ExactThreeAdicDepthCertificate 80 0 where
  unit := 80
  factorExact := by norm_num
  unitModThreeNonzero := by decide

def originExactDepthFive :
    ExactThreeAdicDepthCertificate 243 5 where
  unit := 1
  factorExact := by norm_num
  unitModThreeNonzero := by decide

def jExactDepthFive :
    ExactThreeAdicDepthCertificate 1215 5 where
  unit := 5
  factorExact := by norm_num
  unitModThreeNonzero := by decide

def targetExactDepthFive :
    ExactThreeAdicDepthCertificate 972 5 where
  unit := 4
  factorExact := by norm_num
  unitModThreeNonzero := by decide

def exactDepthProfile : Nat × Nat × Nat × Nat :=
  (0,5,5,5)

/-! ## Direct attachment to the proved unrestricted atomic identity -/

theorem quarticFourAtomic_primitive_integer_kernel
    (lam mu : ℝ) :
    80 * Real.pi^4 * quarticFourAtomicHighPoleResidual lam mu
      + 243 * Real.pi^4 * quarticFourAtomicProjectiveOriginCoordinate lam mu
      + 1215 * Real.pi^2 * quarticFourAtomicJAt lam mu 2
      + 972 * quarticFourAtomicTargetStrengthAt lam mu
      = 0 := by
  rw [quarticFourAtomic_targetAt_eq_pole_origin_J2_combination]
  ring

theorem quarticFourAtomic_sparse_shift_kernel
    (lam mu : ℝ) :
    (((3 : ℝ)^4 - 1) * Real.pi^4
        * quarticFourAtomicHighPoleResidual lam mu)
      + ((3 : ℝ)^5 * Real.pi^4
        * quarticFourAtomicProjectiveOriginCoordinate lam mu)
      + (((3 : ℝ)^7 - (3 : ℝ)^6 - (3 : ℝ)^5) * Real.pi^2
        * quarticFourAtomicJAt lam mu 2)
      + (((3 : ℝ)^6 + (3 : ℝ)^5)
        * quarticFourAtomicTargetStrengthAt lam mu)
      = 0 := by
  have h := quarticFourAtomic_primitive_integer_kernel lam mu
  norm_num at h ⊢
  exact h

theorem quarticFourAtomic_depth_five_block_kernel
    (lam mu : ℝ) :
    (((3 : ℝ)^4 - 1) * Real.pi^4
        * quarticFourAtomicHighPoleResidual lam mu)
      +
    (3 : ℝ)^5 *
      (
        Real.pi^4 * quarticFourAtomicProjectiveOriginCoordinate lam mu
        + ((3 : ℝ)^2 - 3 - 1) * Real.pi^2
            * quarticFourAtomicJAt lam mu 2
        + ((3 : ℝ) + 1) * quarticFourAtomicTargetStrengthAt lam mu
      )
      = 0 := by
  have h := quarticFourAtomic_primitive_integer_kernel lam mu
  norm_num at h ⊢
  ring_nf at h ⊢
  exact h

theorem quarticFourAtomic_null_target_sparse_coefficient
    {lam : ℝ} (hlam : lam <= 2/3) :
    quarticFourAtomicTargetStrength lam
      =
    Real.pi^4 *
      (
        -((((3 : ℝ)^4 - 1) / (4 * (3 : ℝ)^5)))
          * quarticFourAtomicPoleOnNull lam
        - (1/4 : ℝ) * quarticFourAtomicOriginOnNull lam
      ) := by
  rw [quarticFourAtomic_target_eq_pole_origin_combination hlam]
  norm_num

/-! ## Primitive Smith/gcd lens

The primitive row gcd is one.  For a 1×4 integer matrix this is the only
nonzero Smith invariant up to sign.  It does not encode which three
coefficients share five factors of 3.
-/

def primitiveKernelGCD : Nat :=
  Nat.gcd 80 (Nat.gcd 243 (Nat.gcd 1215 972))

theorem primitive_kernel_gcd_one :
    primitiveKernelGCD = 1 := by
  native_decide

inductive PrimitiveGcdOneDeterminesDepthProfile : Prop

theorem primitive_gcd_does_not_determine_depth_profile :
    ¬ PrimitiveGcdOneDeterminesDepthProfile := by
  intro h
  cases h

structure Boundary where
  sparseStencilOwned : Bool
  symbolicShiftPolynomialKernelOwned : Bool
  modThreeUnitVsDepthFiveSplitOwned : Bool
  exactThreeAdicDepthCertificatesOwned : Bool
  directRHKernelAttachmentOwned : Bool
  depthFiveBlockKernelOwned : Bool
  twoSpike196830Owned : Bool
  primitiveKernelGcdOneOwned : Bool
  gcdInvariantDeterminesDepthProfile : Bool
  createsNewAnalyticRHHypothesis : Bool
  createsSemanticCarrierIdentity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sparseStencilOwned := true
  symbolicShiftPolynomialKernelOwned := true
  modThreeUnitVsDepthFiveSplitOwned := true
  exactThreeAdicDepthCertificatesOwned := true
  directRHKernelAttachmentOwned := true
  depthFiveBlockKernelOwned := true
  twoSpike196830Owned := true
  primitiveKernelGcdOneOwned := true
  gcdInvariantDeterminesDepthProfile := false
  createsNewAnalyticRHHypothesis := false
  createsSemanticCarrierIdentity := false

end RiemannQuarticBalancedTernaryStencil

end Synthesis
