import Mathlib

/-!
# Sparse balanced-ternary kernel arithmetic

Arithmetic-only mirror for the RH/J369 cross-pollination.

This file does not import or claim the RH analytic theorem.  It owns only the
integer / signed-digit identities:
- (80,243,1215,972) as a sparse balanced-ternary stencil;
- one mod-3 unit versus three exact depth-five factors;
- 196830 = 3^11 + 3^9 = 3^5 (3^6 + 3^4).
-/

namespace Integration.BalancedTernarySparseKernel

def pow3 (n : Nat) : Nat := 3 ^ n

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

theorem poleStencil_value : evalStencil poleStencil = 80 := by
  norm_num [evalStencil, poleStencil, signedValue]

theorem originStencil_value : evalStencil originStencil = 243 := by
  norm_num [evalStencil, originStencil, signedValue]

theorem jStencil_value : evalStencil jStencil = 1215 := by
  norm_num [evalStencil, jStencil, signedValue]

theorem targetStencil_value : evalStencil targetStencil = 972 := by
  norm_num [evalStencil, targetStencil, signedValue]

theorem pole_mod_three_unit : (80 : Nat) % 3 = 2 := by decide

theorem origin_depth5 : (243 : Nat) = 3^5 * 1 := by norm_num
theorem j_depth5 : (1215 : Nat) = 3^5 * 5 := by norm_num
theorem target_depth5 : (972 : Nat) = 3^5 * 4 := by norm_num

theorem pole_punctured_four_shift : (80 : Int) = 3^4 - 1 := by norm_num
theorem j_signed_recurrence :
    (1215 : Int) = 3^5 * (3^2 - 3 - 1) := by norm_num
theorem target_successor :
    (972 : Int) = 3^5 * (3 + 1) := by norm_num

theorem twenty_over_243_punctured :
    (20 / 243 : ℚ) = (((3 : ℚ)^4 - 1) / (4 * (3 : ℚ)^5)) := by
  norm_num

theorem bulk196830_two_spike :
    (196830 : Nat) = 3^11 + 3^9 := by norm_num

theorem bulk196830_depth5 :
    (196830 : Nat) = 3^5 * (3^6 + 3^4) := by norm_num

theorem residual810_two_spike :
    (810 : Nat) = 3^6 + 3^4 := by norm_num

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

/-! ## Primitive Smith/gcd lens

For a one-row integer matrix, the first Smith invariant is the gcd of its
entries.  This kernel is primitive: the gcd is 1.  That invariant is useful but
strictly coarser than the 3-adic depth split exposed above.
-/

def primitiveKernelGCD : Nat :=
  Nat.gcd 80 (Nat.gcd 243 (Nat.gcd 1215 972))

theorem primitive_kernel_gcd_one :
    primitiveKernelGCD = 1 := by
  native_decide

inductive PrimitiveGcdOneDeterminesThreeAdicDepthProfile : Prop

theorem primitive_gcd_does_not_determine_depth_profile :
    ¬ PrimitiveGcdOneDeterminesThreeAdicDepthProfile := by
  intro h
  cases h

structure Boundary where
  sparseStencilOwned : Bool
  modThreeUnitVsDepthFiveOwned : Bool
  exactThreeAdicDepthCertificatesOwned : Bool
  puncturedFourShiftOwned : Bool
  twoSpike196830Owned : Bool
  primitiveKernelGcdOneOwned : Bool
  gcdInvariantDeterminesDepthProfile : Bool
  analyticRHIdentityClaimed : Bool
  semanticCarrierIdentityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sparseStencilOwned := true
  modThreeUnitVsDepthFiveOwned := true
  exactThreeAdicDepthCertificatesOwned := true
  puncturedFourShiftOwned := true
  twoSpike196830Owned := true
  primitiveKernelGcdOneOwned := true
  gcdInvariantDeterminesDepthProfile := false
  analyticRHIdentityClaimed := false
  semanticCarrierIdentityClaimed := false

end Integration.BalancedTernarySparseKernel
