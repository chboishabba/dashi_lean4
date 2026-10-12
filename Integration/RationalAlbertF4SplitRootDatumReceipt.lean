import Integration.RationalAlbertF4CartanNative
import Integration.E6F4ShortRootRecognition
import Integration.RationalAlbertF4LieMaxCut
import Mathlib

/-!
# Split F4 root-datum cross-kernel receipt

Lean owns two theorem-bearing pieces on the same programme:

* the literal native rational Albert algebra and the four same-object Cartan
  inner derivations in `RationalAlbertF4CartanNative`;
* an independently constructed standard F4 finite root/Coxeter datum with
  48 roots in `E6F4ShortRootRecognition`.

The companion Agda branch now additionally owns exact executable, floating-free
Q(i) producers on the same rational Albert coordinate formulas:

* zero joint weight dimension 4;
* 48 nonzero one-dimensional weight/root spaces, split 24+8+8+8;
* exact symbolic spectral projectors;
* all 1128 unordered root-pair brackets checked exactly;
* 408 nonzero root-sum brackets, 24 opposite-root Cartan brackets and 696
  forbidden-sum zero brackets;
* split F4 root-datum recognition.

Those companion results are recorded here as provenance/receipt coordinates,
not imported as Lean theorem authority.  This owner therefore closes the
programme-level split-root-datum ledger while keeping Lean-internal Q(i)
projectors and the original-Q-form/algebraic-group classification separate.
-/

namespace Integration.RationalAlbertF4SplitRootDatumReceipt

open Integration.RationalAlbertF4CartanNative
open Integration.E6F4ShortRootRecognition

structure CompanionExactQIReceipt where
  sourceOwner : String
  splittingField : String
  cartanDimension : Nat
  zeroWeightDimension : Nat
  nonzeroRootSpaces : Nat
  eachNonzeroRootSpaceDimension : Nat
  d4Roots : Nat
  vectorWeights : Nat
  spinPlusWeights : Nat
  spinMinusWeights : Nat
  unorderedRootPairsChecked : Nat
  rootSumNonzeroBrackets : Nat
  oppositeRootCartanBrackets : Nat
  forbiddenRootSumZeroBrackets : Nat
  symbolicProjectorsExact : Bool
  floatingPointUsed : Bool
  exactRootGradingPaid : Bool
  splitF4RootDatumRecognized : Bool
  deriving Repr

/-- Companion-Agda exact producer receipt; this is metadata/provenance in Lean,
not cross-kernel theorem import. -/
def companionExactQI : CompanionExactQIReceipt where
  sourceOwner :=
    "DASHI.Mathematics.Algebra.RationalAlbertF4SplitRootDatumRecognitionExact"
  splittingField := "Q(i)"
  cartanDimension := 4
  zeroWeightDimension := 4
  nonzeroRootSpaces := 48
  eachNonzeroRootSpaceDimension := 1
  d4Roots := 24
  vectorWeights := 8
  spinPlusWeights := 8
  spinMinusWeights := 8
  unorderedRootPairsChecked := 1128
  rootSumNonzeroBrackets := 408
  oppositeRootCartanBrackets := 24
  forbiddenRootSumZeroBrackets := 696
  symbolicProjectorsExact := true
  floatingPointUsed := false
  exactRootGradingPaid := true
  splitF4RootDatumRecognized := true

/-- Lean independently pays the literal 48-root finite F4 datum. -/
theorem lean_f4_root_count_48 : f4RootSet.card = 48 := f4_root_card_48

theorem lean_f4_short_count_24 : f4ShortRootSet.card = 24 := f4_short_root_card_24

theorem lean_f4_long_count_24 : f4LongRootSet.card = 24 := f4_long_root_card_24

/-- Lean independently pays the native same-object Cartan, rather than merely
recording the companion producer's four-dimensional count. -/
theorem lean_native_cartan_commutes :
    ∀ i j X,
      cartanDerivation i (cartanDerivation j X) =
        cartanDerivation j (cartanDerivation i X) :=
  cartan_commute

structure Boundary where
  nativeCartanSameObjectPaid : Bool
  nativeCartanTrialityRolesPaid : Bool
  companionExactQIRootSpacesPaid : Bool
  companionExactRootGradingPaid : Bool
  independentLeanF4RootDatumPaid : Bool
  splitF4RootDatumRecognizedCrossKernel : Bool
  crossKernelReceiptCreatesLeanProofAuthority : Bool
  leanInternalQIRootProjectorsPaid : Bool
  rationalFormClassificationPaid : Bool
  fullAutJEqualsF4Paid : Bool
  e6UnitStabilizerEqualsF4Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  nativeCartanSameObjectPaid := true
  nativeCartanTrialityRolesPaid := true
  companionExactQIRootSpacesPaid := true
  companionExactRootGradingPaid := true
  independentLeanF4RootDatumPaid := true
  splitF4RootDatumRecognizedCrossKernel := true
  crossKernelReceiptCreatesLeanProofAuthority := false
  leanInternalQIRootProjectorsPaid := false
  rationalFormClassificationPaid := false
  fullAutJEqualsF4Paid := false
  e6UnitStabilizerEqualsF4Paid := false

inductive CrossKernelReceiptCreatesLeanProof : Prop

theorem cross_kernel_receipt_does_not_create_lean_proof :
    ¬ CrossKernelReceiptCreatesLeanProof := by intro h; cases h

end Integration.RationalAlbertF4SplitRootDatumReceipt
