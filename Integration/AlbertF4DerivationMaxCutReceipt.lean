import Mathlib

/-!
# Cross-kernel Albert/F4 derivation max-cut receipt

The companion Agda branch now source-writes an actual rational Albert algebra
`H_3(O_Q)`, its cubic norm, Jordan product/laws, explicit coordinate `S3`
automorphisms, explicit signed-monomial octonion automorphisms and their Albert
lift.

Independent exact-rational Python checks on those literal coordinate formulas
produce:

* 1344 signed-monomial octonion basis automorphisms;
* 8064 elements in the explicitly generated Albert automorphism subgroup after
  adjoining the coordinate `S3`;
* 729 unknown entries in a general 27x27 endomorphism;
* derivation-constraint rank 677;
* derivation nullity 52;
* rank 52 for the span of all 351 inner commutators `[L_ei,L_ej]`.

A separate order-only control gives `192 * 6 = 1152`, but that commuting
construction is deliberately NOT identified with `W(F4)`: genuine F4 requires
nontrivial D4 triality/root data, not the right order alone.

This Lean file is a typed cross-kernel status/arithmetical receipt only.  It does
not promote Agda source or Python runtime calculations to Lean kernel theorems.
-/

namespace Integration.AlbertF4DerivationMaxCutReceipt

def signedMonomialOctonionOrder : Nat := 1344
def coordinateS3Order : Nat := 6
def explicitAlbertSubgroupOrder : Nat := 8064

def derivationUnknownCount : Nat := 729
def derivationConstraintRank : Nat := 677
def derivationDimension : Nat := 52
def innerCommutatorCount : Nat := 351
def innerCommutatorSpanRank : Nat := 52

def orderTrapLineStabilizer : Nat := 192
def orderTrapProductWithS3 : Nat := 1152

theorem explicit_subgroup_checksum :
    signedMonomialOctonionOrder * coordinateS3Order = explicitAlbertSubgroupOrder := by
  native_decide

theorem derivation_dimension_checksum :
    derivationUnknownCount - derivationConstraintRank = derivationDimension := by
  native_decide

theorem inner_span_matches_derivation_dimension :
    innerCommutatorSpanRank = derivationDimension := rfl

theorem order_trap_checksum :
    orderTrapLineStabilizer * coordinateS3Order = orderTrapProductWithS3 := by
  native_decide

inductive AgdaAlbertKernelTransferredToLean : Prop
inductive RuntimeDimensionAloneRecognizesF4 : Prop
inductive Order1152AloneRecognizesWeylF4 : Prop
inductive NontrivialD4TrialityPaid : Prop
inductive FullF4RecognitionPaid : Prop

theorem no_cross_kernel_promotion : ¬ AgdaAlbertKernelTransferredToLean := by
  intro h; cases h

theorem dimension_52_alone_does_not_recognize_f4 :
    ¬ RuntimeDimensionAloneRecognizesF4 := by intro h; cases h

theorem order_1152_alone_does_not_recognize_weyl_f4 :
    ¬ Order1152AloneRecognizesWeylF4 := by intro h; cases h

theorem d4_triality_still_explicitly_open : ¬ NontrivialD4TrialityPaid := by
  intro h; cases h

theorem full_f4_still_explicitly_open : ¬ FullF4RecognitionPaid := by
  intro h; cases h

structure Boundary where
  rationalAlbertCarrierSourceWrittenOnAgda : Bool
  cubicNormSourceWrittenOnAgda : Bool
  jordanProductAndLawsSourceWrittenOnAgda : Bool
  coordinateS3AutomorphismsSourceWrittenOnAgda : Bool
  signedMonomialOctonionAutomorphismsSourceWrittenOnAgda : Bool
  signedMonomialAlbertLiftSourceWrittenOnAgda : Bool
  signedMonomialClosure1344RuntimeChecked : Bool
  explicitAlbertSubgroup8064RuntimeChecked : Bool
  derivationRank677RuntimeChecked : Bool
  derivationDimension52RuntimeChecked : Bool
  innerSpan52RuntimeChecked : Bool
  order1152RejectedAsRecognition : Bool
  nontrivialD4TrialityPaid : Bool
  fullF4RecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rationalAlbertCarrierSourceWrittenOnAgda := true
  cubicNormSourceWrittenOnAgda := true
  jordanProductAndLawsSourceWrittenOnAgda := true
  coordinateS3AutomorphismsSourceWrittenOnAgda := true
  signedMonomialOctonionAutomorphismsSourceWrittenOnAgda := true
  signedMonomialAlbertLiftSourceWrittenOnAgda := true
  signedMonomialClosure1344RuntimeChecked := true
  explicitAlbertSubgroup8064RuntimeChecked := true
  derivationRank677RuntimeChecked := true
  derivationDimension52RuntimeChecked := true
  innerSpan52RuntimeChecked := true
  order1152RejectedAsRecognition := true
  nontrivialD4TrialityPaid := false
  fullF4RecognitionPaid := false

end Integration.AlbertF4DerivationMaxCutReceipt
