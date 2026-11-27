import Integration.F4WeylD4TrialityExact
import Mathlib

/-!
# Cross-kernel Albert/F4 derivation and triality max-cut receipt

The companion Agda branch source-writes the rational Albert algebra `H_3(O_Q)`
and its actual Jordan/cubic structure.  Exact-rational runtime calculations now
recover both the full 52-dimensional derivation space and its triality split:

  Der(J) = tri(O) + O + O + O
         = 28 + 8 + 8 + 8 = 52.

The octonion triality equation

  A(xy) = B(x)y + x C(y),  A,B,C in so(8)

has 84 skew-matrix unknowns, exact rank 56 and nullity 28; each projection to
A/B/C has rank 28.  The induced Albert block action gives 28 derivations, while
three explicit Peirce/inner families contribute independent ranks 8,8,8.  Their
combined rank is 52, exhausting the earlier derivation-space computation.

Independently, `F4WeylD4TrialityExact` pays the finite Weyl-side triality object:
`W(F4)` order 1152, normal long-root `W(D4)` order 192, three eight-element
short-root classes, quotient triality image order 6, and exact kernel D4.

The missing seam is now representation-level: identify the actual rational
triality/Peirce derivation modules with the D4 vector/spinor/cospinor roles and
prove the Lie/root intertwiner.  Neither `52` nor `1152` is used by itself as
classification authority.
-/

namespace Integration.AlbertF4DerivationMaxCutReceipt

open Integration.F4WeylD4TrialityExact

def signedMonomialOctonionOrder : Nat := 1344
def coordinateS3Order : Nat := 6
def explicitAlbertSubgroupOrder : Nat := 8064

def derivationUnknownCount : Nat := 729
def derivationConstraintRank : Nat := 677
def derivationDimension : Nat := 52
def innerCommutatorCount : Nat := 351
def innerCommutatorSpanRank : Nat := 52

def trialityUnknownCount : Nat := 84
def trialityConstraintRank : Nat := 56
def trialityDimension : Nat := 28
def peirceXDimension : Nat := 8
def peirceYDimension : Nat := 8
def peirceZDimension : Nat := 8

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

theorem triality_dimension_checksum :
    trialityUnknownCount - trialityConstraintRank = trialityDimension := by
  native_decide

theorem triality_peirce_decomposition_checksum :
    trialityDimension + peirceXDimension + peirceYDimension + peirceZDimension =
      derivationDimension := by
  native_decide

theorem finite_weyl_triality_paid :
    F4WeylD4TrialityExact.canonicalBoundary.nontrivialTrialityClassActionPaid = true ∧
    F4WeylD4TrialityExact.canonicalBoundary.trialityKernelExactlyD4Paid = true ∧
    F4WeylD4TrialityExact.canonicalBoundary.trialityImageOrderSixPaid = true := by
  decide

theorem order_trap_checksum :
    orderTrapLineStabilizer * coordinateS3Order = orderTrapProductWithS3 := by
  native_decide

inductive AgdaAlbertKernelTransferredToLean : Prop
inductive RuntimeDimensionAloneRecognizesF4 : Prop
inductive Order1152AloneRecognizesWeylF4 : Prop
inductive AlbertTrialitySameActionWithWeylD4Paid : Prop
inductive F4LieRootIntertwinerPaid : Prop
inductive FullF4RecognitionPaid : Prop

theorem no_cross_kernel_promotion : ¬ AgdaAlbertKernelTransferredToLean := by
  intro h; cases h

theorem dimension_52_alone_does_not_recognize_f4 :
    ¬ RuntimeDimensionAloneRecognizesF4 := by intro h; cases h

theorem order_1152_alone_does_not_recognize_weyl_f4 :
    ¬ Order1152AloneRecognizesWeylF4 := by intro h; cases h

theorem albert_triality_same_action_still_open :
    ¬ AlbertTrialitySameActionWithWeylD4Paid := by intro h; cases h

theorem f4_lie_root_intertwiner_still_open :
    ¬ F4LieRootIntertwinerPaid := by intro h; cases h

theorem full_f4_still_explicitly_open : ¬ FullF4RecognitionPaid := by
  intro h; cases h

structure Boundary where
  rationalAlbertCarrierSourceWrittenOnAgda : Bool
  jordanProductAndLawsSourceWrittenOnAgda : Bool
  signedMonomialAlbertLiftSourceWrittenOnAgda : Bool
  explicitAlbertSubgroup8064RuntimeChecked : Bool
  derivationRank677RuntimeChecked : Bool
  derivationDimension52RuntimeChecked : Bool
  innerSpan52RuntimeChecked : Bool
  trialityRank56Nullity28RuntimeChecked : Bool
  trialityThreeProjectionRanks28RuntimeChecked : Bool
  threePeirceRanksEightRuntimeChecked : Bool
  trialityPlusPeirceRank52RuntimeChecked : Bool
  finiteWF4Order1152PaidOnLean : Bool
  finiteD4NormalSubgroup192PaidOnLean : Bool
  finiteNontrivialS3TrialityPaidOnLean : Bool
  order1152CardinalityTrapRejected : Bool
  albertTrialitySameActionWithFiniteD4Paid : Bool
  f4LieRootIntertwinerPaid : Bool
  fullF4RecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rationalAlbertCarrierSourceWrittenOnAgda := true
  jordanProductAndLawsSourceWrittenOnAgda := true
  signedMonomialAlbertLiftSourceWrittenOnAgda := true
  explicitAlbertSubgroup8064RuntimeChecked := true
  derivationRank677RuntimeChecked := true
  derivationDimension52RuntimeChecked := true
  innerSpan52RuntimeChecked := true
  trialityRank56Nullity28RuntimeChecked := true
  trialityThreeProjectionRanks28RuntimeChecked := true
  threePeirceRanksEightRuntimeChecked := true
  trialityPlusPeirceRank52RuntimeChecked := true
  finiteWF4Order1152PaidOnLean := true
  finiteD4NormalSubgroup192PaidOnLean := true
  finiteNontrivialS3TrialityPaidOnLean := true
  order1152CardinalityTrapRejected := true
  albertTrialitySameActionWithFiniteD4Paid := false
  f4LieRootIntertwinerPaid := false
  fullF4RecognitionPaid := false

end Integration.AlbertF4DerivationMaxCutReceipt
