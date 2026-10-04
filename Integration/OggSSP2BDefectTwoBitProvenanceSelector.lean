import Integration.OggSSP2BDefectRecognitionAmbiguity

/-!
# Final D max-cut: two provenance bits select the defect-compatible chart

The sourced defect profile leaves exactly four charts.  Its multiplicities show
precisely where the ambiguity lives:

* depth 3: mode09/mode18 must map to identity/centralMinusOne, but source data
  must decide which orientation;
* depth 2: mode27 -> orderFour is forced;
* depth 1: mode36/mode45 must map to orderThree/orderSix, but source data must
  decide which orientation.

Thus D no longer needs an arbitrary five-label bijection.  It needs exactly two
independent source decisions.  This file compiles those decisions into the
existing `FiveModeDefectRecognition` type.  It does not fabricate their
provenance.
-/

namespace Integration.OggSSP2BDefectTwoBitProvenanceSelector

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture
namespace D := Integration.OggSSP2BBinaryTetrahedralDefectSource
namespace A := Integration.OggSSP2BDefectRecognitionAmbiguity

/-- First bit: which depth-3 Completion10 mode is the identity stratum. -/
inductive DepthThreeOrientation
  | mode09IsIdentity
  | mode18IsIdentity
  deriving DecidableEq, Repr, Fintype

/-- Second bit: which depth-1 Completion10 mode is the order-3 stratum. -/
inductive DepthOneOrientation
  | mode36IsOrderThree
  | mode45IsOrderThree
  deriving DecidableEq, Repr, Fintype

structure ProvenanceBits where
  depthThree : DepthThreeOrientation
  depthOne : DepthOneOrientation
  deriving DecidableEq, Repr, Fintype

 theorem provenance_bit_count : Fintype.card ProvenanceBits = 4 := by
  native_decide

private def chart00 : F.Mode5 ≃ D.OrderStratum where
  toFun
    | .mode09 => .identity
    | .mode18 => .centralMinusOne
    | .mode27 => .orderFour
    | .mode36 => .orderThree
    | .mode45 => .orderSix
  invFun
    | .identity => .mode09
    | .centralMinusOne => .mode18
    | .orderFour => .mode27
    | .orderThree => .mode36
    | .orderSix => .mode45
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro s; cases s <;> rfl

private def chart10 : F.Mode5 ≃ D.OrderStratum where
  toFun
    | .mode09 => .centralMinusOne
    | .mode18 => .identity
    | .mode27 => .orderFour
    | .mode36 => .orderThree
    | .mode45 => .orderSix
  invFun
    | .identity => .mode18
    | .centralMinusOne => .mode09
    | .orderFour => .mode27
    | .orderThree => .mode36
    | .orderSix => .mode45
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro s; cases s <;> rfl

private def chart01 : F.Mode5 ≃ D.OrderStratum where
  toFun
    | .mode09 => .identity
    | .mode18 => .centralMinusOne
    | .mode27 => .orderFour
    | .mode36 => .orderSix
    | .mode45 => .orderThree
  invFun
    | .identity => .mode09
    | .centralMinusOne => .mode18
    | .orderFour => .mode27
    | .orderThree => .mode45
    | .orderSix => .mode36
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro s; cases s <;> rfl

private def chart11 : F.Mode5 ≃ D.OrderStratum where
  toFun
    | .mode09 => .centralMinusOne
    | .mode18 => .identity
    | .mode27 => .orderFour
    | .mode36 => .orderSix
    | .mode45 => .orderThree
  invFun
    | .identity => .mode18
    | .centralMinusOne => .mode09
    | .orderFour => .mode27
    | .orderThree => .mode45
    | .orderSix => .mode36
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro s; cases s <;> rfl

/-- The four, and only four by the previous counting theorem, defect-compatible
charts expressed as the two unresolved source orientations. -/
def chartFromBits : ProvenanceBits → (F.Mode5 ≃ D.OrderStratum)
  | ⟨.mode09IsIdentity, .mode36IsOrderThree⟩ => chart00
  | ⟨.mode18IsIdentity, .mode36IsOrderThree⟩ => chart10
  | ⟨.mode09IsIdentity, .mode45IsOrderThree⟩ => chart01
  | ⟨.mode18IsIdentity, .mode45IsOrderThree⟩ => chart11

theorem chartFromBits_defect_compatible (b : ProvenanceBits) :
    A.DefectCompatible (chartFromBits b) := by
  rcases b with ⟨d3,d1⟩
  cases d3 <;> cases d1 <;> intro m <;> cases m <;> rfl

/-- `mode27 -> orderFour` needs no provenance bit: the unique depth-2 stratum
forces it in every one of the four charts. -/
theorem orderFour_is_forced (b : ProvenanceBits) :
    chartFromBits b .mode27 = .orderFour := by
  rcases b with ⟨d3,d1⟩
  cases d3 <;> cases d1 <;> rfl

/-- Source receipt for D.  The mathematical payload is now only the two
orientation decisions plus independent provenance for those decisions. -/
structure TwoBitSourceReceipt where
  bits : ProvenanceBits
  depthThreeSourceProvenance : String
  depthOneSourceProvenance : String

/-- Compile the two source decisions into the pre-existing final D receipt. -/
def TwoBitSourceReceipt.toFiveModeDefectRecognition
    (r : TwoBitSourceReceipt) : D.FiveModeDefectRecognition where
  modeToOrderStratum := chartFromBits r.bits
  defectIntertwines := chartFromBits_defect_compatible r.bits
  sourceProvenance :=
    "depth-3: " ++ r.depthThreeSourceProvenance ++
    "; depth-1: " ++ r.depthOneSourceProvenance

/-- Defect data itself cannot fill either source decision. -/
inductive DefectProfileConstructsTwoProvenanceBits : Prop

theorem defect_profile_cannot_construct_two_source_bits :
    ¬ DefectProfileConstructsTwoProvenanceBits := by
  intro h
  cases h

end Integration.OggSSP2BDefectTwoBitProvenanceSelector
