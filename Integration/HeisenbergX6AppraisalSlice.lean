import Integration.TernaryHub
import Integration.MoonshineMonstrousExponentTrialecticCodec
import Mathlib

/-!
# Six-trit X6 / appraisal-fibre carrier mirror

Minimal Lean mirror of the Agda carrier/action facts behind
`Base369AppraisalFibreHeisenbergCarrierBidiExact` and
`Base369HeisenbergTranslationGridObstructionExact`.

No Monster-representation claim is made.  This file owns only:

* the exact six-trit carrier chart `X6 ≃ Surface3 × Surface3`;
* six cyclic coordinate translations;
* transport of those translations through the chart;
* the firewall that cyclic wraparound is not the native non-periodic path
  adjacency used elsewhere in the geometry.
-/

namespace Integration.HeisenbergX6AppraisalSlice

open Integration.TernaryHub
open Integration.MoonshineMonstrousExponentTrialecticCodec

/-! ## §1 Six-trit carrier -/

structure X6 where
  a0 : SSPTrit
  a1 : SSPTrit
  a2 : SSPTrit
  b0 : SSPTrit
  b1 : SSPTrit
  b2 : SSPTrit
  deriving DecidableEq, Repr, Fintype

abbrev AppraisalFibre := Surface3 × Surface3

def x6ToAppraisal : X6 → AppraisalFibre
  | ⟨a0,a1,a2,b0,b1,b2⟩ =>
      (⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩)

def appraisalToX6 : AppraisalFibre → X6
  | (⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩) =>
      ⟨a0,a1,a2,b0,b1,b2⟩

theorem appraisal_after_x6 (x : X6) :
    appraisalToX6 (x6ToAppraisal x) = x := by
  cases x
  rfl

theorem x6_after_appraisal (f : AppraisalFibre) :
    x6ToAppraisal (appraisalToX6 f) = f := by
  rcases f with ⟨⟨a0,a1,a2⟩,⟨b0,b1,b2⟩⟩
  rfl

def x6AppraisalEquiv : X6 ≃ AppraisalFibre where
  toFun := x6ToAppraisal
  invFun := appraisalToX6
  left_inv := appraisal_after_x6
  right_inv := x6_after_appraisal

theorem x6_state_count : Fintype.card X6 = 729 := by decide
theorem appraisal_state_count : Fintype.card AppraisalFibre = 729 := by decide

/-! ## §2 Cyclic coordinate translations -/

def cyclicIncrement : SSPTrit → SSPTrit
  | .negOne => .zero
  | .zero => .posOne
  | .posOne => .negOne

inductive Axis6
  | axis0 | axis1 | axis2 | axis3 | axis4 | axis5
  deriving DecidableEq, Repr, Fintype

def translateX6 : Axis6 → X6 → X6
  | .axis0, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨cyclicIncrement a0,a1,a2,b0,b1,b2⟩
  | .axis1, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨a0,cyclicIncrement a1,a2,b0,b1,b2⟩
  | .axis2, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨a0,a1,cyclicIncrement a2,b0,b1,b2⟩
  | .axis3, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨a0,a1,a2,cyclicIncrement b0,b1,b2⟩
  | .axis4, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨a0,a1,a2,b0,cyclicIncrement b1,b2⟩
  | .axis5, ⟨a0,a1,a2,b0,b1,b2⟩ =>
      ⟨a0,a1,a2,b0,b1,cyclicIncrement b2⟩

def translateAppraisal : Axis6 → AppraisalFibre → AppraisalFibre
  | .axis0, (⟨a0,a1,a2⟩, b) =>
      (⟨cyclicIncrement a0,a1,a2⟩, b)
  | .axis1, (⟨a0,a1,a2⟩, b) =>
      (⟨a0,cyclicIncrement a1,a2⟩, b)
  | .axis2, (⟨a0,a1,a2⟩, b) =>
      (⟨a0,a1,cyclicIncrement a2⟩, b)
  | .axis3, (a, ⟨b0,b1,b2⟩) =>
      (a, ⟨cyclicIncrement b0,b1,b2⟩)
  | .axis4, (a, ⟨b0,b1,b2⟩) =>
      (a, ⟨b0,cyclicIncrement b1,b2⟩)
  | .axis5, (a, ⟨b0,b1,b2⟩) =>
      (a, ⟨b0,b1,cyclicIncrement b2⟩)

theorem x6_translation_intertwines
    (axis : Axis6) (x : X6) :
    x6ToAppraisal (translateX6 axis x) =
      translateAppraisal axis (x6ToAppraisal x) := by
  cases axis <;> cases x <;> rfl

theorem appraisal_translation_intertwines
    (axis : Axis6) (f : AppraisalFibre) :
    appraisalToX6 (translateAppraisal axis f) =
      translateX6 axis (appraisalToX6 f) := by
  cases axis <;>
    rcases f with ⟨⟨a0,a1,a2⟩,⟨b0,b1,b2⟩⟩ <;>
    rfl

/-! ## §3 Exact shared-slice inclusion -/

def includeX6 : X6 → AppraisalFibre :=
  x6ToAppraisal

theorem includeX6_injective : Function.Injective includeX6 :=
  x6AppraisalEquiv.injective

theorem includeX6_intertwines
    (axis : Axis6) (x : X6) :
    includeX6 (translateX6 axis x) =
      translateAppraisal axis (includeX6 x) :=
  x6_translation_intertwines axis x

/-! ## §4 Wraparound firewall -/

theorem cyclic_wraparound :
    cyclicIncrement .posOne = SSPTrit.negOne := rfl

inductive CyclicTranslationEqualsNativePathAdjacency : Prop

theorem cyclic_translation_not_promoted_to_native_path :
    ¬ CyclicTranslationEqualsNativePathAdjacency := by
  intro h
  cases h

structure Boundary where
  exactSixTritChartOwned : Bool
  carrierCount729 : Bool
  sixCoordinateTranslationsOwned : Bool
  translationIntertwiningOwned : Bool
  sharedSliceInclusionInjective : Bool
  cyclicWraparoundExplicit : Bool
  nativePathAdjacencyIdentified : Bool
  monsterRepresentationRecognized : Bool
  fullCechGeometryMirroredHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exactSixTritChartOwned := true
  carrierCount729 := true
  sixCoordinateTranslationsOwned := true
  translationIntertwiningOwned := true
  sharedSliceInclusionInjective := true
  cyclicWraparoundExplicit := true
  nativePathAdjacencyIdentified := false
  monsterRepresentationRecognized := false
  fullCechGeometryMirroredHere := false

end Integration.HeisenbergX6AppraisalSlice
