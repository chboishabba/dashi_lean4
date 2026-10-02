import Integration.HeisenbergX6AppraisalSlice
import Integration.MoonshineTrialecticSurfaceConsumerRouting

/-!
# Trialectic / X6 carrier-action capstone

Lean currently mirrors the carrier/action part of the Agda trialectic-X6 weld:

* exact six-trit `X6 ≃ AppraisalFibre`;
* exact `T9Carrier ≃ Surface3 × X6`;
* exact six-axis cyclic translation intertwining through the appraisal chart.

The full Agda Cech face/edge/corner geometry is intentionally not claimed here.
-/

namespace Integration.TrialecticX6ModelCapstone

open Integration.HeisenbergX6AppraisalSlice
open Integration.MoonshineTrialecticSurfaceConsumerRouting

theorem x6_appraisal_exact :
    Function.Bijective x6ToAppraisal :=
  ⟨includeX6_injective, x6AppraisalEquiv.surjective⟩

theorem t9_interaction_x6_exact :
    Function.Bijective t9ToInteractionX6 :=
  ⟨t9InteractionX6Equiv.injective, t9InteractionX6Equiv.surjective⟩

theorem x6_translation_transport_exact
    (axis : Axis6) (x : X6) :
    x6ToAppraisal (translateX6 axis x) =
      translateAppraisal axis (x6ToAppraisal x) :=
  x6_translation_intertwines axis x

structure Boundary where
  x6AppraisalBijectionOwned : Bool
  t9FactorsAsInteractionTimesX6 : Bool
  sixAxisTranslationIntertwiningOwned : Bool
  x6StateCount729 : Bool
  t9StateCount19683 : Bool
  fullAgdaCechGeometryMirrored : Bool
  monsterRepresentationRecognized : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  x6AppraisalBijectionOwned := true
  t9FactorsAsInteractionTimesX6 := true
  sixAxisTranslationIntertwiningOwned := true
  x6StateCount729 := true
  t9StateCount19683 := true
  fullAgdaCechGeometryMirrored := false
  monsterRepresentationRecognized := false

end Integration.TrialecticX6ModelCapstone
