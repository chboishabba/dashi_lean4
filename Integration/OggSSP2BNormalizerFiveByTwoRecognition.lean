import Integration.OggSSP2BFiveByTwoDefectArchitecture
import Integration.OggSSP2BResidualC4BinaryPhaseNoGo

/-!
# Same-object recognition target for a nontrivial five-by-two 2B Tate sector

The cyclic 4A/C2 residual action is proved trivial on each non-acyclic ordinary
Tate class.  Therefore a genuine BinaryPhase flip must come from additional
source structure, e.g. a 2B centralizer/normalizer/local-inertia action.

This record states the exact same-object requirement on the actual weight-two
276-dimensional Tate multiplicity: ten selected source coordinates embed into
Fin 276 and an involution J preserves that image while acting as the already
owned ten-state complement.

No inhabitant is fabricated here.  Theorems below show what follows from such
an inhabitant and why J must be genuinely nontrivial.
-/

namespace Integration.OggSSP2BNormalizerFiveByTwoRecognition

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture

abbrev ActualWeightTwoTateIndex := Fin 276

record FiveByTwoRecognition where
  embed : F.TenState → ActualWeightTwoTateIndex
  injective : Function.Injective embed

  action : ActualWeightTwoTateIndex → ActualWeightTwoTateIndex
  actionInvolutive : ∀ i, action (action i) = i

  sameObjectBinaryFlip :
    ∀ s, action (embed s) = embed (F.complement s)

open FiveByTwoRecognition

theorem selected_image_is_action_invariant
    (r : FiveByTwoRecognition) (s : F.TenState) :
    ∃ t : F.TenState, r.action (r.embed s) = r.embed t := by
  exact ⟨F.complement s, r.sameObjectBinaryFlip s⟩

theorem action_nontrivial_on_selected_image
    (r : FiveByTwoRecognition) :
    ∃ i : ActualWeightTwoTateIndex, r.action i ≠ i := by
  refine ⟨r.embed F.TenState.d0, ?_⟩
  rw [r.sameObjectBinaryFlip]
  intro h
  have hs := r.injective h
  norm_num [F.complement, F.encode, F.decode, F.flipPhase] at hs

theorem selected_pair_is_swapped
    (r : FiveByTwoRecognition) :
    r.action (r.embed F.TenState.d0) = r.embed F.TenState.j9
    ∧
    r.action (r.embed F.TenState.j9) = r.embed F.TenState.d0 := by
  constructor
  · simpa [F.complement, F.encode, F.decode, F.flipPhase]
      using r.sameObjectBinaryFlip F.TenState.d0
  · simpa [F.complement, F.encode, F.decode, F.flipPhase]
      using r.sameObjectBinaryFlip F.TenState.j9

theorem selected_mode_preserved
    (r : FiveByTwoRecognition) (s : F.TenState) :
    (F.encode (F.complement s)).1 = (F.encode s).1 :=
  F.complement_preserves_mode s

/-- A recognition witness cannot be supplied by the cyclic 4A/H action that
acts trivially on every selected A-copy Tate generator: its selected image
would have to contain a non-fixed point. -/
theorem recognition_requires_more_than_pointwise_identity
    (r : FiveByTwoRecognition)
    (hIdentity : ∀ i : ActualWeightTwoTateIndex, r.action i = i) :
    False := by
  obtain ⟨i, hi⟩ := action_nontrivial_on_selected_image r
  exact hi (hIdentity i)

/-- Defect data is mode-level metadata, independent of the binary action. -/
def recognizedDefectDepth
    (_r : FiveByTwoRecognition) (s : F.TenState) : ℕ :=
  F.defectDepth (F.encode s).1

theorem recognized_defect_is_flip_invariant
    (r : FiveByTwoRecognition) (s : F.TenState) :
    recognizedDefectDepth r (F.complement s) =
      recognizedDefectDepth r s := by
  simp [recognizedDefectDepth, F.complement_preserves_mode]

end Integration.OggSSP2BNormalizerFiveByTwoRecognition
