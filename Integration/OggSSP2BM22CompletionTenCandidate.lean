import Integration.OggSSP2BFiveByTwoDefectArchitecture
import Integration.OggSSP2BCo1TenDimensionalNoGo

/-!
# M22 local 10-dimensional candidate for Completion10

Source facts:
* Co1 has a maximal subgroup 2^11 : M24.
* M22 occurs naturally inside M24.
* M22 has exactly two absolutely irreducible 10-dimensional modules over F2,
  the Golay-code and Golay-cocode modules.

These are the first sourced characteristic-two modules found at exactly the
Completion10 dimension.  Therefore M22 is a serious local candidate for the
nontrivial 5x2 action after restricting/localising the actual 276-dimensional
2B Tate module.

This file does NOT claim either M22 module occurs in that Tate module.
It records the exact recognition test needed:
  a sourced M22-stable 10-dimensional subquotient of the actual Tate space,
  plus an intertwiner carrying one sourced involution to the repo-native
  complement flip.

The involution fingerprint to test computationally is five J2 blocks:
equivalently, in the permutation-pair basis the involution fixes a
5-dimensional subspace and (J-I) has rank 5.
-/

namespace Integration.OggSSP2BM22CompletionTenCandidate

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture

inductive M22TenModuleKind
  | golayCode
  | golayCocode
  deriving DecidableEq, Repr, Fintype

def sourcedDimension : M22TenModuleKind → ℕ
  | .golayCode => 10
  | .golayCocode => 10

theorem both_M22_candidates_are_dimension_ten
    (k : M22TenModuleKind) :
    sourcedDimension k = 10 := by
  cases k <;> rfl

theorem exactly_two_named_M22_ten_candidates :
    Fintype.card M22TenModuleKind = 2 := by
  decide

/-- Repo-native complement operator on the ten basis states. -/
def completionFlip : F.TenState → F.TenState :=
  F.complement

theorem completionFlip_involutive :
    Function.Involutive completionFlip := by
  intro x
  exact F.complement_involutive x

theorem completionFlip_has_no_fixed_basis_state
    (x : F.TenState) :
    completionFlip x ≠ x := by
  cases x <;> decide

/-- The five unordered complement pairs. -/
def completionPairMode (x : F.TenState) : F.Mode5 :=
  (F.encode x).1

theorem completionPairMode_flip_invariant
    (x : F.TenState) :
    completionPairMode (completionFlip x) = completionPairMode x := by
  exact F.complement_preserves_mode x

/-- Source-level receipt we now need from an actual M22 restriction of the
2B Tate module.  This is not a new generic recognition framework; it packages
only the concrete missing same-object data for the existing Completion10
carrier. -/
structure ActualTateM22TenReceipt where
  kind : M22TenModuleKind

  /-- ten selected actual Tate coordinates inside the source 276-space -/
  embed : F.TenState → Fin 276
  injective : Function.Injective embed

  /-- action of one sourced involution from the chosen M22 local subgroup -/
  involution : Fin 276 → Fin 276
  involution_sq : ∀ i, involution (involution i) = i

  /-- exact same-object intertwiner target -/
  complement_intertwines :
    ∀ s, involution (embed s) = embed (completionFlip s)

open ActualTateM22TenReceipt

theorem receipt_gives_nontrivial_actual_Tate_action
    (r : ActualTateM22TenReceipt) :
    ∃ i : Fin 276, r.involution i ≠ i := by
  refine ⟨r.embed F.TenState.d0, ?_⟩
  rw [r.complement_intertwines]
  intro h
  have := r.injective h
  decide at this

theorem receipt_selected_image_is_M22_involution_stable
    (r : ActualTateM22TenReceipt)
    (s : F.TenState) :
    ∃ t : F.TenState, r.involution (r.embed s) = r.embed t := by
  exact ⟨completionFlip s, r.complement_intertwines s⟩

theorem receipt_recovers_five_flip_pairs
    (r : ActualTateM22TenReceipt)
    (s : F.TenState) :
    completionPairMode (completionFlip s) = completionPairMode s :=
  completionPairMode_flip_invariant s

/-- Full Co1 was screened out; a proper local subgroup such as M22 is therefore
not merely optional if the ten-dimensional action is to be nontrivial. -/
theorem local_subgroup_is_dimensionally_compatible :
    ∀ k : M22TenModuleKind, sourcedDimension k < 24 := by
  intro k
  cases k <;> decide

end Integration.OggSSP2BM22CompletionTenCandidate
