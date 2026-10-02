import Integration.OggSSP2BPair24Carrier
import Integration.OggSSP2BFiveByTwoDefectArchitecture

/-!
# Product-action no-go: the S3 factor is invisible on the bare M24 duad carrier

The sourced 2B-pure local quotient has shape M24 x S3.  The natural
degree-276 duad action is the M24 action on unordered pairs of 24 points.

If the product action on Pair24 factors through projection to M24, then every
element of the S3 factor acts identically on Pair24 and therefore identically
on the F2 permutation module Pair24 -> F2.

So the sourced S3 factor cannot by itself realize the nontrivial Completion10
phase action on the *bare duad module*.  A nontrivial C3/S3 phase must occur in
additional source structure: a Tate/local multiplicity space, an extension, or
a subquotient on which S3 acts genuinely.

This is a structural no-go, not a claim that S3 is irrelevant to the full
Monster-local representation.
-/

namespace Integration.OggSSP2BM24xS3DuadPhaseNoGo

namespace P := Integration.OggSSP2BPair24Carrier
namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture

variable {S3 : Type*}

/-- Any product action that uses only the M24/coordinate component is
independent of the S3 coordinate. -/
def duadActionThroughM24
    (m24perm : Equiv.Perm (Fin 24))
    (_s3 : S3) :
    P.Pair24 ≃ P.Pair24 :=
  P.permutePair m24perm

theorem s3_coordinate_invisible_on_duads
    (m24perm : Equiv.Perm (Fin 24))
    (a b : S3) :
    duadActionThroughM24 m24perm a =
      duadActionThroughM24 m24perm b := by
  rfl

/-- In particular, an S3 element paired with identity M24 acts identically. -/
theorem pure_s3_acts_identity_on_duads
    (s : S3) :
    duadActionThroughM24 (Equiv.refl (Fin 24)) s =
      Equiv.refl P.Pair24 := by
  ext p
  exact P.permutePair_id p

/-- Same result on the F2 permutation module. -/
def duadModuleActionThroughM24
    (m24perm : Equiv.Perm (Fin 24))
    (_s3 : S3) :
    P.Pair24PermutationModule →ₗ[ZMod 2] P.Pair24PermutationModule :=
  P.pullbackAction m24perm

theorem pure_s3_acts_identity_on_duad_module
    (s : S3) :
    duadModuleActionThroughM24 (Equiv.refl (Fin 24)) s =
      LinearMap.id := by
  exact P.pullbackAction_id

/-- Completion10's complement is genuinely nontrivial on its ten-state
carrier, so it cannot be identified with a pure-S3 action that is pointwise
identity on Pair24. -/
theorem completion_flip_nontrivial :
    F.complement F.TenState.d0 ≠ F.TenState.d0 := by
  decide

structure DuadCompletionTenEmbedding where
  embed : F.TenState → P.Pair24
  injective : Function.Injective embed

/-- No injective Completion10 chart into Pair24 can intertwine its nontrivial
complement flip with a pure-S3 action that factors trivially through M24. -/
theorem no_completion_flip_from_pure_s3_duad_action
    (e : DuadCompletionTenEmbedding)
    (s : S3)
    (hIntertwine :
      ∀ t,
        (duadActionThroughM24 (Equiv.refl (Fin 24)) s) (e.embed t)
          = e.embed (F.complement t)) :
    False := by
  have h0 := hIntertwine F.TenState.d0
  rw [pure_s3_acts_identity_on_duads] at h0
  have := e.injective h0
  exact completion_flip_nontrivial this.symm

end Integration.OggSSP2BM24xS3DuadPhaseNoGo
