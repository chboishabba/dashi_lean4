import Integration.OggSSP2BPair24Carrier
import Integration.OggSSP2BNormalizerFiveByTwoRecognition

/-!
# Pair24 same-object weld into the actual 2B Tate recognition contract

The canonical finite carrier
  Pair24 = unordered two-subsets of 24 coordinates
has cardinality 276 and carries the natural S24 action.

This file proves a composition theorem:

1. suppose an independently sourced ten-state Completion10 configuration is
   embedded into Pair24 and one sourced permutation of the 24 coordinates acts
   as the Completion10 complement flip on those ten states;
2. suppose the actual Carnahan--Urano weight-two 2B Tate index carrier is
   equivariantly identified with Pair24 for that same action.

Then the existing OggSSP2BNormalizerFiveByTwoRecognition contract is inhabited.

No such source receipts are fabricated here.  This isolates gate C exactly:
the missing theorem is an equivariant same-object identification between the
actual Tate 276 and the Pair24/ATLAS degree-276 geometry.
-/

namespace Integration.OggSSP2BPair24SameObjectWeld

namespace P := Integration.OggSSP2BPair24Carrier
namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture
namespace R := Integration.OggSSP2BNormalizerFiveByTwoRecognition

/-- Finite local data on the genuine Pair24 carrier. -/
structure Pair24CompletionTenReceipt where
  embedPair : F.TenState → P.Pair24
  injective : Function.Injective embedPair

  coordinatePermutation : Equiv.Perm (Fin 24)
  coordinatePermutationInvolutive :
    coordinatePermutation.trans coordinatePermutation = Equiv.refl (Fin 24)

  completionIntertwines :
    ∀ s,
      P.permutePair coordinatePermutation (embedPair s)
        = embedPair (F.complement s)

/-- The actual-source gate C: same-object identification of the source Tate
276 carrier with Pair24, equivariant for the selected action. -/
structure ActualTatePair24Weld
    (pairReceipt : Pair24CompletionTenReceipt) where
  actualToPair : R.ActualWeightTwoTateIndex ≃ P.Pair24

  actualAction : R.ActualWeightTwoTateIndex → R.ActualWeightTwoTateIndex

  actionEquivariant :
    ∀ i,
      actualToPair (actualAction i)
        =
      P.permutePair pairReceipt.coordinatePermutation (actualToPair i)

open Pair24CompletionTenReceipt ActualTatePair24Weld

def inducedActualEmbedding
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p) :
    F.TenState → R.ActualWeightTwoTateIndex :=
  fun s => w.actualToPair.symm (p.embedPair s)

theorem inducedActualEmbedding_injective
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p) :
    Function.Injective (inducedActualEmbedding p w) := by
  intro a b h
  apply p.injective
  have := congrArg w.actualToPair h
  simpa [inducedActualEmbedding] using this

theorem inducedAction_is_involutive
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p) :
    ∀ i, w.actualAction (w.actualAction i) = i := by
  intro i
  apply w.actualToPair.injective
  rw [w.actionEquivariant, w.actionEquivariant]
  have hcomp :
      P.permutePair p.coordinatePermutation
        (P.permutePair p.coordinatePermutation (w.actualToPair i))
      =
      P.permutePair
        (p.coordinatePermutation.trans p.coordinatePermutation)
        (w.actualToPair i) := by
    symm
    exact P.permutePair_comp _ _ _
  rw [hcomp, p.coordinatePermutationInvolutive]
  exact P.permutePair_id _

theorem inducedAction_intertwines_completion
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p)
    (s : F.TenState) :
    w.actualAction (inducedActualEmbedding p w s)
      =
    inducedActualEmbedding p w (F.complement s) := by
  apply w.actualToPair.injective
  rw [w.actionEquivariant]
  simp only [inducedActualEmbedding, Equiv.apply_symm_apply]
  rw [p.completionIntertwines]
  simp

/-- Gate-C composition theorem: the existing five-by-two recognition object
is produced automatically from a Pair24 finite receipt plus the genuine
same-object Tate/Pair24 weld. -/
def recognitionOfPair24Weld
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p) :
    R.FiveByTwoRecognition where
  embed := inducedActualEmbedding p w
  injective := inducedActualEmbedding_injective p w
  action := w.actualAction
  actionInvolutive := inducedAction_is_involutive p w
  sameObjectBinaryFlip := inducedAction_intertwines_completion p w

theorem pair24_weld_pays_existing_recognition
    (p : Pair24CompletionTenReceipt)
    (w : ActualTatePair24Weld p) :
    ∃ r : R.FiveByTwoRecognition,
      ∀ s,
        r.action (r.embed s) = r.embed (F.complement s) := by
  refine ⟨recognitionOfPair24Weld p w, ?_⟩
  intro s
  exact (recognitionOfPair24Weld p w).sameObjectBinaryFlip s

/-- Boundary proposition: cardinality 276 alone still cannot construct the
actual equivariant weld. -/
inductive EqualCardinalityConstructsActualTatePair24Weld : Prop

theorem cardinality_does_not_pay_gate_C :
    ¬ EqualCardinalityConstructsActualTatePair24Weld := by
  intro h
  cases h

end Integration.OggSSP2BPair24SameObjectWeld
