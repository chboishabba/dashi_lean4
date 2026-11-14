/-!
# Finite C3 orbit sum of the asymmetric three-vertex weighted graph

Downstream golden Agda:
DASHI.Reasoning.TrialecticC3WeightedOrbitSymmetrizationExact.

The input graph has no weighted C3 action. Summing its three rotated
weight functions produces a *new* C3-invariant graph without division
or negative weights. Its compatible two-ended rows then transport by
rotation pointwise. This construction is not a same-object Monster
representation, a source-authorised triadic face, or smooth gluing.
-/
import Mathlib
import AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369
import AgdaMirror.Reasoning.TrialecticDirectedSourceTargetHyperfabric

namespace AgdaMirror.Reasoning.TrialecticC3WeightedOrbitSymmetrization

open AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369
open AgdaMirror.Reasoning.TrialecticDirectedSourceTargetHyperfabric

def orbitSum (w : WeightedGraph3) : WeightedGraph3 :=
  fun s t => (w s t + w (rotate s) (rotate t)) +
    w (rotate (rotate s)) (rotate (rotate t))

theorem orbit_sum_c3_invariant (w : WeightedGraph3) (s t : Vertex3) :
    orbitSum w (rotate s) (rotate t) = orbitSum w s t := by
  cases s <;> cases t <;>
    simp only [orbitSum, rotate] <;> ac_rfl

def symmetrizedFixture : WeightedGraph3 :=
  orbitSum (matrixToGraph fixture)

theorem exact_orbit_sum_matrix :
    graphToMatrix symmetrizedFixture =
      (⟨5,50,22, 22,5,50, 50,22,5⟩ : Matrix3 Nat) := by
  rfl

theorem fixture_still_not_invariant :
    ¬ ∀ s t : Vertex3,
      matrixToGraph fixture (rotate s) (rotate t) =
        matrixToGraph fixture s t := fixture_not_c3_invariant

theorem symmetrized_is_not_identical_to_fixture :
    symmetrizedFixture .a .b ≠ matrixToGraph fixture .a .b := by
  decide

def compatibleRows (w : WeightedGraph3) (v : Vertex3) : VertexRows :=
  ⟨fun t => w v t, fun s => w s v⟩

theorem source_target_compatible (w : WeightedGraph3)
    (s t : Vertex3) :
    (compatibleRows w s).outgoing t =
      (compatibleRows w t).incoming s := rfl

theorem outgoing_c3_transport (v t : Vertex3) :
    (compatibleRows symmetrizedFixture (rotate v)).outgoing (rotate t) =
    (compatibleRows symmetrizedFixture v).outgoing t :=
  orbit_sum_c3_invariant (matrixToGraph fixture) v t

theorem incoming_c3_transport (v s : Vertex3) :
    (compatibleRows symmetrizedFixture (rotate v)).incoming (rotate s) =
    (compatibleRows symmetrizedFixture v).incoming s :=
  orbit_sum_c3_invariant (matrixToGraph fixture) s v

end AgdaMirror.Reasoning.TrialecticC3WeightedOrbitSymmetrization
