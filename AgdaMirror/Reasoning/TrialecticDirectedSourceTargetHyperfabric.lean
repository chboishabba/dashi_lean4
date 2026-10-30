/-!
# Two-ended directed source/target hyperfabric mirror.

Golden owner: DASHI.Reasoning.TrialecticDirectedSourceTargetHyperfabricExact

One oriented edge s→t is simultaneously restricted from source outgoing(s)[t]
and target incoming(t)[s]. The two restrictions match on that edge,
not on its reversed edge. A self-loop has two *role tags* at one vertex.

Source roots: standard matrix/directed graph. Fiorini et al. (ICLR 2026)
and Mule et al. (ICLR 2026) are concept comparisons, not imported neural
networks, Laplacians, performance benchmarks, or mathematical proofs.
-/
import Mathlib
import AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369

namespace AgdaMirror.Reasoning.TrialecticDirectedSourceTargetHyperfabric

open AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369

structure OrientedEdge where
  source : Vertex3
  target : Vertex3
  deriving DecidableEq, Repr

inductive IncidenceRole
  | source
  | target
  deriving DecidableEq, Repr

def incident (v : Vertex3) (e : OrientedEdge)
    (role : IncidenceRole) : Prop :=
  match role with
  | .source => v = e.source
  | .target => v = e.target

structure VertexRows where
  outgoing : Vertex3 → Nat
  incoming : Vertex3 → Nat

def rowsAt (v : Vertex3) : VertexRows :=
  ⟨fun t => matrixToGraph fixture v t,
   fun s => matrixToGraph fixture s v⟩

def edgeValue (e : OrientedEdge) : Nat :=
  matrixToGraph fixture e.source e.target

def restrictSource (e : OrientedEdge) : Nat :=
  (rowsAt e.source).outgoing e.target

def restrictTarget (e : OrientedEdge) : Nat :=
  (rowsAt e.target).incoming e.source

theorem source_restriction_compatible (e : OrientedEdge) :
    restrictSource e = edgeValue e := rfl

theorem target_restriction_compatible (e : OrientedEdge) :
    restrictTarget e = edgeValue e := rfl

theorem both_ends_agree_on_oriented_edge (e : OrientedEdge) :
    restrictSource e = restrictTarget e := by
  rw [source_restriction_compatible, target_restriction_compatible]

def forward : OrientedEdge := ⟨.a,.b⟩
def reverse : OrientedEdge := ⟨.b,.a⟩
def loop : OrientedEdge := ⟨.a,.a⟩

theorem forward_ends_equal_ten :
    restrictSource forward = 10 ∧ restrictTarget forward = 10 := by
  decide

theorem reverse_ends_equal_two :
    restrictSource reverse = 2 ∧ restrictTarget reverse = 2 := by
  decide

theorem forward_reverse_differ :
    edgeValue forward ≠ edgeValue reverse := by
  decide

theorem loop_source_target_roles_coincide_at_vertex :
    incident .a loop .source ∧ incident .a loop .target := by
  decide

theorem loop_two_restrictions_equal_five :
    restrictSource loop = 5 ∧ restrictTarget loop = 5 := by
  decide

end AgdaMirror.Reasoning.TrialecticDirectedSourceTargetHyperfabric
