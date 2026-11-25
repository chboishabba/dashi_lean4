import Integration.E8LiteralMixed27Fibres
import Mathlib

/-!
# E6 transitivity of the six literal E8 mixed 27-point fibres

No action is transported from a ternary carrier.  Adjacency is defined directly
from the independent literal 8D E8 reflection formula: two roots are related
when one is obtained from the other by one of the six embedded E6 simple
reflections.

Finite relation saturation proves every one of the six A2-weight fibres is a
single connected E6 reflection orbit of size 27.  This is the exact finite
signature expected of the two minuscule-27 families in the
`E8 -> E6 x A2` root branching.
-/

namespace Integration.E8LiteralMixed27Transitivity

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E6Mod3WeylAction
open Integration.E6LiteralE8Action
open Integration.E8LiteralMixed27Fibres

/-- Independent literal-reflection relation on the 240 E8 roots. -/
def literalRelated (r t : E8ScaledRoot) : Bool :=
  decide (∃ s : E6SimpleReflection, ∀ k,
    e8Coord t k = literalReflectCoord s r k)

/-- Restrict the relation to one A2-weight fibre. -/
def fiberRelated {w : Int × Int}
    (r t : LiteralWeightFiber w) : Bool :=
  literalRelated r.1 t.1

/-- One relation-saturation step on a finite carrier. -/
def expandRelation {α : Type*} [Fintype α] [DecidableEq α]
    (rel : α → α → Bool) (S : Finset α) : Finset α :=
  S ∪ Finset.univ.filter (fun y => ∃ x ∈ S, rel x y = true)

def relationOrbitN {α : Type*} [Fintype α] [DecidableEq α]
    (rel : α → α → Bool) (seed : α) : Nat → Finset α
  | 0 => {seed}
  | n + 1 => expandRelation rel (relationOrbitN rel seed n)

/-- Local exhaustive preflight found diameter 16 for each weight fibre; using
that uniform bound makes the kernel-facing finite statements simple. -/
def plus0Orbit (seed : Plus0) : Finset Plus0 := relationOrbitN fiberRelated seed 16
def plus1Orbit (seed : Plus1) : Finset Plus1 := relationOrbitN fiberRelated seed 16
def plus2Orbit (seed : Plus2) : Finset Plus2 := relationOrbitN fiberRelated seed 16
def minus0Orbit (seed : Minus0) : Finset Minus0 := relationOrbitN fiberRelated seed 16
def minus1Orbit (seed : Minus1) : Finset Minus1 := relationOrbitN fiberRelated seed 16
def minus2Orbit (seed : Minus2) : Finset Minus2 := relationOrbitN fiberRelated seed 16

theorem plus0_orbit_full : ∀ seed : Plus0, plus0Orbit seed = Finset.univ := by
  native_decide

theorem plus1_orbit_full : ∀ seed : Plus1, plus1Orbit seed = Finset.univ := by
  native_decide

theorem plus2_orbit_full : ∀ seed : Plus2, plus2Orbit seed = Finset.univ := by
  native_decide

theorem minus0_orbit_full : ∀ seed : Minus0, minus0Orbit seed = Finset.univ := by
  native_decide

theorem minus1_orbit_full : ∀ seed : Minus1, minus1Orbit seed = Finset.univ := by
  native_decide

theorem minus2_orbit_full : ∀ seed : Minus2, minus2Orbit seed = Finset.univ := by
  native_decide

/-- Relation-level transitivity packaged without selecting a noncomputable root
action function. -/
def ReflectionRelationTransitive {w : Int × Int} : Prop :=
  ∀ seed target : LiteralWeightFiber w,
    target ∈ relationOrbitN fiberRelated seed 16

theorem plus0_relation_transitive : ReflectionRelationTransitive (0,-4) := by
  intro seed target
  rw [plus0_orbit_full seed]
  simp [plus0Orbit]

theorem plus1_relation_transitive : ReflectionRelationTransitive (4,0) := by
  intro seed target
  rw [plus1_orbit_full seed]
  simp [plus1Orbit]

theorem plus2_relation_transitive : ReflectionRelationTransitive (-4,4) := by
  intro seed target
  rw [plus2_orbit_full seed]
  simp [plus2Orbit]

theorem minus0_relation_transitive : ReflectionRelationTransitive (0,4) := by
  intro seed target
  rw [minus0_orbit_full seed]
  simp [minus0Orbit]

theorem minus1_relation_transitive : ReflectionRelationTransitive (-4,0) := by
  intro seed target
  rw [minus1_orbit_full seed]
  simp [minus1Orbit]

theorem minus2_relation_transitive : ReflectionRelationTransitive (4,-4) := by
  intro seed target
  rw [minus2_orbit_full seed]
  simp [minus2Orbit]

structure Boundary where
  literalReflectionRelationTyped : Bool
  plusThreeFibresTransitivePaid : Bool
  minusThreeFibresTransitivePaid : Bool
  sixFibresE6TransitivePaid : Bool
  uniformFiniteDiameter16Paid : Bool
  actionChosenByTransport : Bool
  minusculeRepresentationIdentificationPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalReflectionRelationTyped := true
  plusThreeFibresTransitivePaid := true
  minusThreeFibresTransitivePaid := true
  sixFibresE6TransitivePaid := true
  uniformFiniteDiameter16Paid := true
  actionChosenByTransport := false
  minusculeRepresentationIdentificationPaidHere := false

end Integration.E8LiteralMixed27Transitivity
