/-!
DASHI generic B^k hyperfabric carrier and query-relative projection spine.
Not owned by McNamara's 9-grid or by SensibLaw WrongType.
No philosophical theory, legal liability, cultural permission, or historical
fact follows merely from an address. Gluing needs separately sourced evidence.

Finite cardinality for B of size b is b^k; B containing n tagged
three-mode families has (3*n)^k elements if tags are disjoint.
The self-indexing carrier (previous level → B) is a distinct tower.
-/
import Mathlib

namespace AgdaMirror.Core.IndexedRelationalHyperfabric

abbrev Address (B : Type) (k : Nat) := Fin k → B

structure IndexedFabric (B : Type) (k : Nat) where
  Fibre : Address B k → Type
  provenance : String

abbrev Situated {B : Type} {k : Nat} (f : IndexedFabric B k) :=
  (a : Address B k) × f.Fibre a

def address {B : Type} {k : Nat} {f : IndexedFabric B k}
    (s : Situated f) : Address B k := s.1

/-- Consumer-specific factorisation, not a universal observer-adequacy claim. -/
def FactorsThrough {State View Answer : Type}
    (observe : State → View) (answer : State → Answer) : Prop :=
  ∃ f : View → Answer, ∀ s, answer s = f (observe s)

/-- Exact collision sufficient to refute all decoder functions. -/
structure Collision {State View Answer : Type}
    (observe : State → View) (answer : State → Answer) : Type where
  left : State
  right : State
  sameView : observe left = observe right
  differentAnswer : answer left ≠ answer right

theorem collision_blocks_factorisation {State View Answer : Type}
    {observe : State → View} {answer : State → Answer}
    (h : Collision observe answer) :
    ¬ FactorsThrough observe answer := by
  intro f
  obtain ⟨decode, factor⟩ := f
  apply h.differentAnswer
  calc
    answer h.left = decode (observe h.left) := factor _
    _ = decode (observe h.right) := by rw [h.sameView]
    _ = answer h.right := (factor _).symm

theorem rechart_cannot_recover {State View Chart Answer : Type}
    {observe : State → View} {answer : State → Answer}
    (chart : View → Chart)
    (h : Collision observe answer) :
    ¬ FactorsThrough (fun s => chart (observe s)) answer := by
  intro derived
  apply collision_blocks_factorisation h
  obtain ⟨decode, factor⟩ := derived
  exact ⟨fun v => decode (chart v), factor⟩

structure AdmissibleObservation {State View Answer : Type}
    (observe : State → View) (answer : State → Answer) where
  sufficient : FactorsThrough observe answer
  AuthorityEvidence : Prop
  authority : AuthorityEvidence
  SourceEvidence : Prop
  sourced : SourceEvidence

/-- A gluing action is not granted by carrier overlap: supply the
    compatibility witness for this exact interface. -/
structure GuardedGluing {B : Type} {k l : Nat}
    (left : IndexedFabric B k) (right : IndexedFabric B l) where
  Interface : Type
  interface : Interface
  Compatible : Interface → Prop
  compatibility : Compatible interface
  Output : Type
  glue : Situated left → Situated right → Output
  provenance : String

def sites (b k : Nat) : Nat := b ^ k

theorem three_two : sites 3 2 = 9 := by decide
theorem three_three : sites 3 3 = 27 := by decide
theorem three_four : sites 3 4 = 81 := by decide
theorem six_two : sites (3 * 2) 2 = 36 := by decide

end AgdaMirror.Core.IndexedRelationalHyperfabric
