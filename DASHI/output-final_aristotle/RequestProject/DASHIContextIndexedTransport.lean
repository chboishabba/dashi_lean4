import RequestProject.Properties

/-!
DASHI-local context-indexed transport over JMD-attributed Wikidata properties.
This module does not modify RequestProject's original JMD semantics.
A transport proof is scoped to one declared observation/query; it is neither
a source equivalence nor an edit-authority or live-Wikidata certificate.
-/
namespace DASHI.ContextIndexedOntology

/-- One consumer's observation of a native representation. -/
structure ConsumerView (α out : Type) where
  observe : α → out

/-- Proof-relevant, query-local structure-preserving translation. -/
structure Licensed (α β out : Type)
    (a : ConsumerView α out) (b : ConsumerView β out) where
  map : α → β
  preserves : ∀ x, b.observe (map x) = a.observe x

def Licensed.id {α out : Type} (a : ConsumerView α out) :
    Licensed α α out a a where
  map := fun x => x
  preserves := by intro _; rfl

/-- Licences compose only when their shared intermediate observer is the same. -/
def Licensed.comp {α β γ out : Type}
    {a : ConsumerView α out} {b : ConsumerView β out}
    {c : ConsumerView γ out}
    (f : Licensed α β out a b)
    (g : Licensed β γ out b c) :
    Licensed α γ out a c where
  map := g.map ∘ f.map
  preserves := by
    intro x
    exact (g.preserves (f.map x)).trans (f.preserves x)

theorem Licensed.consumer_eq {α β out : Type}
    {a : ConsumerView α out} {b : ConsumerView β out}
    (f : Licensed α β out a b) {x y : α}
    (h : a.observe x = a.observe y) :
    b.observe (f.map x) = b.observe (f.map y) := by
  calc
    b.observe (f.map x) = a.observe x := f.preserves x
    _ = a.observe y := h
    _ = b.observe (f.map y) := (f.preserves y).symm

/-- Support and counter-support are separate, non-exclusive evidence coordinates. -/
structure EvidenceLedger where
  support : List String
  counter : List String
  missing : List String
  provenance : List String

def EvidenceLedger.addSupport (e : EvidenceLedger) (ref : String) :
    EvidenceLedger := { e with support := ref :: e.support }

def EvidenceLedger.addCounter (e : EvidenceLedger) (ref : String) :
    EvidenceLedger := { e with counter := ref :: e.counter }

@[simp] theorem EvidenceLedger.addSupport_counter (e : EvidenceLedger) (ref : String) :
    (e.addSupport ref).counter = e.counter := rfl

@[simp] theorem EvidenceLedger.addCounter_support (e : EvidenceLedger) (ref : String) :
    (e.addCounter ref).support = e.support := rfl

/-- An obligation is never inferred from equality of native IDs alone. -/
inductive ObligationState
  | discharged | refuted | missing | outsideScope | contested
  deriving DecidableEq, Repr

structure ContractJudgment where
  sourceRevision : String
  queryRef : String
  contractRef : String
  witnessRefs : List String
  missingPremises : List String
  state : ObligationState
  deriving Repr

/-- One consumer's truth-preserving, modeled repair; this does not authorise edits. -/
structure BoundedRepair (α out : Type) (v : ConsumerView α out) where
  patch : α → α
  preserves : ∀ x, v.observe (patch x) = v.observe x
  rerunObligations : List String

theorem BoundedRepair.consumer_eq {α out : Type}
    {v : ConsumerView α out} (r : BoundedRepair α out v)
    {x y : α} (h : v.observe x = v.observe y) :
    v.observe (r.patch x) = v.observe (r.patch y) := by
  calc
    v.observe (r.patch x) = v.observe x := r.preserves x
    _ = v.observe y := h
    _ = v.observe (r.patch y) := (r.preserves y).symm

end DASHI.ContextIndexedOntology
