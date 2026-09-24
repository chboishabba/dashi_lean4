import RequestProject.Wikidata.Provenance

/-!
# Slices

A *slice* of a knowledge base is the sub-base cut out by a decidable predicate on
statements.  `RequestProject.Wikidata.Provenance` already exhibits two families of
slices (provenance and time); this file isolates the general notion so that the
facts they share are proved once:

* slices compose (`restrict_restrict`) and the trivial slice is the identity
  (`restrict_true`);
* slices are ordered by refinement (`Refines`), and a finer slice is contained in
  a coarser one (`restrict_subset_of_refines`);
* facts derived in a slice hold in the whole base (`subclassOf_of_restrict`,
  `instanceOf_of_restrict`), and validity is inherited (`valid_restrict`);
* the provenance and temporal slices of `Provenance.lean` are instances
  (`Provenanced.slice_eq_restrict`, `Timed.snapshot_eq_restrict`).

Slicing is *downward*: a slice never derives a fact the full base does not have.
That direction is what makes "supported on a more trustworthy slice" a stronger
statement than "supported somewhere", and it is why the converse fails.
-/

namespace Wikidata

/-- A slice criterion: a decidable predicate on statements. -/
abbrev StatementFilter := Statement → Bool

/-- The knowledge base cut down to the statements satisfying `f`. -/
def restrict (kb : KB) (f : StatementFilter) : KB :=
  { kb with statements := kb.statements.filter f }

@[simp] theorem restrict_entities (kb : KB) (f : StatementFilter) :
    (restrict kb f).entities = kb.entities := rfl

@[simp] theorem restrict_statements (kb : KB) (f : StatementFilter) :
    (restrict kb f).statements = kb.statements.filter f := rfl

theorem restrict_subset (kb : KB) (f : StatementFilter) :
    (restrict kb f).statements ⊆ kb.statements :=
  fun _ hst => List.mem_of_mem_filter hst

theorem mem_restrict_iff (kb : KB) (f : StatementFilter) (st : Statement) :
    st ∈ (restrict kb f).statements ↔ st ∈ kb.statements ∧ f st = true := by
  simp [restrict, List.mem_filter]

/-- Slicing twice is slicing once, by the conjunction of the criteria. -/
theorem restrict_restrict (kb : KB) (f g : StatementFilter) :
    restrict (restrict kb f) g = restrict kb (fun st => f st && g st) := by
  cases kb with
  | mk ents sts => simp [restrict, List.filter_filter, Bool.and_comm]

/-- The trivial slice keeps everything. -/
@[simp] theorem restrict_true (kb : KB) : restrict kb (fun _ => true) = kb := by
  cases kb with
  | mk ents sts => simp [restrict]

/-! ## The refinement order -/

/-- `f` refines `g` when every statement kept by `f` is kept by `g`. -/
def Refines (f g : StatementFilter) : Prop := ∀ st, f st = true → g st = true

theorem Refines.refl (f : StatementFilter) : Refines f f := fun _ h => h

theorem Refines.trans {f g h : StatementFilter} (hfg : Refines f g) (hgh : Refines g h) :
    Refines f h := fun st hst => hgh st (hfg st hst)

theorem refines_true (f : StatementFilter) : Refines f (fun _ => true) := fun _ _ => rfl

theorem restrict_subset_of_refines {f g : StatementFilter} (h : Refines f g) (kb : KB) :
    (restrict kb f).statements ⊆ (restrict kb g).statements := by
  intro st hst
  rw [mem_restrict_iff] at hst ⊢
  exact ⟨hst.1, h st hst.2⟩

/-- The conjunction of two criteria is their greatest lower bound. -/
theorem refines_and_left (f g : StatementFilter) : Refines (fun st => f st && g st) f := by
  intro st h
  exact (Bool.and_eq_true .. |>.mp h).1

theorem refines_and_right (f g : StatementFilter) : Refines (fun st => f st && g st) g := by
  intro st h
  exact (Bool.and_eq_true .. |>.mp h).2

theorem refines_and_of_refines {h f g : StatementFilter} (hf : Refines h f) (hg : Refines h g) :
    Refines h (fun st => f st && g st) := by
  intro st hst
  simp [hf st hst, hg st hst]

/-! ## Derivation and validity under slicing -/

theorem allNormal_restrict {kb : KB} (h : AllNormal kb) (f : StatementFilter) :
    AllNormal (restrict kb f) := allNormal_of_subset (restrict_subset kb f) h

/-- Subclass facts derived in a slice hold in the whole base. -/
theorem subclassOf_of_restrict (kb : KB) (f : StatementFilter) (hnormal : AllNormal kb)
    {a b : Qid} (h : SubclassOf (restrict kb f) a b) : SubclassOf kb a b :=
  subclassOf_mono (restrict_subset kb f) hnormal h

/-- Instance facts derived in a slice hold in the whole base. -/
theorem instanceOf_of_restrict (kb : KB) (f : StatementFilter) (hnormal : AllNormal kb)
    {x c : Qid} (h : InstanceOf (restrict kb f) x c) : InstanceOf kb x c :=
  instanceOf_mono (restrict_subset kb f) hnormal h

/-- A fact derived in a finer slice holds in every coarser slice. -/
theorem subclassOf_of_refines {f g : StatementFilter} (hfg : Refines f g) (kb : KB)
    (hnormal : AllNormal kb) {a b : Qid} (h : SubclassOf (restrict kb f) a b) :
    SubclassOf (restrict kb g) a b :=
  subclassOf_mono (restrict_subset_of_refines hfg kb) (allNormal_restrict hnormal g) h

theorem instanceOf_of_refines {f g : StatementFilter} (hfg : Refines f g) (kb : KB)
    (hnormal : AllNormal kb) {x c : Qid} (h : InstanceOf (restrict kb f) x c) :
    InstanceOf (restrict kb g) x c :=
  instanceOf_mono (restrict_subset_of_refines hfg kb) (allNormal_restrict hnormal g) h

/-- Slicing preserves validity. -/
theorem valid_restrict (kb : KB) (f : StatementFilter) (hnormal : AllNormal kb)
    (hvalid : Valid kb) : Valid (restrict kb f) :=
  valid_of_subset (kb₁ := restrict kb f) (kb₂ := kb) rfl (restrict_subset kb f) hnormal hvalid

/-! ## The provenance and temporal slices are instances -/

theorem Provenanced.slice_eq_restrict (p : Provenanced) (s : Slice) :
    p.slice s = restrict p.base (p.keep s) := rfl

theorem Timed.snapshot_eq_restrict (t : Timed) (n : Nat) :
    t.snapshot n = restrict t.base (fun st => t.start st ≤ n ∧ n < t.stop st) := rfl

/-- The reliable provenance slice refines the sourced one. -/
theorem Provenanced.refines_reliable_sourced (p : Provenanced) :
    Refines (p.keep Slice.reliable) (p.keep Slice.sourced) := by
  intro st hst
  simp only [keep] at hst ⊢
  obtain ⟨r, hr, _⟩ := List.any_eq_true.1 hst
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
  exact List.ne_nil_of_mem hr

/-- Every provenance slice refines the asserted (trivial) one. -/
theorem Provenanced.refines_asserted (p : Provenanced) (s : Slice) :
    Refines (p.keep s) (p.keep Slice.asserted) := fun _ _ => rfl

end Wikidata
