import RequestProject.Engine
import RequestProject.Matching

/-!
# `is the study of` (P2578) and `topic's main category` (P910)

Two predicates the enrichment tool asked for.  Running `wikidata frontier` over
the scanned theory articles ranks the Wikidata properties the sources use that
this development has no Lean predicate for
(`RequestProject.EnrichmentRun.predicateDemand_top`); after the external
identifiers — which the existing `Wikidata.IdKB` layer already covers as a class
— the most used are

* **P2578, `is the study of`** (37 items), with its declared inverse **P2579,
  `studied by`**: what an academic field studies;
* **P910, `topic's main category`** (37 items), with its declared inverse
  **P301, `category's main topic`**: the Wikimedia category page collecting the
  material about a topic.

This file adds both.

## The study relation

A `StudyKB` is an ontology together with `is the study of` statements, in either
direction.  Being an inverse pair is not an extra axiom here: a P2579 statement
`o studied by f` *is* the P2578 statement `f is the study of o` read backwards
(`StudyKB.asserted_comm`).

Two derivation rules are then justified by the class hierarchy, and both are
familiar from how Wikidata is actually written:

* **down the field**: a subfield studies whatever its field studies — algebraic
  topology is a subclass of topology, so it studies topological spaces;
* **down the object**: a field studies every kind of thing it studies — topology
  studies topological spaces, and an Alexandrov topology is one, so topology
  studies Alexandrov topologies.

`StudyKB.Studies` is the resulting relation and `StudyKB.studiesB` decides it
(`StudyKB.studiesB_iff`).  It is monotone in both arguments, contains the
asserted statements, is idempotent under the two rules, and is transitive along
the class hierarchy of fields.

## The category link

`P910` and `P301` are functional in both directions: a topic has one main
category and a category has one main topic.  That is exactly the partial
bijection situation of `RequestProject.Matching`, so the layer is a `KeyTable`
and the theorems come for free (`TopicKB.mainCategory_eq_some_iff_mainTopic_eq_some`).
-/

namespace Wikidata

/-! ## `is the study of` -/

/-- An ontology together with `is the study of` (P2578) and `studied by` (P2579)
statements. -/
structure StudyKB where
  /-- The class hierarchy the statements live in. -/
  base : KB
  /-- Asserted `is the study of` (P2578) statements, field first. -/
  studies : List (Qid × Qid) := []
  /-- Asserted `studied by` (P2579) statements, object first. -/
  studiedBy : List (Qid × Qid) := []
deriving DecidableEq, Repr, Inhabited

namespace StudyKB

variable (S : StudyKB)

/-- The asserted study statements, in one direction: `f` is declared to be the
study of `o`, by a P2578 statement or by the P2579 statement that says the same
thing backwards. -/
def Asserted (f o : Qid) : Prop := (f, o) ∈ S.studies ∨ (o, f) ∈ S.studiedBy

/-- The executable version. -/
def assertedB (f o : Qid) : Bool := S.studies.contains (f, o) || S.studiedBy.contains (o, f)

theorem assertedB_iff {f o : Qid} : S.assertedB f o = true ↔ S.Asserted f o := by
  simp [assertedB, Asserted]

/-- The two properties are an inverse pair: P2579 asserts the converse of P2578. -/
theorem asserted_comm {f o : Qid} :
    S.Asserted f o ↔ ((f, o) ∈ S.studies ∨ (o, f) ∈ S.studiedBy) := Iff.rfl

/-- **The derived study relation**: `f` studies `o` when some field `g` is
declared to study some `x`, `f` is a subclass of `g` (a subfield) and `o` is a
subclass of `x` (a kind of the thing studied). -/
def Studies (f o : Qid) : Prop :=
  ∃ g x, S.Asserted g x ∧ S.base.isSubclassOf f g = true ∧ S.base.isSubclassOf o x = true

/-- The executable version of the derived relation. -/
def studiesB (f o : Qid) : Bool :=
  (S.studies.any fun p => S.base.isSubclassOf f p.1 && S.base.isSubclassOf o p.2) ||
  (S.studiedBy.any fun p => S.base.isSubclassOf f p.2 && S.base.isSubclassOf o p.1)

/-- The decision procedure is sound and complete for the derived relation. -/
theorem studiesB_iff {f o : Qid} : S.studiesB f o = true ↔ S.Studies f o := by
  simp only [studiesB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Studies, Asserted]
  constructor
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p.1, p.2, Or.inl (by simpa using hp), h1, h2⟩
    · exact ⟨p.2, p.1, Or.inr (by simpa using hp), h1, h2⟩
  · rintro ⟨g, x, (h | h), h1, h2⟩
    · exact Or.inl ⟨(g, x), by simpa using h, h1, h2⟩
    · exact Or.inr ⟨(x, g), by simpa using h, h1, h2⟩

/-- The derived relation as a decidable proposition. -/
instance (f o : Qid) : Decidable (S.Studies f o) :=
  decidable_of_iff _ S.studiesB_iff

variable {S}

/-- What is asserted is derived. -/
theorem studies_of_asserted {f o : Qid} (h : S.Asserted f o) : S.Studies f o :=
  ⟨f, o, h, KB.isSubclassOf_refl _ _, KB.isSubclassOf_refl _ _⟩

/-- **Down the field**: a subfield studies what its field studies. -/
theorem studies_mono_field {f f' o : Qid} (hwf : S.base.wellFormed = true)
    (hsub : S.base.isSubclassOf f' f = true) (h : S.Studies f o) : S.Studies f' o := by
  obtain ⟨g, x, ha, h1, h2⟩ := h
  refine ⟨g, x, ha, ?_, h2⟩
  exact (KB.isSubclassOf_iff hwf _ _).2
    (((KB.isSubclassOf_iff hwf _ _).1 hsub).trans ((KB.isSubclassOf_iff hwf _ _).1 h1))

/-- **Down the object**: a field studies every kind of the thing it studies. -/
theorem studies_mono_object {f o o' : Qid} (hwf : S.base.wellFormed = true)
    (hsub : S.base.isSubclassOf o' o = true) (h : S.Studies f o) : S.Studies f o' := by
  obtain ⟨g, x, ha, h1, h2⟩ := h
  refine ⟨g, x, ha, h1, ?_⟩
  exact (KB.isSubclassOf_iff hwf _ _).2
    (((KB.isSubclassOf_iff hwf _ _).1 hsub).trans ((KB.isSubclassOf_iff hwf _ _).1 h2))

/-- The two rules do not produce anything new a second time round: the derived
relation is closed under them. -/
theorem studies_idem {f o : Qid} (hwf : S.base.wellFormed = true)
    (h : ∃ g x, S.Studies g x ∧ S.base.isSubclassOf f g = true ∧
      S.base.isSubclassOf o x = true) : S.Studies f o := by
  obtain ⟨g, x, hgx, h1, h2⟩ := h
  exact studies_mono_object hwf h2 (studies_mono_field hwf h1 hgx)

variable (S)

/-- The converse relation, which is what P2579 expresses. -/
def StudiedBy (o f : Qid) : Prop := S.Studies f o

@[simp] theorem studiedBy_iff_studies {o f : Qid} : S.StudiedBy o f ↔ S.Studies f o := Iff.rfl

/-! ### Validation -/

/-- Every study statement mentions declared items. -/
def wellFormedB : Bool :=
  S.studies.all (fun p => S.base.items.contains p.1 && S.base.items.contains p.2) &&
  S.studiedBy.all (fun p => S.base.items.contains p.1 && S.base.items.contains p.2)

/-- The statements that mention an undeclared item. -/
def danglingL : List (Qid × Qid) :=
  (S.studies.filter fun p => !(S.base.items.contains p.1 && S.base.items.contains p.2)) ++
  (S.studiedBy.filter fun p => !(S.base.items.contains p.1 && S.base.items.contains p.2))

/-- **The report is empty exactly when the layer is well formed.** -/
theorem danglingL_eq_nil_iff : S.danglingL = [] ↔ S.wellFormedB = true := by
  simp only [danglingL, wellFormedB, List.append_eq_nil_iff, List.filter_eq_nil_iff,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => by simpa using h1 p hp, fun p hp => by simpa using h2 p hp⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => by simpa using h1 p hp, fun p hp => by simpa using h2 p hp⟩

/-! ### The theories of this development, as Wikidata states them

The statements below are the P2578 / P2579 statements of the seven theory items,
as downloaded in `data/theories.wdkb`. -/

/-- Topology, category theory, group theory and field theory with what Wikidata
says they study, over the downloaded theory corpus. -/
def theoryFields : StudyKB where
  base :=
    { name := "theory fields"
      items := [.wd "Q42989", .wd "Q179899", .wd "Q3532117", .wd "Q217413", .wd "Q719395",
                .wd "Q864475", .wd "Q1442189", .wd "Q874429", .wd "Q83478", .wd "Q466109",
                .wd "Q903820", .wd "Q190109", .wd "Q1062242"]
      sub := [(.wd "Q3532117", .wd "Q179899"),   -- Alexandrov topology ⊑ topological space
              (.wd "Q466109", .wd "Q83478"),     -- subgroup ⊑ group
              (.wd "Q1062242", .wd "Q179899")]   -- Grothendieck topology ⊑ topology (of a site)
      inst := [] }
  studies :=
    [(.wd "Q42989", .wd "Q179899"),   -- topology is the study of topological spaces
     (.wd "Q217413", .wd "Q719395"),  -- category theory is the study of categories,
     (.wd "Q217413", .wd "Q864475"),  --   of functors
     (.wd "Q217413", .wd "Q1442189"), --   and of natural transformations
     (.wd "Q874429", .wd "Q83478"),   -- group theory is the study of groups
     (.wd "Q903820", .wd "Q190109")]  -- field theory is the study of fields
  studiedBy :=
    [(.wd "Q1062242", .wd "Q217413")] -- a Grothendieck topology is studied by category theory

/-- The fragment is well formed. -/
theorem theoryFields_wellFormed : theoryFields.wellFormedB = true := by decide

/-- Wikidata's own statement: topology is the study of topological spaces. -/
theorem topology_studies_space : theoryFields.Studies (.wd "Q42989") (.wd "Q179899") := by decide

/-- Derived by the object rule: an Alexandrov topology is a topological space,
so topology studies those too, although Wikidata never says so. -/
theorem topology_studies_alexandrov :
    theoryFields.Studies (.wd "Q42989") (.wd "Q3532117") := by decide

/-- Derived from a `studied by` (P2579) statement read backwards: category theory
studies Grothendieck topologies. -/
theorem categoryTheory_studies_grothendieck :
    theoryFields.Studies (.wd "Q217413") (.wd "Q1062242") := by decide

/-- Group theory studies subgroups, since a subgroup is a group. -/
theorem groupTheory_studies_subgroup :
    theoryFields.Studies (.wd "Q874429") (.wd "Q466109") := by decide

/-- Nothing is invented: group theory does not study functors. -/
theorem groupTheory_not_studies_functor :
    ¬ theoryFields.Studies (.wd "Q874429") (.wd "Q864475") := by decide

/-- Topology studies Grothendieck topologies as well — through the object rule,
not through category theory. -/
theorem topology_studies_grothendieck :
    theoryFields.Studies (.wd "Q42989") (.wd "Q1062242") := by decide

end StudyKB

/-! ## `topic's main category` -/

/-- An ontology together with `topic's main category` (P910) statements.  The
inverse property `category's main topic` (P301) is the same table read the other
way. -/
structure TopicKB where
  /-- The topics and the category items. -/
  items : List Qid := []
  /-- The `topic's main category` statements, as ⟨topic, P910, category⟩ rows. -/
  table : KeyTable Qid Qid Qid := {}
deriving DecidableEq, Repr, Inhabited

namespace TopicKB

variable (T : TopicKB)

/-- The property carrying the statements. -/
def p910 : Qid := .wd "P910"

/-- The main category of a topic, if recorded. -/
def mainCategory (q : Qid) : Option Qid := T.table.value? q p910

/-- The main topic of a category — the P301 direction. -/
def mainTopic (c : Qid) : Option Qid := T.table.subject? p910 c

/-- A topic has at most one main category. -/
def SingleCategory : Prop := T.table.Functional

/-- A category is the main category of at most one topic. -/
def SingleTopic : Prop := T.table.Injective

/-- The executable checks. -/
def singleCategoryB : Bool := T.table.functionalB

/-- The executable check for `SingleTopic`. -/
def singleTopicB : Bool := T.table.injectiveB

theorem singleCategoryB_iff : T.singleCategoryB = true ↔ T.SingleCategory :=
  KeyTable.functionalB_iff

theorem singleTopicB_iff : T.singleTopicB = true ↔ T.SingleTopic := KeyTable.injectiveB_iff

variable {T}

/-- **P910 and P301 are mutually inverse partial functions**: recording the main
category of a topic is the same as recording the main topic of a category. -/
theorem mainCategory_eq_some_iff_mainTopic_eq_some (hf : T.SingleCategory) (hi : T.SingleTopic)
    {q c : Qid} : T.mainCategory q = some c ↔ T.mainTopic c = some q := by
  rw [mainCategory, mainTopic, KeyTable.value?_eq_some_iff hf, KeyTable.subject?_eq_some_iff hi]

/-- Two topics with the same main category are the same topic. -/
theorem eq_of_mainCategory_eq (hf : T.SingleCategory) (hi : T.SingleTopic) {q q' c : Qid}
    (h : T.mainCategory q = some c) (h' : T.mainCategory q' = some c) : q = q' := by
  rw [mainCategory, KeyTable.value?_eq_some_iff hf] at h h'
  exact hi _ _ _ _ h h'

/-! ### The categories of the theory items, as Wikidata records them -/

/-- The `topic's main category` statements of the theory items. -/
def theoryTopics : TopicKB where
  items := [.wd "Q42989", .wd "Q7217333", .wd "Q217413", .wd "Q7451918",
            .wd "Q874429", .wd "Q7217286", .wd "Q903820", .wd "Q7210431"]
  table := ⟨[(.wd "Q42989", p910, .wd "Q7217333"),
             (.wd "Q217413", p910, .wd "Q7451918"),
             (.wd "Q874429", p910, .wd "Q7217286"),
             (.wd "Q903820", p910, .wd "Q7210431")]⟩

theorem theoryTopics_singleCategory : theoryTopics.SingleCategory :=
  (singleCategoryB_iff theoryTopics).1 (by decide)

theorem theoryTopics_singleTopic : theoryTopics.SingleTopic :=
  (singleTopicB_iff theoryTopics).1 (by decide)

/-- So the four statements are a partial bijection between the theories and their
Wikimedia categories. -/
theorem theoryTopics_partialBijection {q c : Qid} :
    theoryTopics.mainCategory q = some c ↔ theoryTopics.mainTopic c = some q :=
  mainCategory_eq_some_iff_mainTopic_eq_some theoryTopics_singleCategory theoryTopics_singleTopic

/-- Wikidata's statement, read forwards: the main category of topology. -/
theorem topology_mainCategory :
    theoryTopics.mainCategory (.wd "Q42989") = some (.wd "Q7217333") := by decide

/-- And backwards, by the theorem above rather than by a second statement. -/
theorem topology_mainTopic : theoryTopics.mainTopic (.wd "Q7217333") = some (.wd "Q42989") :=
  theoryTopics_partialBijection.1 topology_mainCategory

end TopicKB
end Wikidata
