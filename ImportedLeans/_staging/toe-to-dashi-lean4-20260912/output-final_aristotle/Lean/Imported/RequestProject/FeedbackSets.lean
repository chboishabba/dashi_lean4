import RequestProject.RelationWords
import RequestProject.PeriodicityReport

/-!
# The distance to acyclicity: minimum feedback sets of the class hierarchy

The periodicity search answers a binary question — is an item on a cycle? —
while the interesting quantity is *how far* the hierarchy is from being acyclic.
This module measures it, for the downloaded corpus, in the two standard ways:

* a **feedback edge set** is a set of `subclass of` statements whose deletion
  leaves no periodic point at all (`KB.IsFeedbackEdgeSet`), and
* a **feedback vertex set** is a set of items whose removal — together with every
  statement touching them — does the same (`KB.IsFeedbackVertexSet`).

The results, for `DefectReport.corpus`:

* `corpus_isFeedbackEdgeSet_cycleBreak` — the four deletions of the defect report
  are a feedback edge set, and `four_le_card_of_isFeedbackEdgeSet` — **every
  feedback edge set has at least four statements**.  So the minimum feedback edge
  set of the downloaded class hierarchy has exactly four edges
  (`min_feedbackEdgeSet_card`);
* `corpus_isFeedbackVertexSet_hubs`, `four_le_card_of_isFeedbackVertexSet`,
  `min_feedbackVertexSet_card` — the same for items: **four deletions are
  necessary and sufficient**, one per cycle.

Both lower bounds come from the same observation, and neither needs a new
computation over the corpus: the four cycles found by the defect report are
pairwise vertex-disjoint, so a set that breaks all of them must spend one
element on each.  The upper bounds reuse `acyclicCorpus`, whose acyclicity is
already proved, through the monotonicity lemma
`KB.isPeriodic_of_sub_subset`: deleting statements can only destroy cycles.
-/

namespace Wikidata

namespace KB

open Periodicity

/-- The knowledge base with a set of `subclass of` statements deleted. -/
def dropEdgeSet (kb : KB) (S : Finset (Qid × Qid)) : KB :=
  { kb with sub := kb.sub.filter (fun e => decide (e ∉ S)) }

/-- The knowledge base with a set of items removed from the class hierarchy:
every `subclass of` statement touching one of them is deleted. -/
def dropVertexSet (kb : KB) (S : Finset Qid) : KB :=
  { kb with sub := kb.sub.filter (fun e => decide (e.1 ∉ S ∧ e.2 ∉ S)) }

variable {kb : KB}

theorem mem_supersL_dropEdgeSet {S : Finset (Qid × Qid)} {a b : Qid} :
    b ∈ (kb.dropEdgeSet S).supersL a ↔ (a, b) ∈ kb.sub ∧ (a, b) ∉ S := by
  simp [dropEdgeSet, mem_supersL, List.mem_filter]

theorem mem_supersL_dropVertexSet {S : Finset Qid} {a b : Qid} :
    b ∈ (kb.dropVertexSet S).supersL a ↔ (a, b) ∈ kb.sub ∧ a ∉ S ∧ b ∉ S := by
  simp [dropVertexSet, mem_supersL, List.mem_filter]

/-- **Deleting statements can only destroy cycles**: a periodic point of a
smaller hierarchy is a periodic point of the bigger one. -/
theorem isPeriodic_of_sub_subset {kb' : KB} (h : ∀ e ∈ kb'.sub, e ∈ kb.sub) {x : Qid}
    (hx : IsPeriodic kb'.supersL x) : IsPeriodic kb.supersL x := by
  refine IsPeriodic.mono ?_ hx
  intro a b hab
  exact mem_supersL.2 (h (a, b) (mem_supersL.1 hab))

/-- A set of `subclass of` statements whose deletion leaves an acyclic
hierarchy. -/
def IsFeedbackEdgeSet (kb : KB) (S : Finset (Qid × Qid)) : Prop :=
  ∀ x, ¬ IsPeriodic (kb.dropEdgeSet S).supersL x

/-- A set of items whose removal leaves an acyclic hierarchy. -/
def IsFeedbackVertexSet (kb : KB) (S : Finset Qid) : Prop :=
  ∀ x, ¬ IsPeriodic (kb.dropVertexSet S).supersL x

end KB

namespace FeedbackSets

open Wikidata.Periodicity Wikidata.DefectReport Wikidata.KB

/-! ### The four cycles of the corpus, as edge and vertex sets -/

/-- The two statements of the *region* / *geographical area* cycle. -/
def regionEdges : Finset (Qid × Qid) :=
  {(Qid.wd "Q82794", Qid.wd "Q3622002"), (Qid.wd "Q3622002", Qid.wd "Q82794")}

/-- The four statements of the *scientist* cycle. -/
def scientistEdges : Finset (Qid × Qid) :=
  {(Qid.wd "Q901", Qid.wd "Q1650915"), (Qid.wd "Q1650915", Qid.wd "Q66666685"),
   (Qid.wd "Q66666685", Qid.wd "Q3400985"), (Qid.wd "Q3400985", Qid.wd "Q901")}

/-- The three statements of the *element* cycle. -/
def elementEdges : Finset (Qid × Qid) :=
  {(Qid.wd "Q379825", Qid.wd "Q5358816"), (Qid.wd "Q5358816", Qid.wd "Q36808958"),
   (Qid.wd "Q36808958", Qid.wd "Q379825")}

/-- The two statements of the *delict* cycle. -/
def delictEdges : Finset (Qid × Qid) :=
  {(Qid.wd "Q1184244", Qid.wd "Q1456832"), (Qid.wd "Q1456832", Qid.wd "Q1184244")}

/-- The items of the *region* cycle. -/
def regionItems : Finset Qid := {Qid.wd "Q82794", Qid.wd "Q3622002"}

/-- The items of the *scientist* cycle. -/
def scientistItems : Finset Qid :=
  {Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q66666685", Qid.wd "Q3400985"}

/-- The items of the *element* cycle. -/
def elementItems : Finset Qid :=
  {Qid.wd "Q379825", Qid.wd "Q5358816", Qid.wd "Q36808958"}

/-- The items of the *delict* cycle. -/
def delictItems : Finset Qid := {Qid.wd "Q1184244", Qid.wd "Q1456832"}

/-! ### Each cycle survives a deletion that misses it -/

theorem region_isPeriodic {S : Finset (Qid × Qid)} (h : ∀ e ∈ regionEdges, e ∉ S) :
    IsPeriodic (corpus.dropEdgeSet S).supersL (Qid.wd "Q82794") := by
  refine ⟨2, by norm_num, ?_⟩
  refine (ReachIn.refl _).tail (mem_supersL_dropEdgeSet.2
      ⟨geographicalArea_cycle.1, h _ (by decide)⟩) |>.tail ?_
  exact mem_supersL_dropEdgeSet.2 ⟨geographicalArea_cycle.2, h _ (by decide)⟩

theorem scientist_isPeriodic {S : Finset (Qid × Qid)} (h : ∀ e ∈ scientistEdges, e ∉ S) :
    IsPeriodic (corpus.dropEdgeSet S).supersL (Qid.wd "Q901") := by
  refine ⟨4, by norm_num, ?_⟩
  refine ((((ReachIn.refl _).tail (mem_supersL_dropEdgeSet.2
      ⟨scientist_cycle.1, h _ (by decide)⟩)).tail (mem_supersL_dropEdgeSet.2
      ⟨scientist_cycle.2.1, h _ (by decide)⟩)).tail (mem_supersL_dropEdgeSet.2
      ⟨scientist_cycle.2.2.1, h _ (by decide)⟩)).tail ?_
  exact mem_supersL_dropEdgeSet.2 ⟨scientist_cycle.2.2.2, h _ (by decide)⟩

theorem element_isPeriodic {S : Finset (Qid × Qid)} (h : ∀ e ∈ elementEdges, e ∉ S) :
    IsPeriodic (corpus.dropEdgeSet S).supersL (Qid.wd "Q379825") := by
  refine ⟨3, by norm_num, ?_⟩
  refine (((ReachIn.refl _).tail (mem_supersL_dropEdgeSet.2
      ⟨element_cycle.1, h _ (by decide)⟩)).tail (mem_supersL_dropEdgeSet.2
      ⟨element_cycle.2.1, h _ (by decide)⟩)).tail ?_
  exact mem_supersL_dropEdgeSet.2 ⟨element_cycle.2.2, h _ (by decide)⟩

theorem delict_isPeriodic {S : Finset (Qid × Qid)} (h : ∀ e ∈ delictEdges, e ∉ S) :
    IsPeriodic (corpus.dropEdgeSet S).supersL (Qid.wd "Q1184244") := by
  refine ⟨2, by norm_num, ?_⟩
  refine (ReachIn.refl _).tail (mem_supersL_dropEdgeSet.2
      ⟨delict_cycle.1, h _ (by decide)⟩) |>.tail ?_
  exact mem_supersL_dropEdgeSet.2 ⟨delict_cycle.2, h _ (by decide)⟩

theorem region_isPeriodic_vertex {S : Finset Qid} (h : ∀ q ∈ regionItems, q ∉ S) :
    IsPeriodic (corpus.dropVertexSet S).supersL (Qid.wd "Q82794") := by
  refine ⟨2, by norm_num, ?_⟩
  refine (ReachIn.refl _).tail (mem_supersL_dropVertexSet.2
      ⟨geographicalArea_cycle.1, h _ (by decide), h _ (by decide)⟩) |>.tail ?_
  exact mem_supersL_dropVertexSet.2 ⟨geographicalArea_cycle.2, h _ (by decide), h _ (by decide)⟩

theorem scientist_isPeriodic_vertex {S : Finset Qid} (h : ∀ q ∈ scientistItems, q ∉ S) :
    IsPeriodic (corpus.dropVertexSet S).supersL (Qid.wd "Q901") := by
  refine ⟨4, by norm_num, ?_⟩
  refine ((((ReachIn.refl _).tail (mem_supersL_dropVertexSet.2
      ⟨scientist_cycle.1, h _ (by decide), h _ (by decide)⟩)).tail
      (mem_supersL_dropVertexSet.2
        ⟨scientist_cycle.2.1, h _ (by decide), h _ (by decide)⟩)).tail
      (mem_supersL_dropVertexSet.2
        ⟨scientist_cycle.2.2.1, h _ (by decide), h _ (by decide)⟩)).tail ?_
  exact mem_supersL_dropVertexSet.2 ⟨scientist_cycle.2.2.2, h _ (by decide), h _ (by decide)⟩

theorem element_isPeriodic_vertex {S : Finset Qid} (h : ∀ q ∈ elementItems, q ∉ S) :
    IsPeriodic (corpus.dropVertexSet S).supersL (Qid.wd "Q379825") := by
  refine ⟨3, by norm_num, ?_⟩
  refine (((ReachIn.refl _).tail (mem_supersL_dropVertexSet.2
      ⟨element_cycle.1, h _ (by decide), h _ (by decide)⟩)).tail
      (mem_supersL_dropVertexSet.2
        ⟨element_cycle.2.1, h _ (by decide), h _ (by decide)⟩)).tail ?_
  exact mem_supersL_dropVertexSet.2 ⟨element_cycle.2.2, h _ (by decide), h _ (by decide)⟩

theorem delict_isPeriodic_vertex {S : Finset Qid} (h : ∀ q ∈ delictItems, q ∉ S) :
    IsPeriodic (corpus.dropVertexSet S).supersL (Qid.wd "Q1184244") := by
  refine ⟨2, by norm_num, ?_⟩
  refine (ReachIn.refl _).tail (mem_supersL_dropVertexSet.2
      ⟨delict_cycle.1, h _ (by decide), h _ (by decide)⟩) |>.tail ?_
  exact mem_supersL_dropVertexSet.2 ⟨delict_cycle.2, h _ (by decide), h _ (by decide)⟩

/-! ### The lower bounds -/

private theorem ne_of_disjoint {α : Type*} [DecidableEq α] {A B : Finset α} {a b : α}
    (hAB : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) : a ≠ b := by
  rintro rfl
  exact (Finset.disjoint_left.1 hAB ha) hb

private theorem four_le_card_of_four_members {α : Type*} [DecidableEq α]
    {A B C D S : Finset α} (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (ha : ∃ a ∈ A, a ∈ S) (hb : ∃ b ∈ B, b ∈ S) (hc : ∃ c ∈ C, c ∈ S)
    (hd : ∃ d ∈ D, d ∈ S) : 4 ≤ S.card := by
  obtain ⟨a, haA, haS⟩ := ha
  obtain ⟨b, hbB, hbS⟩ := hb
  obtain ⟨c, hcC, hcS⟩ := hc
  obtain ⟨d, hdD, hdS⟩ := hd
  have hab := ne_of_disjoint hAB haA hbB
  have hac := ne_of_disjoint hAC haA hcC
  have had := ne_of_disjoint hAD haA hdD
  have hbc := ne_of_disjoint hBC hbB hcC
  have hbd := ne_of_disjoint hBD hbB hdD
  have hcd := ne_of_disjoint hCD hcC hdD
  have hsub : ({a, b, c, d} : Finset α) ⊆ S := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  calc 4 = ({a, b, c, d} : Finset α).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- **Every feedback edge set of the downloaded class hierarchy has at least four
statements.**  The four cycles are pairwise disjoint, so no statement can break
two of them. -/
theorem four_le_card_of_isFeedbackEdgeSet {S : Finset (Qid × Qid)}
    (hS : corpus.IsFeedbackEdgeSet S) : 4 ≤ S.card := by
  refine four_le_card_of_four_members (A := regionEdges) (B := scientistEdges)
    (C := elementEdges) (D := delictEdges) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_
  · by_contra hcon
    push_neg at hcon
    exact hS _ (region_isPeriodic hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (scientist_isPeriodic hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (element_isPeriodic hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (delict_isPeriodic hcon)

/-- **Every feedback vertex set of the downloaded class hierarchy has at least
four items.** -/
theorem four_le_card_of_isFeedbackVertexSet {S : Finset Qid}
    (hS : corpus.IsFeedbackVertexSet S) : 4 ≤ S.card := by
  refine four_le_card_of_four_members (A := regionItems) (B := scientistItems)
    (C := elementItems) (D := delictItems) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_
  · by_contra hcon
    push_neg at hcon
    exact hS _ (region_isPeriodic_vertex hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (scientist_isPeriodic_vertex hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (element_isPeriodic_vertex hcon)
  · by_contra hcon
    push_neg at hcon
    exact hS _ (delict_isPeriodic_vertex hcon)

/-! ### The upper bounds -/

/-- The four statements the defect report deletes, as a set. -/
def cycleBreakF : Finset (Qid × Qid) :=
  {(Qid.wd "Q3622002", Qid.wd "Q82794"), (Qid.wd "Q3400985", Qid.wd "Q901"),
   (Qid.wd "Q36808958", Qid.wd "Q379825"), (Qid.wd "Q1184244", Qid.wd "Q1456832")}

/-- One item from each cycle. -/
def hubs : Finset Qid :=
  {Qid.wd "Q82794", Qid.wd "Q901", Qid.wd "Q379825", Qid.wd "Q1184244"}

theorem cycleBreakF_card : cycleBreakF.card = 4 := by decide

theorem hubs_card : hubs.card = 4 := by decide

/-- Deleting the four statements leaves no more statements than the repaired
corpus of the defect report has. -/
theorem dropEdgeSet_sub_subsetB :
    (corpus.dropEdgeSet cycleBreakF).sub.all (fun e => acyclicCorpus.sub.contains e) = true := by
  native_decide

/-- Removing the four items leaves no more statements than the repaired corpus
has either. -/
theorem dropVertexSet_sub_subsetB :
    (corpus.dropVertexSet hubs).sub.all (fun e => acyclicCorpus.sub.contains e) = true := by
  native_decide

/-- **Four deletions suffice**: the statements of the defect report are a
feedback edge set. -/
theorem corpus_isFeedbackEdgeSet_cycleBreak : corpus.IsFeedbackEdgeSet cycleBreakF := by
  intro x hx
  refine PeriodicityReport.acyclicCorpus_no_periodic x ?_
  refine KB.isPeriodic_of_sub_subset (kb := acyclicCorpus) ?_ hx
  intro e he
  have := List.all_eq_true.1 dropEdgeSet_sub_subsetB e he
  simpa using this

/-- **Four items suffice**: one item from each cycle is a feedback vertex set. -/
theorem corpus_isFeedbackVertexSet_hubs : corpus.IsFeedbackVertexSet hubs := by
  intro x hx
  refine PeriodicityReport.acyclicCorpus_no_periodic x ?_
  refine KB.isPeriodic_of_sub_subset (kb := acyclicCorpus) ?_ hx
  intro e he
  have := List.all_eq_true.1 dropVertexSet_sub_subsetB e he
  simpa using this

/-- **The minimum feedback edge set of the downloaded class hierarchy has exactly
four statements**: the distance from the hierarchy to acyclicity is four
deletions, no fewer. -/
theorem min_feedbackEdgeSet_card :
    (∃ S : Finset (Qid × Qid), corpus.IsFeedbackEdgeSet S ∧ S.card = 4) ∧
      ∀ S : Finset (Qid × Qid), corpus.IsFeedbackEdgeSet S → 4 ≤ S.card :=
  ⟨⟨cycleBreakF, corpus_isFeedbackEdgeSet_cycleBreak, cycleBreakF_card⟩,
    fun _ hS => four_le_card_of_isFeedbackEdgeSet hS⟩

/-- **The minimum feedback vertex set has exactly four items.** -/
theorem min_feedbackVertexSet_card :
    (∃ S : Finset Qid, corpus.IsFeedbackVertexSet S ∧ S.card = 4) ∧
      ∀ S : Finset Qid, corpus.IsFeedbackVertexSet S → 4 ≤ S.card :=
  ⟨⟨hubs, corpus_isFeedbackVertexSet_hubs, hubs_card⟩,
    fun _ hS => four_le_card_of_isFeedbackVertexSet hS⟩

end FeedbackSets
end Wikidata
