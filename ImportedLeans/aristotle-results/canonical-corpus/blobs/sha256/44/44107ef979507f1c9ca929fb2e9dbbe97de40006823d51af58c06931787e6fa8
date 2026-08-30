import RequestProject.Merge
import RequestProject.Normalize

/-!
# Auto-enrichment: growing the ontology from its sources

The corpus of this development was assembled by hand: a list of Wikidata
identifiers was chosen, downloaded, imported and compiled.  This file is the
verified core of the *automatic* version of that loop — the part of the
enrichment tool that Lean checks, with the network plumbing in
`RequestProject.Cli.Enrich` and the pipeline itself in
`scripts/enrich.sh`.

The loop has four stages, and each stage is a function here:

1. **scan** — a downloaded document (a Wikipedia article in some language, or an
   external page it cites) is reduced to a `ScannedSource`: the entities it
   mentions, the Wikidata properties (predicates) it uses, and the further
   sources it cites;
2. **rank** — everything the scanned sources refer to but the library does not
   yet have is collected and ordered by how often it is referred to
   (`Enrichment.termDemand`, `predicateDemand`, `sourceDemand`).  The head of
   each list is *the most referenced missing term / predicate / source*, which
   is what the next round is about;
3. **enrich** — candidate statements extracted from the sources are added to the
   knowledge base (`KB.enrich`).  This is the autoformalisation step: a claim
   read off a source becomes a `subclass of` or `instance of` statement of the
   base, tagged with the source it came from;
4. **iterate** — the sources cited by the newly scanned sources feed the next
   round (`Enrichment.step`).

What is proved:

* enrichment is **conservative**: the enriched base entails the old one
  (`KB.enrich_entails`), so every fact that was derivable stays derivable
  (`KB.enrich_isSubclassOf`, `KB.enrich_isInstanceOf`), and it is well formed
  whenever the old base was (`KB.enrich_wellFormed`) — every identifier a
  candidate mentions is declared as an item;
* enrichment is **traceable**: every statement of the enriched base is either a
  statement of the old base or carries a source (`KB.enrich_provenance`);
* the rankings are **correct**: a term is listed exactly when some scanned
  source mentions it and the base does not have it
  (`Enrichment.mem_termDemand_iff`), the list is sorted by reference count
  (`Enrichment.termDemand_sorted`) so its head really is a most referenced
  missing term (`Enrichment.termDemand_head_max`), and similarly for predicates
  and for sources;
* the loop **makes progress**: enriching with the demanded terms empties the
  term demand (`Enrichment.termDemand_absorb`), scanning a source removes it
  from the source demand (`Enrichment.sourceDemand_scan`), and the frontier
  report is empty exactly when there is nothing left to pull in
  (`Enrichment.frontier_isEmpty_iff_closed`).
-/

namespace Wikidata

/-! ## Sources -/

/-- A document the enrichment tool has downloaded: a Wikipedia article in one
language, or an external page cited by one.  `url` identifies it; `lang` is the
language code of a Wikipedia article and `""` for anything else. -/
structure SourceRef where
  /-- The address the document was downloaded from. -/
  url : String
  /-- The language code (`"en"`, `"de"`, …), or `""` for a non-Wikipedia source. -/
  lang : String := ""
  /-- The title of the document. -/
  title : String := ""
deriving DecidableEq, Repr, Inhabited

/-- A downloaded document after scanning: what the scanner found in it. -/
structure ScannedSource where
  /-- Which document this is. -/
  ref : SourceRef
  /-- The Wikidata items the document refers to. -/
  mentions : List Qid := []
  /-- The Wikidata property identifiers (`"P279"`, …) the document uses. -/
  predicates : List String := []
  /-- The addresses of the further sources the document cites. -/
  cites : List String := []
deriving DecidableEq, Repr, Inhabited

/-! ## Candidate statements

The autoformalisation step.  A claim read off a source is one of the two
statements the ontology layer understands, and it is kept together with the
address of the source it was read from, so that the enriched base can be
audited. -/

/-- A statement a source suggests adding.  (Not to be confused with
`Wikidata.Claim` of `Ranks.lean`, the claim of a Wikidata statement.) -/
inductive CandidateClaim where
  /-- `a` is a subclass of `b` (P279). -/
  | sub (a b : Qid)
  /-- `a` is an instance of `c` (P31). -/
  | inst (a c : Qid)
deriving DecidableEq, Repr, Inhabited

/-- The identifiers a candidate claim mentions. -/
def CandidateClaim.mentions : CandidateClaim → List Qid
  | .sub a b => [a, b]
  | .inst a c => [a, c]

/-- A claim together with the source it was extracted from. -/
structure Candidate where
  /-- The statement suggested. -/
  claim : CandidateClaim
  /-- The address of the source it was read from. -/
  source : String
deriving DecidableEq, Repr, Inhabited

namespace KB

/-- The `subclass of` statements a list of candidates suggests. -/
def candSub (cs : List Candidate) : List (Qid × Qid) :=
  cs.filterMap fun c => match c.claim with | .sub a b => some (a, b) | .inst _ _ => none

/-- The `instance of` statements a list of candidates suggests. -/
def candInst (cs : List Candidate) : List (Qid × Qid) :=
  cs.filterMap fun c => match c.claim with | .inst a c' => some (a, c') | .sub _ _ => none

/-- The identifiers a list of candidates mentions. -/
def candItems (cs : List Candidate) : List Qid := cs.flatMap fun c => c.claim.mentions

/-- **The enrichment step.**  Add the candidate statements to a knowledge base,
declaring every identifier they mention.

The metaclass levels are *not* invented: a candidate cannot know them, so they
are left as they were.  Consequently `KB.enrich` preserves well-formedness
(`KB.enrich_wellFormed`) but not the level discipline; a real round of
enrichment re-infers the levels afterwards, exactly as `wikidata import` does. -/
def enrich (kb : KB) (cs : List Candidate) : KB where
  name := kb.name
  items := kb.items ++ (candItems cs).filter fun q => !kb.items.contains q
  levels := kb.levels
  sub := kb.sub ++ candSub cs
  inst := kb.inst ++ candInst cs
  disj := kb.disj

variable {kb : KB} {cs : List Candidate}

theorem mem_candSub {a b : Qid} :
    (a, b) ∈ candSub cs ↔ ∃ c ∈ cs, c.claim = .sub a b := by
  simp only [candSub, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hcl⟩
    refine ⟨c, hc, ?_⟩
    cases h : c.claim with
    | sub x y => rw [h] at hcl; simp at hcl; rw [hcl.1, hcl.2]
    | inst x y => rw [h] at hcl; simp at hcl
  · rintro ⟨c, hc, hcl⟩
    exact ⟨c, hc, by rw [hcl]⟩

theorem mem_candInst {a b : Qid} :
    (a, b) ∈ candInst cs ↔ ∃ c ∈ cs, c.claim = .inst a b := by
  simp only [candInst, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hcl⟩
    refine ⟨c, hc, ?_⟩
    cases h : c.claim with
    | inst x y => rw [h] at hcl; simp at hcl; rw [hcl.1, hcl.2]
    | sub x y => rw [h] at hcl; simp at hcl
  · rintro ⟨c, hc, hcl⟩
    exact ⟨c, hc, by rw [hcl]⟩

theorem mem_candItems {q : Qid} :
    q ∈ candItems cs ↔ ∃ c ∈ cs, q ∈ c.claim.mentions := by
  simp [candItems, List.mem_flatMap]

/-- An item of the enriched base is an old item or one a candidate mentions. -/
theorem mem_enrich_items {q : Qid} :
    q ∈ (kb.enrich cs).items ↔ q ∈ kb.items ∨ q ∈ candItems cs := by
  simp only [enrich, List.mem_append, List.mem_filter]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hk : q ∈ kb.items
      · exact Or.inl hk
      · exact Or.inr ⟨h, by simpa using hk⟩

theorem subset_enrich_items : kb.items ⊆ (kb.enrich cs).items := fun _ h =>
  mem_enrich_items.2 (Or.inl h)

/-- Every identifier a candidate statement mentions is declared, so enrichment
preserves well-formedness. -/
theorem enrich_wellFormed (h : kb.wellFormed = true) : (kb.enrich cs).wellFormed = true := by
  have hsub : ∀ p ∈ kb.sub, p.1 ∈ kb.items ∧ p.2 ∈ kb.items := by
    intro p hp
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.1 p hp
  have hinst : ∀ p ∈ kb.inst, p.1 ∈ kb.items ∧ p.2 ∈ kb.items := by
    intro p hp
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.2 p hp
  have hdisj : ∀ p ∈ kb.disj, p.1 ∈ kb.items ∧ p.2 ∈ kb.items := by
    intro p hp
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2 p hp
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [enrich, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨mem_enrich_items.2 (Or.inl (hsub p hp).1), mem_enrich_items.2 (Or.inl (hsub p hp).2)⟩
    · obtain ⟨c, hc, hcl⟩ := mem_candSub (cs := cs) (a := p.1) (b := p.2) |>.1 (by simpa using hp)
      constructor
      · exact mem_enrich_items.2 (Or.inr (mem_candItems.2 ⟨c, hc, by rw [hcl]; simp [CandidateClaim.mentions]⟩))
      · exact mem_enrich_items.2 (Or.inr (mem_candItems.2 ⟨c, hc, by rw [hcl]; simp [CandidateClaim.mentions]⟩))
  · intro p hp
    simp only [enrich, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨mem_enrich_items.2 (Or.inl (hinst p hp).1), mem_enrich_items.2 (Or.inl (hinst p hp).2)⟩
    · obtain ⟨c, hc, hcl⟩ := mem_candInst (cs := cs) (a := p.1) (b := p.2) |>.1 (by simpa using hp)
      constructor
      · exact mem_enrich_items.2 (Or.inr (mem_candItems.2 ⟨c, hc, by rw [hcl]; simp [CandidateClaim.mentions]⟩))
      · exact mem_enrich_items.2 (Or.inr (mem_candItems.2 ⟨c, hc, by rw [hcl]; simp [CandidateClaim.mentions]⟩))
  · intro p hp
    have hp' : p ∈ kb.disj := by simpa [enrich] using hp
    exact ⟨mem_enrich_items.2 (Or.inl (hdisj p hp').1), mem_enrich_items.2 (Or.inl (hdisj p hp').2)⟩

/-- **Traceability.**  Every statement of an enriched base was either already
there or comes from a named source. -/
theorem enrich_provenance {a b : Qid} (hab : (a, b) ∈ (kb.enrich cs).sub) :
    (a, b) ∈ kb.sub ∨ ∃ c ∈ cs, c.claim = .sub a b := by
  simp only [enrich, List.mem_append] at hab
  exact hab.imp id fun h => mem_candSub.1 h

theorem enrich_provenance_inst {a c : Qid} (hac : (a, c) ∈ (kb.enrich cs).inst) :
    (a, c) ∈ kb.inst ∨ ∃ d ∈ cs, d.claim = .inst a c := by
  simp only [enrich, List.mem_append] at hac
  exact hac.imp id fun h => mem_candInst.1 h

/-- **Conservativity.**  The enriched base entails the base it came from. -/
theorem enrich_entails (h : kb.wellFormed = true) : (kb.enrich cs).Entails kb = true := by
  have hwf := enrich_wellFormed (cs := cs) h
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    refine (isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single ?_)
    simp [Sub, enrich, hp]
  · intro p hp
    have : p ∈ (kb.enrich cs).inst := by simp [enrich, hp]
    have hsub : (kb.enrich cs).isSubclassOf p.2 p.2 = true :=
      (isSubclassOf_iff hwf p.2 p.2).2 Relation.ReflTransGen.refl
    simp only [isInstanceOf, List.any_eq_true]
    refine ⟨p.2, ?_, hsub⟩
    simp only [directClassesL, List.mem_map, List.mem_filter]
    exact ⟨p, ⟨this, by simp⟩, rfl⟩

/-- Enrichment never loses a derived `subclass of` fact. -/
theorem enrich_isSubclassOf (h : kb.wellFormed = true) {a b : Qid}
    (hab : kb.isSubclassOf a b = true) : (kb.enrich cs).isSubclassOf a b = true :=
  entails_subclass (enrich_wellFormed h) h (enrich_entails h) hab

/-- Enrichment never loses a derived `instance of` fact. -/
theorem enrich_isInstanceOf (h : kb.wellFormed = true) {a c : Qid}
    (hac : kb.isInstanceOf a c = true) : (kb.enrich cs).isInstanceOf a c = true :=
  entails_instance (enrich_wellFormed h) h (enrich_entails h) hac

/-- Enriching with nothing changes nothing. -/
@[simp] theorem enrich_nil : kb.enrich [] = kb := by
  cases kb; simp [enrich, candSub, candInst, candItems]

/-- Every candidate statement really is asserted by the enriched base. -/
theorem enrich_sub_of_mem {a b : Qid} {c : Candidate} (hc : c ∈ cs) (hcl : c.claim = .sub a b) :
    (a, b) ∈ (kb.enrich cs).sub := by
  simp only [enrich, List.mem_append]
  exact Or.inr (mem_candSub.2 ⟨c, hc, hcl⟩)

theorem enrich_inst_of_mem {a b : Qid} {c : Candidate} (hc : c ∈ cs) (hcl : c.claim = .inst a b) :
    (a, b) ∈ (kb.enrich cs).inst := by
  simp only [enrich, List.mem_append]
  exact Or.inr (mem_candInst.2 ⟨c, hc, hcl⟩)

/-- What a candidate suggests is derivable after enrichment. -/
theorem enrich_isSubclassOf_cand (h : kb.wellFormed = true) {a b : Qid} {c : Candidate}
    (hc : c ∈ cs) (hcl : c.claim = .sub a b) : (kb.enrich cs).isSubclassOf a b = true :=
  (isSubclassOf_iff (enrich_wellFormed h) a b).2
    (Relation.ReflTransGen.single (enrich_sub_of_mem hc hcl))

end KB

/-! ## The frontier: what is missing, and how often it is referred to -/

namespace Enrichment

/-- The relation used to order the demand lists: by decreasing count. -/
def byCount {α : Type} (x y : α × ℕ) : Prop := y.2 ≤ x.2

instance {α : Type} : DecidableRel (byCount (α := α)) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

instance {α : Type} : Std.Total (byCount (α := α)) :=
  ⟨fun x y => by unfold byCount; exact Nat.le_total y.2 x.2⟩

instance {α : Type} : IsTrans (α × ℕ) byCount := ⟨fun _ _ _ hxy hyz => le_trans hyz hxy⟩

/-- Sort a table of counts, most referenced first. -/
def rank {α : Type} (l : List (α × ℕ)) : List (α × ℕ) := List.insertionSort byCount l

theorem rank_perm {α : Type} (l : List (α × ℕ)) : (rank l).Perm l :=
  List.perm_insertionSort _ l

@[simp] theorem mem_rank {α : Type} {l : List (α × ℕ)} {p : α × ℕ} : p ∈ rank l ↔ p ∈ l :=
  (rank_perm l).mem_iff

theorem rank_sorted {α : Type} (l : List (α × ℕ)) : (rank l).Pairwise byCount :=
  List.pairwise_insertionSort _ l

/-- The head of a ranked list is a maximum: nothing in the list is referred to
more often. -/
theorem rank_head_max {α : Type} {l : List (α × ℕ)} {p q : α × ℕ}
    (hp : rank l = p :: (rank l).tail) (hq : q ∈ l) : q.2 ≤ p.2 := by
  have hmem : q ∈ rank l := mem_rank.2 hq
  rw [hp] at hmem
  rcases List.mem_cons.1 hmem with h | h
  · exact le_of_eq (congrArg Prod.snd h)
  · have := rank_sorted l
    rw [hp] at this
    exact (List.pairwise_cons.1 this).1 q h

/-! ### Terms -/

/-- How many of the scanned sources mention an item. -/
def refCount (ss : List ScannedSource) (q : Qid) : ℕ :=
  (ss.filter fun s => s.mentions.contains q).length

/-- The items some scanned source mentions but the base does not declare. -/
def missingTerms (kb : KB) (ss : List ScannedSource) : List Qid :=
  ((ss.flatMap fun s => s.mentions).filter fun q => !kb.items.contains q).dedup

theorem mem_missingTerms {kb : KB} {ss : List ScannedSource} {q : Qid} :
    q ∈ missingTerms kb ss ↔ (∃ s ∈ ss, q ∈ s.mentions) ∧ q ∉ kb.items := by
  simp [missingTerms, List.mem_dedup, List.mem_filter, List.mem_flatMap, and_comm]

/-- **The missing terms, most referenced first.** -/
def termDemand (kb : KB) (ss : List ScannedSource) : List (Qid × ℕ) :=
  rank ((missingTerms kb ss).map fun q => (q, refCount ss q))

theorem mem_termDemand_iff {kb : KB} {ss : List ScannedSource} {q : Qid} {n : ℕ} :
    (q, n) ∈ termDemand kb ss ↔
      ((∃ s ∈ ss, q ∈ s.mentions) ∧ q ∉ kb.items) ∧ n = refCount ss q := by
  simp only [termDemand, mem_rank, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxq⟩
    obtain ⟨rfl, rfl⟩ : x = q ∧ n = refCount ss x := by
      exact ⟨(Prod.mk.injEq _ _ _ _ ▸ hxq).1.symm ▸ rfl, ((Prod.mk.injEq _ _ _ _ ▸ hxq).2).symm⟩
    exact ⟨mem_missingTerms.1 hx, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨q, mem_missingTerms.2 hx, rfl⟩

theorem termDemand_sorted (kb : KB) (ss : List ScannedSource) :
    (termDemand kb ss).Pairwise byCount := rank_sorted _

/-- The first entry of the term demand really is a most referenced missing
term. -/
theorem termDemand_head_max {kb : KB} {ss : List ScannedSource} {p : Qid × ℕ}
    (hp : termDemand kb ss = p :: (termDemand kb ss).tail)
    {q : Qid} {n : ℕ} (hq : (q, n) ∈ termDemand kb ss) : n ≤ p.2 := by
  have := rank_head_max (l := (missingTerms kb ss).map fun q => (q, refCount ss q))
    (p := p) (q := (q, n)) (by simpa [termDemand] using hp) (by simpa [termDemand] using hq)
  simpa using this

/-- Every missing term is mentioned at least once. -/
theorem refCount_pos_of_mem_missingTerms {kb : KB} {ss : List ScannedSource} {q : Qid}
    (hq : q ∈ missingTerms kb ss) : 0 < refCount ss q := by
  obtain ⟨⟨s, hs, hqs⟩, -⟩ := mem_missingTerms.1 hq
  have : s ∈ ss.filter fun s => s.mentions.contains q := by
    simp [List.mem_filter, hs, hqs]
  exact List.length_pos_of_mem this

/-- Declaring the missing terms as items — the enrichment tool's `absorb` step. -/
def absorb (kb : KB) (ss : List ScannedSource) : KB :=
  { kb with items := kb.items ++ missingTerms kb ss }

/-- **Progress.**  After absorbing the demanded terms, nothing is missing. -/
theorem termDemand_absorb (kb : KB) (ss : List ScannedSource) :
    termDemand (absorb kb ss) ss = [] := by
  have : missingTerms (absorb kb ss) ss = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro q hq
    obtain ⟨⟨s, hs, hqs⟩, hnot⟩ := mem_missingTerms.1 hq
    exact hnot (by
      simp only [absorb, List.mem_append]
      by_cases hk : q ∈ kb.items
      · exact Or.inl hk
      · exact Or.inr (mem_missingTerms.2 ⟨⟨s, hs, hqs⟩, hk⟩))
  simp [termDemand, this, rank]

/-- Absorbing terms adds no statement, so it changes nothing that is derivable. -/
theorem absorb_entails (kb : KB) (ss : List ScannedSource) (h : kb.wellFormed = true) :
    (absorb kb ss).Entails kb = true := by
  have hwf : (absorb kb ss).wellFormed = true := by
    simp only [KB.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨⟨fun p hp => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
    · exact ⟨by simp [absorb, (h.1.1 p hp).1], by simp [absorb, (h.1.1 p hp).2]⟩
    · exact ⟨by simp [absorb, (h.1.2 p hp).1], by simp [absorb, (h.1.2 p hp).2]⟩
    · exact ⟨by simp [absorb, (h.2 p hp).1], by simp [absorb, (h.2 p hp).2]⟩
  simp only [KB.Entails, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · exact (KB.isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single (by simpa [KB.Sub, absorb] using hp))
  · have hsub : (absorb kb ss).isSubclassOf p.2 p.2 = true :=
      (KB.isSubclassOf_iff hwf p.2 p.2).2 Relation.ReflTransGen.refl
    simp only [KB.isInstanceOf, List.any_eq_true]
    refine ⟨p.2, ?_, hsub⟩
    simp only [KB.directClassesL, List.mem_map, List.mem_filter]
    exact ⟨p, ⟨by simpa [absorb] using hp, by simp⟩, rfl⟩

/-! ### Predicates

The other half of the scan: which Wikidata *properties* the sources use.  The
library models a fixed list of them (`subclass of`, `instance of`, `part of`,
…); a property that turns up in a source and is not on that list is a candidate
for a new predicate in Lean. -/

/-- How many scanned sources use a property. -/
def predCount (ss : List ScannedSource) (p : String) : ℕ :=
  (ss.filter fun s => s.predicates.contains p).length

/-- The properties the sources use and the library does not model. -/
def missingPredicates (modelled : List String) (ss : List ScannedSource) : List String :=
  ((ss.flatMap fun s => s.predicates).filter fun p => !modelled.contains p).dedup

theorem mem_missingPredicates {modelled : List String} {ss : List ScannedSource} {p : String} :
    p ∈ missingPredicates modelled ss ↔ (∃ s ∈ ss, p ∈ s.predicates) ∧ p ∉ modelled := by
  simp [missingPredicates, List.mem_dedup, List.mem_filter, List.mem_flatMap, and_comm]

/-- **The candidate new predicates, most used first.** -/
def predicateDemand (modelled : List String) (ss : List ScannedSource) : List (String × ℕ) :=
  rank ((missingPredicates modelled ss).map fun p => (p, predCount ss p))

theorem mem_predicateDemand_iff {modelled : List String} {ss : List ScannedSource}
    {p : String} {n : ℕ} :
    (p, n) ∈ predicateDemand modelled ss ↔
      ((∃ s ∈ ss, p ∈ s.predicates) ∧ p ∉ modelled) ∧ n = predCount ss p := by
  simp only [predicateDemand, mem_rank, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxq⟩
    have hx1 : x = p := (Prod.mk.injEq _ _ _ _ ▸ hxq).1
    have hx2 : predCount ss x = n := (Prod.mk.injEq _ _ _ _ ▸ hxq).2
    subst hx1
    exact ⟨mem_missingPredicates.1 hx, hx2.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨p, mem_missingPredicates.2 hx, rfl⟩

theorem predicateDemand_sorted (modelled : List String) (ss : List ScannedSource) :
    (predicateDemand modelled ss).Pairwise byCount := rank_sorted _

theorem predicateDemand_head_max {modelled : List String} {ss : List ScannedSource}
    {p : String × ℕ} (hp : predicateDemand modelled ss = p :: (predicateDemand modelled ss).tail)
    {q : String} {n : ℕ} (hq : (q, n) ∈ predicateDemand modelled ss) : n ≤ p.2 := by
  have := rank_head_max (l := (missingPredicates modelled ss).map fun p => (p, predCount ss p))
    (p := p) (q := (q, n)) (by simpa [predicateDemand] using hp) (by simpa [predicateDemand] using hq)
  simpa using this

/-- Once a predicate is modelled it is no longer demanded. -/
theorem not_mem_missingPredicates_of_modelled {modelled : List String} {ss : List ScannedSource}
    {p : String} (hp : p ∈ modelled) : p ∉ missingPredicates modelled ss := by
  intro h
  exact (mem_missingPredicates.1 h).2 hp

/-! ### Sources

The last part of the loop: the documents cited by the documents already scanned.
Those not yet scanned are the next round's downloads, ranked by how many scanned
sources cite them. -/

/-- How many scanned sources cite an address. -/
def citeCount (ss : List ScannedSource) (u : String) : ℕ :=
  (ss.filter fun s => s.cites.contains u).length

/-- The addresses cited by a scanned source but not themselves scanned. -/
def missingSources (ss : List ScannedSource) : List String :=
  ((ss.flatMap fun s => s.cites).filter fun u => !(ss.any fun s => s.ref.url == u)).dedup

theorem mem_missingSources {ss : List ScannedSource} {u : String} :
    u ∈ missingSources ss ↔ (∃ s ∈ ss, u ∈ s.cites) ∧ ∀ s ∈ ss, s.ref.url ≠ u := by
  simp [missingSources, List.mem_dedup, List.mem_filter, List.mem_flatMap]

/-- **The sources still to download, most cited first.** -/
def sourceDemand (ss : List ScannedSource) : List (String × ℕ) :=
  rank ((missingSources ss).map fun u => (u, citeCount ss u))

theorem mem_sourceDemand_iff {ss : List ScannedSource} {u : String} {n : ℕ} :
    (u, n) ∈ sourceDemand ss ↔
      ((∃ s ∈ ss, u ∈ s.cites) ∧ ∀ s ∈ ss, s.ref.url ≠ u) ∧ n = citeCount ss u := by
  simp only [sourceDemand, mem_rank, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxq⟩
    have hx1 : x = u := (Prod.mk.injEq _ _ _ _ ▸ hxq).1
    have hx2 : citeCount ss x = n := (Prod.mk.injEq _ _ _ _ ▸ hxq).2
    subst hx1
    exact ⟨mem_missingSources.1 hx, hx2.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨u, mem_missingSources.2 hx, rfl⟩

theorem sourceDemand_sorted (ss : List ScannedSource) :
    (sourceDemand ss).Pairwise byCount := rank_sorted _

theorem sourceDemand_head_max {ss : List ScannedSource} {p : String × ℕ}
    (hp : sourceDemand ss = p :: (sourceDemand ss).tail)
    {u : String} {n : ℕ} (hq : (u, n) ∈ sourceDemand ss) : n ≤ p.2 := by
  have := rank_head_max (l := (missingSources ss).map fun u => (u, citeCount ss u))
    (p := p) (q := (u, n)) (by simpa [sourceDemand] using hp) (by simpa [sourceDemand] using hq)
  simpa using this

/-- **Progress, for sources.**  A source that has been scanned is no longer
demanded. -/
theorem sourceDemand_scan {ss : List ScannedSource} {s : ScannedSource} (hs : s ∈ ss)
    {n : ℕ} : (s.ref.url, n) ∉ sourceDemand ss := by
  intro h
  exact ((mem_sourceDemand_iff.1 h).1.2 s hs) rfl

/-! ## The tool's state, and when it is done -/

/-- The state of an enrichment run: what is known, what has been scanned, and
which properties the formalisation models. -/
structure State where
  /-- The knowledge base built so far. -/
  base : KB
  /-- The documents already downloaded and scanned. -/
  scanned : List ScannedSource := []
  /-- The Wikidata properties the library has a Lean predicate for. -/
  modelled : List String := []
deriving Repr, Inhabited

/-- Everything the scanned sources point at, ranked. -/
structure Frontier where
  /-- Missing items, most referenced first. -/
  terms : List (Qid × ℕ)
  /-- Unmodelled properties, most used first. -/
  predicates : List (String × ℕ)
  /-- Uncollected sources, most cited first. -/
  sources : List (String × ℕ)
deriving Repr, Inhabited

/-- The frontier of a state: the tool's to-do list. -/
def State.frontier (e : State) : Frontier where
  terms := termDemand e.base e.scanned
  predicates := predicateDemand e.modelled e.scanned
  sources := sourceDemand e.scanned

/-- A state is *closed* when the scanned sources point at nothing new: every
item they mention is declared, every property they use is modelled, and every
source they cite has been scanned. -/
def State.Closed (e : State) : Prop :=
  (∀ s ∈ e.scanned, ∀ q ∈ s.mentions, q ∈ e.base.items) ∧
  (∀ s ∈ e.scanned, ∀ p ∈ s.predicates, p ∈ e.modelled) ∧
  (∀ s ∈ e.scanned, ∀ u ∈ s.cites, ∃ t ∈ e.scanned, t.ref.url = u)

/-- Whether a frontier is empty. -/
def Frontier.isEmpty (f : Frontier) : Bool :=
  f.terms.isEmpty && f.predicates.isEmpty && f.sources.isEmpty

/-- **The report is empty exactly when there is nothing left to pull in.** -/
theorem frontier_isEmpty_iff_closed (e : State) :
    e.frontier.isEmpty = true ↔ e.Closed := by
  constructor
  · intro h
    simp only [Frontier.isEmpty, Bool.and_eq_true, List.isEmpty_iff, State.frontier] at h
    obtain ⟨⟨ht, hp⟩, hs⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro s hs' q hq
      by_contra hqk
      have : (q, refCount e.scanned q) ∈ termDemand e.base e.scanned :=
        mem_termDemand_iff.2 ⟨⟨⟨s, hs', hq⟩, hqk⟩, rfl⟩
      rw [ht] at this; exact absurd this (List.not_mem_nil)
    · intro s hs' p hp'
      by_contra hpk
      have : (p, predCount e.scanned p) ∈ predicateDemand e.modelled e.scanned :=
        mem_predicateDemand_iff.2 ⟨⟨⟨s, hs', hp'⟩, hpk⟩, rfl⟩
      rw [hp] at this; exact absurd this (List.not_mem_nil)
    · intro s hs' u hu
      by_contra hnot
      push_neg at hnot
      have : (u, citeCount e.scanned u) ∈ sourceDemand e.scanned :=
        mem_sourceDemand_iff.2 ⟨⟨⟨s, hs', hu⟩, fun t ht => hnot t ht⟩, rfl⟩
      rw [hs] at this; exact absurd this (List.not_mem_nil)
  · rintro ⟨ht, hp, hs⟩
    simp only [Frontier.isEmpty, Bool.and_eq_true, List.isEmpty_iff, State.frontier]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.eq_nil_iff_forall_not_mem]
      rintro ⟨q, n⟩ hmem
      obtain ⟨⟨⟨s, hs', hq⟩, hqk⟩, -⟩ := mem_termDemand_iff.1 hmem
      exact hqk (ht s hs' q hq)
    · rw [List.eq_nil_iff_forall_not_mem]
      rintro ⟨p, n⟩ hmem
      obtain ⟨⟨⟨s, hs', hq⟩, hqk⟩, -⟩ := mem_predicateDemand_iff.1 hmem
      exact hqk (hp s hs' p hq)
    · rw [List.eq_nil_iff_forall_not_mem]
      rintro ⟨u, n⟩ hmem
      obtain ⟨⟨⟨s, hs', hq⟩, hqk⟩, -⟩ := mem_sourceDemand_iff.1 hmem
      obtain ⟨t, ht', htu⟩ := hs s hs' u hq
      exact hqk t ht' htu

/-- One round of the loop: absorb the demanded terms, add the candidate
statements the scanner produced, and record the newly scanned sources. -/
def State.step (e : State) (cs : List Candidate) (fresh : List ScannedSource) : State where
  base := (absorb e.base e.scanned).enrich cs
  scanned := e.scanned ++ fresh
  modelled := e.modelled

/-- A round never loses an item. -/
theorem State.subset_step_items (e : State) (cs : List Candidate) (fresh : List ScannedSource) :
    e.base.items ⊆ (e.step cs fresh).base.items := by
  intro q hq
  exact KB.mem_enrich_items.2 (Or.inl (by simp [absorb, hq]))

/-- A round never loses a scanned source. -/
theorem State.subset_step_scanned (e : State) (cs : List Candidate)
    (fresh : List ScannedSource) : e.scanned ⊆ (e.step cs fresh).scanned := by
  intro s hs; simp [State.step, hs]

/-- **A round is conservative**: everything the base knew, it still knows. -/
theorem State.step_entails (e : State) (cs : List Candidate) (fresh : List ScannedSource)
    (h : e.base.wellFormed = true) : (e.step cs fresh).base.Entails e.base = true := by
  have h1 : (absorb e.base e.scanned).wellFormed = true := by
    simp only [KB.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨⟨fun p hp => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
    · exact ⟨by simp [absorb, (h.1.1 p hp).1], by simp [absorb, (h.1.1 p hp).2]⟩
    · exact ⟨by simp [absorb, (h.1.2 p hp).1], by simp [absorb, (h.1.2 p hp).2]⟩
    · exact ⟨by simp [absorb, (h.2 p hp).1], by simp [absorb, (h.2 p hp).2]⟩
  have hstep : (e.step cs fresh).base = (absorb e.base e.scanned).enrich cs := rfl
  simp only [KB.Entails, Bool.and_eq_true, List.all_eq_true]
  have hwf := KB.enrich_wellFormed (cs := cs) h1
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [hstep]
    refine (KB.isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single ?_)
    simp [KB.Sub, KB.enrich, absorb, hp]
  · rw [hstep]
    have hmem : p ∈ ((absorb e.base e.scanned).enrich cs).inst := by
      simp [KB.enrich, absorb, hp]
    have hsub : ((absorb e.base e.scanned).enrich cs).isSubclassOf p.2 p.2 = true :=
      (KB.isSubclassOf_iff hwf p.2 p.2).2 Relation.ReflTransGen.refl
    simp only [KB.isInstanceOf, List.any_eq_true]
    refine ⟨p.2, ?_, hsub⟩
    simp only [KB.directClassesL, List.mem_map, List.mem_filter]
    exact ⟨p, ⟨hmem, by simp⟩, rfl⟩

end Enrichment
end Wikidata
