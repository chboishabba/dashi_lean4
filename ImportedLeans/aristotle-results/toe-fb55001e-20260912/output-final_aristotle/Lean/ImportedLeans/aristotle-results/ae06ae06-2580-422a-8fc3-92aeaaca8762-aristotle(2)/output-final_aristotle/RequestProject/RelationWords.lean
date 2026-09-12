import RequestProject.Paths
import RequestProject.Periodicity

/-!
# Relation words: every relation of the ontology layer as an operator

`RequestProject.Periodicity` searches for periodic points of **one** transition
system, the `subclass of` successor map.  The ontology layer of Wikidata carries
two relations, `subclass of` (P279) and `instance of` (P31), and this file turns
each of them into an operator

```
T : Qid → List Qid
```

so that *words* in the two letters — `P279`, `P31`, `P31·P279`, `P279·P31`,
`P279²`, … — become transition systems in their own right.  The periodicity
search of `RequestProject.Periodicity` then applies to each of them, and asks
for the **words of the relation algebra that close**:

```
T_{i_k} ⋯ T_{i_1} (x) ∋ x.
```

The alphabet is the one already used by the property-path layer
(`Wikidata.Link`), so a word is literally the path expression
`Wikidata.wordExpr w`, a composition of atomic steps, and the semantics of a
word over an abstract ontology is the semantics of that path expression.

Contents:

* `Wikidata.instCount` — how many `instance of` letters a word has — and
  `Wikidata.wordExpr` — the word as a property path;
* `Wikidata.Ontology.level_of_eval_wordExpr`: **along a word the metaclass level
  increases by exactly the number of `instance of` letters**, and hence
  `Ontology.instCount_eq_zero_of_closed`: in a genuine ontology **no word
  containing an `instance of` letter can close**.  Cycles of the mixed
  transition systems are therefore defects of the same kind as `subclass of`
  cycles, and they are invisible to a search that follows P279 alone;
* `Wikidata.KB.wordStep` — the computable operator of a word over a knowledge
  base — with `KB.mem_wordStep` identifying it with the path semantics, and the
  search `KB.wordPeriodOf` / `KB.wordPeriodicItems` (`KB.mem_wordPeriodicItems`);
* `Wikidata.KB.no_ontology_of_word_return`: a closing word with an `instance of`
  letter in a knowledge base rules out **every** abstract ontology over its
  statements;
* `Wikidata.Periodicity.phaseCertB` — a phase certificate for an arbitrary
  transition system, decided by a forward and a backward reachability
  computation instead of a closure table, with
  `Periodicity.isPeriodDivisor_of_phaseCertB`; and its converse-flavoured
  companion `Periodicity.periodDivisor_eq_one_of_isReturn_one`, which says that
  a component containing a fixed point has fundamental period one, no matter how
  long its shortest cycles through other points are;
* `Wikidata.Periodicity.ReachIn.mono` and `IsPeriodic.mono_kb`: periodicity only
  ever disappears when statements are deleted, which is what makes minimal
  feedback sets meaningful.
-/

namespace Wikidata

/-! ### Words in the two ontology relations -/

/-- The number of `instance of` letters in a word. -/
def instCount (w : List Link) : ℕ := (w.filter (fun l => l == Link.p31)).length

@[simp] theorem instCount_nil : instCount [] = 0 := rfl

@[simp] theorem instCount_cons_p31 (w : List Link) :
    instCount (Link.p31 :: w) = instCount w + 1 := by
  simp [instCount]

@[simp] theorem instCount_cons_p279 (w : List Link) :
    instCount (Link.p279 :: w) = instCount w := by
  simp [instCount]

/-- A word of relations, read as a property path: a composition of atomic
steps. -/
def wordExpr (w : List Link) : PathExpr Link := w.foldr (fun l e => .seq (.atom l) e) .id

@[simp] theorem wordExpr_nil : wordExpr [] = .id := rfl

@[simp] theorem wordExpr_cons (l : Link) (w : List Link) :
    wordExpr (l :: w) = .seq (.atom l) (wordExpr w) := rfl

/-! ### The level discipline forbids mixed cycles -/

namespace Ontology

variable {I : Type*} {O : Ontology I}

/-- **Along a word the metaclass level increases by the number of `instance of`
letters in it.**  `subclass of` steps keep the level, `instance of` steps raise
it by one. -/
theorem level_of_eval_wordExpr :
    ∀ (w : List Link) {x y : I}, PathExpr.Eval O.linkRel (wordExpr w) x y →
      O.level y = O.level x + instCount w := by
  intro w
  induction w with
  | nil =>
      intro x y h
      simp only [wordExpr_nil, PathExpr.Eval] at h
      simp [← h]
  | cons l w ih =>
      intro x y h
      obtain ⟨m, hm, hrest⟩ := h
      have hstep := ih hrest
      cases l with
      | p31 =>
          have : O.level m = O.level x + 1 := O.level_P31 hm
          rw [hstep, this]
          simp [instCount_cons_p31]
          omega
      | p279 =>
          have : O.level x = O.level m := O.level_P279 hm
          rw [hstep, ← this]
          simp

/-- **No word containing an `instance of` letter can close in an ontology.**  A
closed walk returns to the level it started from, and each `instance of` letter
raises the level by one. -/
theorem instCount_eq_zero_of_closed {w : List Link} {x : I}
    (h : PathExpr.Eval O.linkRel (wordExpr w) x x) : instCount w = 0 := by
  have := level_of_eval_wordExpr w h
  omega

end Ontology

/-! ### Words as computable operators on a knowledge base -/

namespace KB

variable (kb : KB)

/-- The one-step operator of a single relation, as a list. -/
def linkStepL : Link → Qid → List Qid
  | .p31, q => kb.directClassesL q
  | .p279, q => kb.supersL q

/-- The relation of a single letter. -/
def LinkRel : Link → Qid → Qid → Prop
  | .p31 => kb.Inst
  | .p279 => kb.Sub

/-- **The operator of a word**: apply its letters from left to right. -/
def wordStep (kb : KB) : List Link → Qid → List Qid
  | [], q => [q]
  | l :: w, q => ((kb.linkStepL l q).flatMap (wordStep kb w)).dedup

variable {kb}

theorem mem_linkStepL {l : Link} {a b : Qid} :
    b ∈ kb.linkStepL l a ↔ kb.LinkRel l a b := by
  cases l with
  | p31 => simpa [linkStepL, LinkRel] using mem_directClassesL
  | p279 => simpa [linkStepL, LinkRel] using mem_supersL

/-- **The operator computes the path semantics of the word**: the values of
`kb.wordStep w` at `x` are exactly the endpoints of walks that spell `w`. -/
theorem mem_wordStep :
    ∀ (w : List Link) {x y : Qid},
      y ∈ kb.wordStep w x ↔ PathExpr.Eval kb.LinkRel (wordExpr w) x y := by
  intro w
  induction w with
  | nil => intro x y; simp [wordStep, eq_comm]
  | cons l w ih =>
      intro x y
      simp only [wordStep, List.mem_dedup, List.mem_flatMap, wordExpr_cons, PathExpr.Eval]
      constructor
      · rintro ⟨m, hm, hy⟩
        exact ⟨m, mem_linkStepL.1 hm, (ih).1 hy⟩
      · rintro ⟨m, hm, hy⟩
        exact ⟨m, mem_linkStepL.2 hm, (ih).2 hy⟩

variable (kb)

/-- The periodicity search for a word: the least number of applications of the
whole word that returns `x` to itself, if there is one within `bound`. -/
def wordPeriodOf (w : List Link) (bound : ℕ) (x : Qid) : Option ℕ :=
  Periodicity.periodOf (kb.wordStep w) bound x

/-- The items on a cycle of the transition system of a word, found by the
search. -/
def wordPeriodicItems (w : List Link) (bound : ℕ) : List Qid :=
  kb.items.filter (fun x => (kb.wordPeriodOf w bound x).isSome)

variable {kb}

/-- The search is exactly right up to its bound: an item is listed precisely
when some number of applications of the word, at most `bound`, returns it to
itself. -/
theorem mem_wordPeriodicItems {w : List Link} {bound : ℕ} {x : Qid} :
    x ∈ kb.wordPeriodicItems w bound ↔
      x ∈ kb.items ∧ ∃ n ≤ bound, Periodicity.IsReturn (kb.wordStep w) n x := by
  simp only [wordPeriodicItems, List.mem_filter, wordPeriodOf]
  constructor
  · rintro ⟨hx, hsome⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (by simpa using hsome)
    obtain ⟨hret, hle, -⟩ := Periodicity.periodOf_eq_some_iff.1 hn
    exact ⟨hx, n, hle, hret⟩
  · rintro ⟨hx, n, hle, hret⟩
    exact ⟨hx, by simpa using Periodicity.isSome_periodOf hret hle⟩

/-- One application of a word moves the metaclass level of any ontology over the
knowledge base by the number of `instance of` letters of the word. -/
theorem level_of_mem_wordStep {O : Ontology Qid} (hO : O.linkRel = kb.LinkRel)
    {w : List Link} {x y : Qid} (h : y ∈ kb.wordStep w x) :
    O.level y = O.level x + instCount w := by
  refine Ontology.level_of_eval_wordExpr w ?_
  rw [hO]
  exact mem_wordStep w |>.1 h

/-- **A closing word with an `instance of` letter rules out every ontology.**  If
some number of applications of `w` returns an item of the knowledge base to
itself and `w` uses `instance of` at least once, then no abstract
`Wikidata.Ontology` has the P31 and P279 statements of the base. -/
theorem no_ontology_of_word_return {w : List Link} {x : Qid}
    (hper : Periodicity.IsPeriodic (kb.wordStep w) x) (hw : 0 < instCount w)
    (O : Ontology Qid) (hO : O.linkRel = kb.LinkRel) : False := by
  obtain ⟨n, hn, hreach⟩ := hper
  have key : ∀ m (y : Qid), Periodicity.ReachIn (kb.wordStep w) m x y →
      O.level y = O.level x + m * instCount w := by
    intro m
    induction m with
    | zero =>
        intro y hy
        rw [← Periodicity.reachIn_zero_iff.1 hy]
        simp
    | succ m ih =>
        intro z hz
        obtain ⟨y, hy, hstep⟩ := Periodicity.reachIn_succ_iff.1 hz
        have h1 := ih y hy
        have h2 := level_of_mem_wordStep hO hstep
        rw [h2, h1]
        ring
  have := key n x hreach
  have hpos : 0 < n * instCount w := Nat.mul_pos hn hw
  omega

end KB

/-! ### Phase certificates for an arbitrary transition system -/

namespace Periodicity

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Walks only get scarcer when the step function does: a walk of a smaller
transition system is a walk of the bigger one. -/
theorem ReachIn.mono {step step' : α → List α} (h : ∀ a b, b ∈ step' a → b ∈ step a)
    {n : ℕ} {x y : α} (hr : ReachIn step' n x y) : ReachIn step n x y := by
  induction hr with
  | refl x => exact ReachIn.refl x
  | tail _ hz ih => exact ih.tail (h _ _ hz)

omit [DecidableEq α] in
/-- Periodicity is monotone in the step function. -/
theorem IsPeriodic.mono {step step' : α → List α} (h : ∀ a b, b ∈ step' a → b ∈ step a)
    {x : α} (hx : IsPeriodic step' x) : IsPeriodic step x := by
  obtain ⟨n, hn, hr⟩ := hx
  exact ⟨n, hn, ReachIn.mono h hr⟩

omit [DecidableEq α] in
/-- **A component with a fixed point has fundamental period one.**  If some point
of the component returns after a single step then the only number dividing all
return times is `1`, however long the shortest cycles through the other points
of the component are. -/
theorem periodDivisor_eq_one_of_isReturn_one {step : α → List α} {d : ℕ} {x : α}
    (hd : IsPeriodDivisor step d x) (h : IsReturn step 1 x) : d = 1 :=
  Nat.dvd_one.1 (hd 1 h)

/-- A step function, read as a `Finset`-valued successor map. -/
def stepF (step : α → List α) (q : α) : Finset α := (step q).toFinset

/-- **The phase check of a component**, decided by two reachability
computations: forward from `x` along `step`, backward from `x` along `rev`.
Inside the strongly connected component of `x` — the points reachable from `x`
that reach `x` back — every step that stays in the returning region must advance
the phase by one. -/
def phaseCertB (step rev : α → List α) (all : Finset α) (x : α) (d : ℕ) [NeZero d]
    (phase : α → ZMod d) : Bool :=
  let R := Reach.reach (stepF step) all x
  let B := Reach.reach (stepF rev) all x
  decide (∀ y ∈ R ∩ B, ∀ z ∈ step y, z ∈ B → phase z = phase y + 1)

omit [DecidableEq α] in
theorem reflTransGen_of_reachIn {step : α → List α} {n : ℕ} {x y : α}
    (h : ReachIn step n x y) : Relation.ReflTransGen (fun a b => b ∈ step a) x y := by
  induction h with
  | refl x => exact Relation.ReflTransGen.refl
  | tail _ hz ih => exact ih.tail hz

/-- **The phase certificate bounds the period of the component from below.**  If
the check succeeds, every return time of `x` is divisible by `d`.  The
hypotheses say that `rev` is the reverse graph of `step` and that both stay
inside the finite ambient set `all`, outside of which there are no steps at
all. -/
theorem isPeriodDivisor_of_phaseCertB {step rev : α → List α} {all : Finset α} {x : α}
    {d : ℕ} [NeZero d] {phase : α → ZMod d}
    (hstepF : ∀ y, stepF step y ⊆ all) (hstepOut : ∀ y, y ∉ all → step y = [])
    (hrevF : ∀ y, stepF rev y ⊆ all) (hrevOut : ∀ y, y ∉ all → rev y = [])
    (hrev : ∀ u v, v ∈ rev u ↔ u ∈ step v)
    (h : phaseCertB step rev all x d phase = true) :
    IsPeriodDivisor step d x := by
  set R := Reach.reach (stepF step) all x with hR
  set B := Reach.reach (stepF rev) all x with hB
  have hstepEmpty : ∀ y, y ∉ all → stepF step y = ∅ := by
    intro y hy; simp [stepF, hstepOut y hy]
  have hrevEmpty : ∀ y, y ∉ all → stepF rev y = ∅ := by
    intro y hy; simp [stepF, hrevOut y hy]
  have hmemR : ∀ y, Relation.ReflTransGen (fun a b => b ∈ step a) x y → y ∈ R := by
    intro y hy
    rw [hR, Reach.mem_reach_iff_of_closed (stepF step) hstepF hstepEmpty]
    exact hy.mono (fun a b hab => by simpa [stepF] using hab)
  have hmemB : ∀ y, Relation.ReflTransGen (fun a b => b ∈ step a) y x → y ∈ B := by
    intro y hy
    rw [hB, Reach.mem_reach_iff_of_closed (stepF rev) hrevF hrevEmpty]
    have : Relation.ReflTransGen (fun a b => b ∈ rev a) x y := by
      refine Relation.ReflTransGen.mono ?_ (Relation.ReflTransGen.swap hy)
      intro a b hab
      exact (hrev a b).2 hab
    exact this.mono (fun a b hab => by simpa [stepF] using hab)
  have h' : ∀ y ∈ R ∩ B, ∀ z ∈ step y, z ∈ B → phase z = phase y + 1 := of_decide_eq_true h
  refine isPeriodDivisor_of_phase phase ?_
  rintro y z ⟨a, ha⟩ ⟨b, hb⟩ hz ⟨c, hc⟩
  have hyR : y ∈ R := hmemR y (reflTransGen_of_reachIn ha)
  have hyB : y ∈ B := hmemB y (reflTransGen_of_reachIn hb)
  have hzB : z ∈ B := hmemB z (reflTransGen_of_reachIn hc)
  exact h' y (Finset.mem_inter.2 ⟨hyR, hyB⟩) z hz hzB

end Periodicity

/-! ### The `subclass of` graph as a transition system with a reverse -/

namespace KB

variable (kb : KB)

/-- The direct *subclasses* of an item: the reverse of the `subclass of` step. -/
def subsL (q : Qid) : List Qid := (kb.sub.filter (fun e => e.2 == q)).map Prod.fst

variable {kb}

theorem mem_subsL {u v : Qid} : u ∈ kb.subsL v ↔ kb.Sub u v := by
  simp only [subsL, List.mem_map, List.mem_filter, beq_iff_eq, Sub]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hmem, hb⟩, ha⟩
    cases ha; cases hb; exact hmem
  · intro h; exact ⟨(u, v), ⟨h, rfl⟩, rfl⟩

variable (kb)

/-- **The phase check of a `subclass of` component**, decided by a forward and a
backward reachability computation from the item — no closure table needed. -/
def subPhaseCertB (x : Qid) (d : ℕ) [NeZero d] (phase : Qid → ZMod d) : Bool :=
  Periodicity.phaseCertB kb.supersL kb.subsL kb.allF x d phase

variable {kb}

/-- **The period of a `subclass of` component, certified from the reachability
computation**: if the check succeeds, every `subclass of` cycle through `x` has
length divisible by `d`. -/
theorem isPeriodDivisor_of_subPhaseCertB (hwf : kb.wellFormed = true) {x : Qid} {d : ℕ}
    [NeZero d] {phase : Qid → ZMod d} (h : kb.subPhaseCertB x d phase = true) :
    Periodicity.IsPeriodDivisor kb.supersL d x := by
  refine Periodicity.isPeriodDivisor_of_phaseCertB (rev := kb.subsL) (all := kb.allF)
    ?_ ?_ ?_ ?_ ?_ h
  · intro y
    have : Periodicity.stepF kb.supersL y = kb.supers y := rfl
    rw [this]
    exact supers_subset_all hwf y
  · intro y hy
    refine List.eq_nil_iff_forall_not_mem.2 fun b hb => ?_
    exact hy (mem_allF.2 (wf_sub hwf (mem_supersL.1 hb)).1)
  · intro y u hu
    have : kb.Sub u y := mem_subsL.1 (by simpa [Periodicity.stepF] using hu)
    exact mem_allF.2 (wf_sub hwf this).1
  · intro y hy
    refine List.eq_nil_iff_forall_not_mem.2 fun u hu => ?_
    exact hy (mem_allF.2 (wf_sub hwf (mem_subsL.1 hu)).2)
  · intro u v
    rw [mem_subsL, mem_supersL]
    rfl

end KB

end Wikidata
