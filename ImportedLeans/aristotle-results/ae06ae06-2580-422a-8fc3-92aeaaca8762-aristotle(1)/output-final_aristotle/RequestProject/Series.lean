import RequestProject.Engine
import RequestProject.Properties

/-!
# The series layer: `follows` (P155), `followed by` (P156), `part of the series` (P179)
and `series ordinal` (P1545)

Besides the taxonomy (`subclass of`) and the meronomy (`part of`), *Wikidata:WikiProject
Ontology* has to account for a third, quite different structure: the **series**.  A book
belongs to a book series (`part of the series`, P179), it `follows` (P155) the previous
volume and is `followed by` (P156) the next one, and it may carry a `series ordinal`
(P1545) recording its position.  Unlike the taxonomy, this hierarchy is not a partial
order by fiat: it is supposed to be a *chain*, each item having at most one predecessor
and at most one successor.

This file adds that layer on top of the executable knowledge base of
`RequestProject.Engine`.  An `SKB` is a `KB` together with

* `part of the series` (P179) statements `(member, series)`,
* `follows` (P155) statements `(item, predecessor)` — the inverse P156 statements are
  read off the same list, since P155 and P156 are declared inverse properties, and
* `series ordinal` (P1545) values.

Everything is computable — `SKB.isAfterB`, `SKB.nextL`, `SKB.originsOfL`,
`SKB.sValid` — and certified: for a well-formed layer `isAfterB` decides the
reflexive–transitive closure of the asserted P155 statements (`SKB.isAfterB_iff`), and
the derived `followed by` list is exactly the converse of the asserted P155 statements
(`SKB.mem_nextL_iff`).

The results are:

* the derived order is a **partial order** on an acyclic layer, and its strict part is a
  strict order (`SKB.after_antisymm`, `SKB.strictlyAfter_trans`);
* the series is **well founded** (`SKB.predecessor_wf`), so every item of a well-formed
  acyclic layer has an **origin**: an item it comes after which itself follows nothing
  (`SKB.exists_origin`);
* **ordinals certify acyclicity**: if every item carries a `series ordinal` and the
  ordinals increase along `follows`, then no item can come strictly after itself
  (`SKB.no_cycle_of_ordinals`) — a cheap, purely local check that rules out the global
  defect;
* **a single predecessor makes a chain**: if no item follows two different items, then
  everything an item comes after is linearly ordered (`SKB.after_total_of_functional`),
  and the origin of an item is unique (`SKB.origin_unique`);
* the series is **not** the taxonomy: a valid layer never asserts a `follows` statement
  between taxonomically related items (`SKB.follows_not_taxonomic`), and membership in a
  series is *not* inherited through `instance of` (a worked counterexample is decided);
* series membership travels along the chain (`SKB.inSeries_of_after`).

`RequestProject.SeriesChain` enumerates a series in order, `RequestProject.SeriesExamples`
works a three-volume book series through the whole layer — together with the ontological
defects the checks are meant to catch — and `RequestProject.SeriesDiagnostics` turns the
validator into a report of individually witnessed issues.
-/

namespace Wikidata

/-- A finite, executable **series layer** over a knowledge base: the `part of the series`
(P179) statements, the `follows` (P155) statements, and the `series ordinal` (P1545)
values. -/
structure SKB where
  /-- The underlying item ontology (taxonomy). -/
  base : KB
  /-- `part of the series` (P179) statements, written `(member, series)`. -/
  series : List (Qid × Qid) := []
  /-- `follows` (P155) statements, written `(item, predecessor)`: the item comes
  immediately after its predecessor. -/
  follows : List (Qid × Qid) := []
  /-- `series ordinal` (P1545) values. -/
  ordinals : List (Qid × ℕ) := []
deriving Repr, DecidableEq, Inhabited

namespace SKB

variable (s : SKB)

/-! ### The computational engine -/

/-- The items an item directly `follows` (P155). -/
def predsL (q : Qid) : List Qid := (s.follows.filter (fun r => r.1 == q)).map Prod.snd

/-- The items an item directly `follows`, as a `Finset`. -/
def preds (q : Qid) : Finset Qid := (s.predsL q).toFinset

/-- The items an item is directly `followed by` (P156): the converse of P155. -/
def nextL (q : Qid) : List Qid := (s.follows.filter (fun r => r.2 == q)).map Prod.fst

/-- All items an item comes after, computed by saturating the P155 graph. -/
def predClosure (q : Qid) : Finset Qid := Reach.reach s.preds s.base.allF q

/-- Decides (reflexive) *comes after*: `a` is `b`, or follows an item that follows … `b`. -/
def isAfterB (a b : Qid) : Bool := b ∈ s.predClosure a

/-- Decides *strictly* comes after. -/
def isStrictlyAfterB (a b : Qid) : Bool := s.isAfterB a b && a != b

/-- The series (P179) an item is declared to belong to. -/
def seriesOfL (q : Qid) : List Qid := (s.series.filter (fun r => r.1 == q)).map Prod.snd

/-- The declared members of a series. -/
def membersOfL (t : Qid) : List Qid := s.base.items.filter (fun a => t ∈ s.seriesOfL a)

/-- The `series ordinal` (P1545) of an item, if it has one. -/
def ordinalOf? (q : Qid) : Option ℕ := s.ordinals.lookup q

/-- An item **begins** a series when it follows nothing. -/
def isOriginB (q : Qid) : Bool := s.predsL q == []

/-- The origins an item comes after. -/
def originsOfL (a : Qid) : List Qid :=
  s.base.items.filter (fun b => s.isAfterB a b && s.isOriginB b)

/-- The number of items an item comes after (itself included): the measure that makes
the series well founded. -/
def seriesHeight (a : Qid) : ℕ := (s.predClosure a).card

/-! ### The validator -/

/-- All series statements mention declared items. -/
def sWellFormed : Bool :=
  s.base.wellFormed &&
  s.series.all (fun r => r.1 ∈ s.base.items && r.2 ∈ s.base.items) &&
  s.follows.all (fun r => r.1 ∈ s.base.items && r.2 ∈ s.base.items) &&
  s.ordinals.all (fun r => r.1 ∈ s.base.items)

/-- The `follows` graph has no cycles: no item follows itself, and no two distinct items
come after one another. -/
def sAcyclic : Bool :=
  s.follows.all (fun r => r.1 != r.2) &&
  s.base.items.all (fun a => s.base.items.all
    (fun b => !(s.isAfterB a b && s.isAfterB b a) || a == b))

/-- No item follows two different items. -/
def singlePredecessor : Bool :=
  s.follows.all (fun r => s.follows.all (fun r' => !(r.1 == r'.1) || r.2 == r'.2))

/-- No item is followed by two different items. -/
def singleSuccessor : Bool :=
  s.follows.all (fun r => s.follows.all (fun r' => !(r.2 == r'.2) || r.1 == r'.1))

/-- Neighbours in the chain belong to the same series. -/
def seriesCoherent : Bool :=
  s.follows.all (fun r => s.seriesOfL r.1 == s.seriesOfL r.2)

/-- The `series ordinal` values increase along `follows`. -/
def ordinalsMonotone : Bool :=
  s.follows.all (fun r =>
    match s.ordinalOf? r.1, s.ordinalOf? r.2 with
    | some m, some n => decide (n < m)
    | _, _ => true)

/-- Every item carries a `series ordinal`. -/
def ordinalsTotal : Bool := s.base.items.all (fun a => (s.ordinalOf? a).isSome)

/-- The series is not the taxonomy: no `follows` statement relates two items that are
already related by `subclass of` or `instance of`. -/
def noTaxonomyConfusion : Bool :=
  s.follows.all (fun r =>
    !s.base.isSubclassOf r.1 r.2 && !s.base.isSubclassOf r.2 r.1 &&
    !s.base.isInstanceOf r.1 r.2 && !s.base.isInstanceOf r.2 r.1)

/-- The checks the series layer itself has to pass. -/
def sLayerValid : Bool :=
  s.sWellFormed && s.sAcyclic && s.singlePredecessor &&
  s.seriesCoherent && s.noTaxonomyConfusion

/-- The full validity check for a series layer: a valid taxonomy carrying a valid series. -/
def sValid : Bool := s.base.valid && s.sLayerValid

/-! ### Semantics -/

/-- The asserted `follows` (P155) statements, as a relation. -/
def Follows (a b : Qid) : Prop := (a, b) ∈ s.follows

/-- The asserted `followed by` (P156) statements: the converse of P155. -/
def FollowedBy (a b : Qid) : Prop := s.Follows b a

/-- Derived order: `a` comes after `b`, i.e. the reflexive–transitive closure of the
asserted `follows` statements. -/
def After (a b : Qid) : Prop := Relation.ReflTransGen s.Follows a b

/-- Membership in a series (P179). -/
def InSeries (a t : Qid) : Prop := (a, t) ∈ s.series

variable {s}

theorem mem_preds {a b : Qid} : b ∈ s.preds a ↔ s.Follows a b := by
  simp [preds, predsL, Follows, List.mem_filter, List.mem_map]

theorem mem_predsL {a b : Qid} : b ∈ s.predsL a ↔ s.Follows a b := by
  simp [predsL, Follows, List.mem_filter, List.mem_map]

/-- **`followed by` is exactly the converse of `follows`**: the derived P156 list of an
item consists of the items whose asserted P155 statement points at it. -/
theorem mem_nextL_iff {a b : Qid} : a ∈ s.nextL b ↔ s.FollowedBy b a := by
  simp [nextL, FollowedBy, Follows, List.mem_filter, List.mem_map]

theorem mem_seriesOfL {a t : Qid} : t ∈ s.seriesOfL a ↔ s.InSeries a t := by
  simp [seriesOfL, InSeries, List.mem_filter, List.mem_map]

theorem succ_eq_follows (s : SKB) : (fun u v => v ∈ s.preds u) = s.Follows := by
  funext u v; exact propext mem_preds

theorem swf_base (h : s.sWellFormed = true) : s.base.wellFormed = true := by
  simp only [sWellFormed, Bool.and_eq_true] at h; tauto

/-- Both endpoints of a `follows` statement of a well-formed layer are items. -/
theorem swf_follows (h : s.sWellFormed = true) {a b : Qid} (hab : s.Follows a b) :
    a ∈ s.base.items ∧ b ∈ s.base.items := by
  simp only [sWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simpa using h.1.2 (a, b) hab

/-- Both endpoints of a P179 statement of a well-formed layer are items. -/
theorem swf_series (h : s.sWellFormed = true) {a t : Qid} (hat : s.InSeries a t) :
    a ∈ s.base.items ∧ t ∈ s.base.items := by
  simp only [sWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simpa using h.1.1.2 (a, t) hat

theorem preds_subset_allF (h : s.sWellFormed = true) (y : Qid) : s.preds y ⊆ s.base.allF := by
  intro b hb
  simpa [KB.allF] using (swf_follows h (mem_preds.1 hb)).2

theorem preds_eq_empty_of_not_mem (h : s.sWellFormed = true) {a : Qid}
    (ha : a ∉ s.base.items) : s.preds a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun b hb => ?_
  exact ha (swf_follows h (mem_preds.1 hb)).1

/-- **Certified order computation**: in a well-formed layer the Boolean check `isAfterB`
decides the reflexive–transitive closure of the asserted P155 statements. -/
theorem isAfterB_iff (h : s.sWellFormed = true) (a b : Qid) :
    s.isAfterB a b = true ↔ s.After a b := by
  have hcl := Reach.mem_reach_iff_of_closed s.preds (preds_subset_allF h)
    (fun y hy => preds_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_follows] at hcl
  simpa [isAfterB, predClosure, After] using hcl

theorem isAfterB_refl (s : SKB) (a : Qid) : s.isAfterB a a = true := by
  simpa [isAfterB, predClosure] using Reach.mem_reach_self s.preds s.base.allF a

theorem isAfterB_of_follows (h : s.sWellFormed = true) {a b : Qid} (hab : s.Follows a b) :
    s.isAfterB a b = true :=
  (isAfterB_iff h a b).2 (Relation.ReflTransGen.single hab)

theorem isAfterB_trans (h : s.sWellFormed = true) {a b c : Qid}
    (hab : s.isAfterB a b = true) (hbc : s.isAfterB b c = true) : s.isAfterB a c = true :=
  (isAfterB_iff h a c).2 (((isAfterB_iff h a b).1 hab).trans ((isAfterB_iff h b c).1 hbc))

/-- Everything an item of the base comes after is again an item of the base. -/
theorem mem_items_of_after (h : s.sWellFormed = true) {a b : Qid}
    (ha : a ∈ s.base.items) (hab : s.After a b) : b ∈ s.base.items := by
  induction hab with
  | refl => exact ha
  | tail _ hstep _ => exact (swf_follows h hstep).2

/-! ### The order and its well-foundedness -/

/-- Antisymmetry of the derived order on an acyclic layer. -/
theorem after_antisymm (h : s.sWellFormed = true) (hac : s.sAcyclic = true) {a b : Qid}
    (hab : s.isAfterB a b = true) (hba : s.isAfterB b a = true) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    by_cases ha : a ∈ s.base.items
    · have hb : b ∈ s.base.items := mem_items_of_after h ha ((isAfterB_iff h a b).1 hab)
      simp only [sAcyclic, Bool.and_eq_true, List.all_eq_true] at hac
      have := hac.2 a ha b hb
      simp [hab, hba, hne] at this
    · -- an item outside the base has no predecessors, so it comes after itself only
      have hp : s.preds a = ∅ := preds_eq_empty_of_not_mem h ha
      have : s.After a b := (isAfterB_iff h a b).1 hab
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 this with rfl | hgen
      · exact hne rfl
      · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 hgen
        exact absurd (mem_preds.2 hc) (by simp [hp])

theorem isStrictlyAfterB_irrefl (s : SKB) (a : Qid) : s.isStrictlyAfterB a a = false := by
  simp [isStrictlyAfterB]

/-- The strict order is asymmetric on an acyclic layer. -/
theorem strictlyAfter_asymm (h : s.sWellFormed = true) (hac : s.sAcyclic = true) {a b : Qid}
    (hab : s.isStrictlyAfterB a b = true) (hba : s.isStrictlyAfterB b a = true) : False := by
  simp only [isStrictlyAfterB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (after_antisymm h hac hab.1 hba.1)

/-- The strict order is transitive on an acyclic layer. -/
theorem strictlyAfter_trans (h : s.sWellFormed = true) (hac : s.sAcyclic = true) {a b c : Qid}
    (hab : s.isStrictlyAfterB a b = true) (hbc : s.isStrictlyAfterB b c = true) :
    s.isStrictlyAfterB a c = true := by
  simp only [isStrictlyAfterB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨isAfterB_trans h hab.1 hbc.1, ?_⟩
  rintro rfl
  exact hbc.2 (after_antisymm h hac hbc.1 hab.1)

theorem predClosure_subset (h : s.sWellFormed = true) {a b : Qid}
    (hab : s.isAfterB a b = true) : s.predClosure b ⊆ s.predClosure a := by
  intro c hc
  have hbc : s.isAfterB b c = true := by simpa [isAfterB] using hc
  simpa [isAfterB] using isAfterB_trans h hab hbc

/-- **Going back along the series strictly decreases the height**: an item comes after
strictly more items than any item it strictly comes after. -/
theorem seriesHeight_lt (h : s.sWellFormed = true) (hac : s.sAcyclic = true) {a b : Qid}
    (hab : s.isStrictlyAfterB a b = true) : s.seriesHeight b < s.seriesHeight a := by
  have hab' : s.isAfterB a b = true := by
    simp only [isStrictlyAfterB, Bool.and_eq_true] at hab
    exact hab.1
  refine Finset.card_lt_card ⟨predClosure_subset h hab', fun hsub => ?_⟩
  have ha : a ∈ s.predClosure a := by simpa [isAfterB] using isAfterB_refl s a
  have hba : s.isAfterB b a = true := by simpa [isAfterB] using hsub ha
  simp only [isStrictlyAfterB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  exact hab.2 (after_antisymm h hac hab' hba)

/-- **The series is well founded**: there is no infinite chain of predecessors, so one
may reason by induction backwards along the series. -/
theorem predecessor_wf (h : s.sWellFormed = true) (hac : s.sAcyclic = true) :
    WellFounded (fun b a : Qid => s.isStrictlyAfterB a b = true) := by
  refine Subrelation.wf (r := InvImage (· < ·) s.seriesHeight) ?_ (InvImage.wf _ Nat.lt_wfRel.wf)
  intro b a hab
  exact seriesHeight_lt h hac hab

/-- On an acyclic layer, an asserted `follows` statement is strict. -/
theorem strictlyAfter_of_follows (h : s.sWellFormed = true) (hac : s.sAcyclic = true)
    {a b : Qid} (hab : s.Follows a b) : s.isStrictlyAfterB a b = true := by
  have hafter : s.isAfterB a b = true := isAfterB_of_follows h hab
  simp only [isStrictlyAfterB, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hafter, ?_⟩
  rintro rfl
  simp only [sAcyclic, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hac
  exact hac.1 (a, a) hab rfl

/-- Every item comes after at least one item, namely itself. -/
theorem seriesHeight_pos (s : SKB) (a : Qid) : 0 < s.seriesHeight a :=
  Finset.card_pos.2 ⟨a, by simpa [isAfterB] using isAfterB_refl s a⟩

/-- **Every item has an origin**: on a well-formed acyclic layer, every item comes after
some item that follows nothing at all. -/
theorem exists_origin (h : s.sWellFormed = true) (hac : s.sAcyclic = true) (a : Qid) :
    ∃ b, s.isAfterB a b = true ∧ s.isOriginB b = true := by
  suffices key : ∀ n a, s.seriesHeight a ≤ n → ∃ b, s.isAfterB a b = true ∧ s.isOriginB b = true by
    exact key (s.seriesHeight a) a le_rfl
  intro n
  induction n with
  | zero =>
      intro a ha
      -- a height of `0` is impossible: an item always comes after itself
      exact absurd (seriesHeight_pos s a) (by omega)
  | succ k ih =>
      intro a ha
      by_cases horig : s.isOriginB a = true
      · exact ⟨a, isAfterB_refl s a, horig⟩
      · obtain ⟨p, hp⟩ : ∃ p, p ∈ s.predsL a := by
          simp only [isOriginB, beq_iff_eq] at horig
          exact List.exists_mem_of_ne_nil _ horig
        have hfp : s.Follows a p := mem_predsL.1 hp
        have hlt : s.seriesHeight p < s.seriesHeight a :=
          seriesHeight_lt h hac (strictlyAfter_of_follows h hac hfp)
        obtain ⟨b, hb, hob⟩ := ih p (by omega)
        exact ⟨b, isAfterB_trans h (isAfterB_of_follows h hfp) hb, hob⟩

/-! ### Ordinals certify acyclicity -/

theorem ordinal_lt_of_follows (h : s.ordinalsMonotone = true) {a b : Qid} (hab : s.Follows a b)
    {m n : ℕ} (hm : s.ordinalOf? a = some m) (hn : s.ordinalOf? b = some n) : n < m := by
  simp only [ordinalsMonotone, List.all_eq_true] at h
  have := h (a, b) hab
  simp only [hm, hn, decide_eq_true_eq] at this
  exact this

theorem ordinal_isSome_of_mem (h : s.ordinalsTotal = true) {a : Qid} (ha : a ∈ s.base.items) :
    (s.ordinalOf? a).isSome = true := by
  simp only [ordinalsTotal, List.all_eq_true] at h
  exact h a ha

/-- Along a nonempty chain of `follows` statements the ordinals strictly decrease. -/
theorem ordinal_lt_of_transGen (hwf : s.sWellFormed = true) (hmono : s.ordinalsMonotone = true)
    (htot : s.ordinalsTotal = true) {a b : Qid} (hab : Relation.TransGen s.Follows a b) :
    ∃ m n, s.ordinalOf? a = some m ∧ s.ordinalOf? b = some n ∧ n < m := by
  induction hab with
  | single hstep =>
      obtain ⟨ha, hb⟩ := swf_follows hwf hstep
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ordinal_isSome_of_mem htot ha)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (ordinal_isSome_of_mem htot hb)
      exact ⟨m, n, hm, hn, ordinal_lt_of_follows hmono hstep hm hn⟩
  | tail _ hstep ih =>
      obtain ⟨m, k, hm, hk, hkm⟩ := ih
      obtain ⟨-, hb⟩ := swf_follows hwf hstep
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (ordinal_isSome_of_mem htot hb)
      exact ⟨m, n, hm, hn, lt_trans (ordinal_lt_of_follows hmono hstep hk hn) hkm⟩

/-- **Consistent ordinals rule out cycles**: if every item carries a `series ordinal` and
the ordinals increase along every asserted `follows` statement — two purely local checks —
then no item comes strictly after itself. -/
theorem no_cycle_of_ordinals (hwf : s.sWellFormed = true) (hmono : s.ordinalsMonotone = true)
    (htot : s.ordinalsTotal = true) (a : Qid) : ¬ Relation.TransGen s.Follows a a := by
  intro hgen
  obtain ⟨m, n, hm, hn, hlt⟩ := ordinal_lt_of_transGen hwf hmono htot hgen
  rw [hm] at hn
  exact absurd hlt (by simp [Option.some_inj.1 hn])

/-- Ordinals are monotone along the derived order as well. -/
theorem ordinal_le_of_after (hwf : s.sWellFormed = true) (hmono : s.ordinalsMonotone = true)
    (htot : s.ordinalsTotal = true) {a b : Qid} (hab : s.After a b) {m n : ℕ}
    (hm : s.ordinalOf? a = some m) (hn : s.ordinalOf? b = some n) : n ≤ m := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hab with rfl | hgen
  · rw [hm] at hn
    exact le_of_eq (Option.some_inj.1 hn).symm
  · obtain ⟨m', n', hm', hn', hlt⟩ := ordinal_lt_of_transGen hwf hmono htot hgen
    rw [hm] at hm'; rw [hn] at hn'
    have e1 : m = m' := Option.some_inj.1 hm'
    have e2 : n = n' := Option.some_inj.1 hn'
    omega

/-! ### One predecessor makes a chain -/

/-- The `singlePredecessor` check says exactly that `follows` is a partial function. -/
theorem follows_functional (h : s.singlePredecessor = true) {a b c : Qid}
    (hb : s.Follows a b) (hc : s.Follows a c) : b = c := by
  simp only [singlePredecessor, List.all_eq_true] at h
  have := h (a, b) hb (a, c) hc
  simpa using this

/-- The `singleSuccessor` check says exactly that `followed by` is a partial function. -/
theorem followedBy_functional (h : s.singleSuccessor = true) {a b c : Qid}
    (hb : s.Follows b a) (hc : s.Follows c a) : b = c := by
  simp only [singleSuccessor, List.all_eq_true] at h
  have := h (b, a) hb (c, a) hc
  simpa using this

/-- A relation in which every point has at most one successor is *linear* on the points
reachable from any given point: this is the combinatorial core of "a series is a chain". -/
theorem reflTransGen_total_of_functional {α : Type*} {F : α → α → Prop}
    (hf : ∀ x y z, F x y → F x z → y = z) {a b c : α}
    (hab : Relation.ReflTransGen F a b) (hac : Relation.ReflTransGen F a c) :
    Relation.ReflTransGen F b c ∨ Relation.ReflTransGen F c b := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hac
  | head hstep _ ih =>
      rcases Relation.ReflTransGen.cases_head hac with rfl | ⟨e, hae, hec⟩
      · exact Or.inr (Relation.ReflTransGen.head hstep (by assumption))
      · exact ih (by rwa [hf _ _ _ hae hstep] at hec)

/-- **A series with single predecessors is a chain**: everything an item comes after is
linearly ordered by the derived order. -/
theorem after_total_of_functional (h : s.singlePredecessor = true) {a b c : Qid}
    (hab : s.After a b) (hac : s.After a c) : s.After b c ∨ s.After c b :=
  reflTransGen_total_of_functional (F := s.Follows)
    (fun _ _ _ hb hc => follows_functional h hb hc) hab hac

/-- An item that follows nothing is only reached from itself. -/
theorem eq_of_after_origin {a b : Qid} (hab : s.After a b) (ha : s.isOriginB a = true) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨e, hae, -⟩
  · rfl
  · exact absurd (mem_predsL.2 hae) (by simp only [isOriginB, beq_iff_eq] at ha; simp [ha])

/-- **The origin of an item is unique** when no item follows two different items: the
series an item belongs to has a well-defined beginning. -/
theorem origin_unique (h : s.singlePredecessor = true) {a b c : Qid}
    (hab : s.After a b) (hac : s.After a c) (hb : s.isOriginB b = true)
    (hc : s.isOriginB c = true) : b = c := by
  rcases after_total_of_functional h hab hac with hbc | hcb
  · exact eq_of_after_origin hbc hb
  · exact (eq_of_after_origin hcb hc).symm

/-- Combining the two: on a well-formed, acyclic layer in which no item follows two
different items, every item comes after **exactly one** origin. -/
theorem exists_unique_origin (h : s.sWellFormed = true) (hac : s.sAcyclic = true)
    (hsp : s.singlePredecessor = true) (a : Qid) :
    ∃! b, s.isAfterB a b = true ∧ s.isOriginB b = true := by
  obtain ⟨b, hb, hob⟩ := exists_origin h hac a
  refine ⟨b, ⟨hb, hob⟩, ?_⟩
  rintro c ⟨hc, hoc⟩
  exact origin_unique hsp ((isAfterB_iff h a c).1 hc) ((isAfterB_iff h a b).1 hb) hoc hob

/-! ### The series is not the taxonomy -/

/-- On a valid layer, no `follows` statement relates two items already related by
`subclass of` or `instance of`: the series is a different hierarchy. -/
theorem follows_not_taxonomic (h : s.noTaxonomyConfusion = true) {a b : Qid}
    (hab : s.Follows a b) :
    s.base.isSubclassOf a b = false ∧ s.base.isSubclassOf b a = false ∧
      s.base.isInstanceOf a b = false ∧ s.base.isInstanceOf b a = false := by
  simp only [noTaxonomyConfusion, List.all_eq_true] at h
  have := h (a, b) hab
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- Series membership travels along the chain: if neighbours agree on their series, an
item belongs to every series any of its predecessors belongs to. -/
theorem inSeries_of_after (h : s.seriesCoherent = true) {a b t : Qid}
    (hab : s.After a b) (hbt : s.InSeries b t) : s.InSeries a t := by
  induction hab with
  | refl => exact hbt
  | @tail x y _ hstep ih =>
      refine ih ?_
      simp only [seriesCoherent, List.all_eq_true, beq_iff_eq] at h
      have hxy : s.seriesOfL x = s.seriesOfL y := h (x, y) hstep
      exact mem_seriesOfL.1 (hxy ▸ mem_seriesOfL.2 hbt)

theorem sValid_sWellFormed (h : s.sValid = true) : s.sWellFormed = true := by
  simp only [sValid, sLayerValid, Bool.and_eq_true] at h; tauto

theorem sValid_sAcyclic (h : s.sValid = true) : s.sAcyclic = true := by
  simp only [sValid, sLayerValid, Bool.and_eq_true] at h; tauto

theorem sValid_singlePredecessor (h : s.sValid = true) : s.singlePredecessor = true := by
  simp only [sValid, sLayerValid, Bool.and_eq_true] at h; tauto

theorem sValid_seriesCoherent (h : s.sValid = true) : s.seriesCoherent = true := by
  simp only [sValid, sLayerValid, Bool.and_eq_true] at h; tauto

theorem sValid_noTaxonomyConfusion (h : s.sValid = true) : s.noTaxonomyConfusion = true := by
  simp only [sValid, sLayerValid, Bool.and_eq_true] at h; tauto

theorem sValid_base (h : s.sValid = true) : s.base.valid = true := by
  simp only [sValid, Bool.and_eq_true] at h; tauto

/-- On a valid series layer every item comes after exactly one origin. -/
theorem sValid_exists_unique_origin (h : s.sValid = true) (a : Qid) :
    ∃! b, s.isAfterB a b = true ∧ s.isOriginB b = true :=
  exists_unique_origin (sValid_sWellFormed h) (sValid_sAcyclic h) (sValid_singlePredecessor h) a

/-! ### The series inside the general property framework

`RequestProject.Properties` models an arbitrary Wikidata property layer, with `subproperty
of` (P1647), transitivity, symmetry and `inverse property` (P1696) declarations, and derives
the statements they force (`PropertyLayer.Holds`).  The series layer is an instance of that
framework: it asserts P155 and P179 statements, and declares P155 and P156 an inverse pair.
The theorem below says that the general machinery then derives **exactly** the intended
statements — the P155 statements, their converses read as P156, and the P179 statements —
and nothing more; in particular `follows` is *not* made transitive. -/

/-- The three properties of the series layer: `follows` (P155), `followed by` (P156) and
`part of the series` (P179). -/
inductive SeriesProp where
  /-- `follows` (P155). -/
  | follows
  /-- `followed by` (P156). -/
  | followedBy
  /-- `part of the series` (P179). -/
  | partOfSeries
deriving DecidableEq, Repr, Inhabited

/-- The series layer read as a `PropertyLayer`: only the P155 and P179 statements are
asserted, P155 and P156 are declared an inverse pair (P1696), and none of the three
properties is declared transitive or symmetric. -/
def toPropertyLayer (s : SKB) : PropertyLayer Qid SeriesProp where
  Stmt p a b :=
    match p with
    | .follows => s.Follows a b
    | .followedBy => False
    | .partOfSeries => s.InSeries a b
  SubProp _ _ := False
  IsTransitive _ := False
  IsSymmetric _ := False
  InverseOf p q :=
    (p = .follows ∧ q = .followedBy) ∨ (p = .followedBy ∧ q = .follows)
  inverseOf_symm := by rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The statements the series layer is meant to make: the asserted `follows` statements,
their converses read as `followed by`, and the asserted `part of the series` statements. -/
def PropStmt (s : SKB) : SeriesProp → Qid → Qid → Prop := fun p a b =>
  match p with
  | .follows => s.Follows a b
  | .followedBy => s.Follows b a
  | .partOfSeries => s.InSeries a b

/-- The intended statements are closed under the derivation rules of the property layer. -/
theorem propStmt_isClosed (s : SKB) :
    PropertyLayer.IsClosed (L := s.toPropertyLayer) (s.PropStmt) where
  stmt := by
    rintro p a b h
    cases p
    · exact h
    · exact h.elim
    · exact h
  sub := by rintro p q a b ⟨⟩
  trans := by rintro p a b c ⟨⟩
  symm := by rintro p a b ⟨⟩
  inv := by
    rintro p q a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) h <;> simpa [PropStmt] using h

/-- **The property framework derives exactly the intended series statements.** Feeding the
asserted P155 and P179 statements and the P155/P156 inverse declaration to the general
property layer of `RequestProject.Properties` yields the asserted `follows` statements, the
`followed by` statements read as their converses, and the `part of the series` statements —
and nothing else. -/
theorem holds_iff (s : SKB) (p : SeriesProp) (a b : Qid) :
    s.toPropertyLayer.Holds p a b ↔ s.PropStmt p a b := by
  constructor
  · exact fun h => PropertyLayer.holds_minimal (propStmt_isClosed s) h
  · intro h
    cases p with
    | follows => exact PropertyLayer.Holds.stmt (by simpa [toPropertyLayer] using h)
    | followedBy =>
        refine PropertyLayer.Holds.inv (p := .follows) (Or.inl ⟨rfl, rfl⟩) ?_
        exact PropertyLayer.Holds.stmt (by simpa [toPropertyLayer, PropStmt] using h)
    | partOfSeries => exact PropertyLayer.Holds.stmt (by simpa [toPropertyLayer] using h)

/-- `follows` is **not** transitive in the property layer: an item does not hold a P155
statement to its predecessor's predecessor, even though it comes after it. -/
theorem holds_follows_not_trans (s : SKB) {a b c : Qid} (hab : s.Follows a b)
    (hbc : s.Follows b c) (hac : ¬ s.Follows a c) :
    s.toPropertyLayer.Holds .follows a b ∧ s.toPropertyLayer.Holds .follows b c ∧
      ¬ s.toPropertyLayer.Holds .follows a c := by
  refine ⟨(holds_iff s _ a b).2 hab, (holds_iff s _ b c).2 hbc, fun h => hac ?_⟩
  exact (holds_iff s _ a c).1 h

end SKB

end Wikidata
