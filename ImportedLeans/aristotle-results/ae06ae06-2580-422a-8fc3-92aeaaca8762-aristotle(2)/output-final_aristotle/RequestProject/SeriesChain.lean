import RequestProject.Series

/-!
# Enumerating a Wikidata series in order

`RequestProject.Series` decides *whether* one item of a series comes after another.  This
file produces the series itself: `SKB.chainFrom a` walks forward from `a` along the
`followed by` (P156) statements and returns the items in order.

The enumeration is certified.  On a well-formed, acyclic layer in which no item is followed
by two different items it lists **exactly** the items that come after `a`
(`SKB.mem_chainFrom_iff`), it lists each of them once (`SKB.chainFrom_nodup`), consecutive
entries are direct neighbours in the chain (`SKB.chainFrom_isChain`), and it starts at `a`
(`SKB.head?_chainFrom`).
-/

namespace Wikidata
namespace SKB

variable {s : SKB}

/-! ### Enumerating a series in order -/

/-- The item the chain continues with after `a`, if there is one. -/
def nextOf? (s : SKB) (a : Qid) : Option Qid := (s.nextL a).head?

/-- Follow the chain forwards from `a`, taking at most `n` steps. -/
def chainFromAux (s : SKB) : ℕ → Qid → List Qid
  | 0, a => [a]
  | n + 1, a =>
      a :: match s.nextOf? a with
        | none => []
        | some b => s.chainFromAux n b

/-- The series from `a` onwards, in order: `a`, the item that follows it, and so on. -/
def chainFrom (s : SKB) (a : Qid) : List Qid := s.chainFromAux (s.base.items.length + 1) a

theorem chainFromAux_succ_of_some {n : ℕ} {a b : Qid} (h : s.nextOf? a = some b) :
    s.chainFromAux (n + 1) a = a :: s.chainFromAux n b := by
  simp [chainFromAux, h]

theorem chainFromAux_succ_of_none {n : ℕ} {a : Qid} (h : s.nextOf? a = none) :
    s.chainFromAux (n + 1) a = [a] := by
  simp [chainFromAux, h]

theorem head?_chainFromAux (n : ℕ) (a : Qid) : (s.chainFromAux n a).head? = some a := by
  cases n <;> rfl

theorem mem_chainFromAux_self (n : ℕ) (a : Qid) : a ∈ s.chainFromAux n a := by
  cases n <;> simp [chainFromAux]

theorem follows_of_nextOf? {a b : Qid} (h : s.nextOf? a = some b) : s.Follows b a :=
  mem_nextL_iff.1 (List.mem_of_mem_head? h)

/-- With single successors the chain has no choice to make: the item recorded as following
`a` is the only one. -/
theorem nextOf?_eq_some (hss : s.singleSuccessor = true) {a e : Qid} (h : s.Follows e a) :
    s.nextOf? a = some e := by
  have hmem : e ∈ s.nextL a := mem_nextL_iff.2 h
  cases hl : s.nextL a with
  | nil => rw [hl] at hmem; simp at hmem
  | cons y ys =>
      have hy : s.Follows y a := mem_nextL_iff.1 (by rw [hl]; simp)
      have hye : y = e := followedBy_functional hss hy h
      simp [nextOf?, hl, hye]

/-- **Soundness of the enumeration**: everything the chain from `a` lists really does come
after `a`. -/
theorem after_of_mem_chainFromAux : ∀ (n : ℕ) (a x : Qid), x ∈ s.chainFromAux n a → s.After x a := by
  intro n
  induction n with
  | zero =>
      intro a x hx
      simp only [chainFromAux, List.mem_singleton] at hx
      exact hx ▸ Relation.ReflTransGen.refl
  | succ k ih =>
      intro a x hx
      cases hn : s.nextOf? a with
      | none =>
          rw [chainFromAux_succ_of_none hn] at hx
          simp only [List.mem_singleton] at hx
          exact hx ▸ Relation.ReflTransGen.refl
      | some b =>
          rw [chainFromAux_succ_of_some hn] at hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Relation.ReflTransGen.refl
          · exact (ih b x hx).tail (follows_of_nextOf? hn)

theorem seriesHeight_le_of_after (h : s.sWellFormed = true) {a b : Qid}
    (hab : s.isAfterB a b = true) : s.seriesHeight b ≤ s.seriesHeight a :=
  Finset.card_le_card (predClosure_subset h hab)

/-- The chain from an item lists each item at most once. -/
theorem chainFromAux_nodup (h : s.sWellFormed = true) (hac : s.sAcyclic = true) :
    ∀ (n : ℕ) (a : Qid), (s.chainFromAux n a).Nodup := by
  intro n
  induction n with
  | zero => intro a; simp [chainFromAux]
  | succ k ih =>
      intro a
      cases hn : s.nextOf? a with
      | none => rw [chainFromAux_succ_of_none hn]; simp
      | some b =>
          rw [chainFromAux_succ_of_some hn]
          refine List.nodup_cons.2 ⟨fun hmem => ?_, ih b⟩
          have hab : s.After a b := after_of_mem_chainFromAux k b a hmem
          have hba : s.isStrictlyAfterB b a = true :=
            strictlyAfter_of_follows h hac (follows_of_nextOf? hn)
          have h1 : s.seriesHeight a < s.seriesHeight b := seriesHeight_lt h hac hba
          have h2 : s.seriesHeight b ≤ s.seriesHeight a :=
            seriesHeight_le_of_after h ((isAfterB_iff h a b).2 hab)
          omega

/-- Consecutive entries of the chain are neighbours: each one is `followed by` the next. -/
theorem chainFromAux_isChain :
    ∀ (n : ℕ) (a : Qid), List.IsChain (fun x y : Qid => s.Follows y x) (s.chainFromAux n a) := by
  intro n
  induction n with
  | zero => intro a; exact List.isChain_singleton a
  | succ k ih =>
      intro a
      cases hn : s.nextOf? a with
      | none => rw [chainFromAux_succ_of_none hn]; exact List.isChain_singleton a
      | some b =>
          rw [chainFromAux_succ_of_some hn]
          refine List.isChain_cons.2 ⟨fun y hy => ?_, ih b⟩
          rw [head?_chainFromAux] at hy
          exact (Option.some_inj.1 hy) ▸ follows_of_nextOf? hn

/-- **Completeness of the enumeration**, with an explicit budget: `n` steps reach every item
whose height exceeds that of `a` by at most `n`. -/
theorem mem_chainFromAux_of_after (h : s.sWellFormed = true) (hac : s.sAcyclic = true)
    (hss : s.singleSuccessor = true) :
    ∀ (n : ℕ) (x a : Qid), s.After x a → s.seriesHeight x ≤ s.seriesHeight a + n →
      x ∈ s.chainFromAux n a := by
  intro n
  induction n with
  | zero =>
      intro x a hxa hle
      have hxa' : x = a := by
        by_contra hne
        have hs : s.isStrictlyAfterB x a = true := by
          simp only [isStrictlyAfterB, Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨(isAfterB_iff h x a).2 hxa, hne⟩
        have := seriesHeight_lt h hac hs
        omega
      exact hxa' ▸ mem_chainFromAux_self 0 x
  | succ k ih =>
      intro x a hxa hle
      rcases Relation.ReflTransGen.cases_tail hxa with rfl | ⟨e, hxe, hea⟩
      · exact mem_chainFromAux_self _ _
      · rw [chainFromAux_succ_of_some (nextOf?_eq_some hss hea)]
        refine List.mem_cons_of_mem _ (ih x e hxe ?_)
        have h1 : s.seriesHeight a < s.seriesHeight e :=
          seriesHeight_lt h hac (strictlyAfter_of_follows h hac hea)
        omega

/-- The number of items an item comes after is bounded by the size of the base. -/
theorem seriesHeight_le (h : s.sWellFormed = true) (x : Qid) :
    s.seriesHeight x ≤ s.base.items.length + 1 := by
  by_cases hx : x ∈ s.base.items
  · have hsub : s.predClosure x ⊆ s.base.items.toFinset := by
      intro b hb
      have hxb : s.isAfterB x b = true := by simpa [isAfterB] using hb
      simpa using mem_items_of_after h hx ((isAfterB_iff h x b).1 hxb)
    have := Finset.card_le_card hsub
    have hlen : s.base.items.toFinset.card ≤ s.base.items.length := List.toFinset_card_le _
    simp only [seriesHeight]
    omega
  · have hp : s.preds x = ∅ := preds_eq_empty_of_not_mem h hx
    have : s.predClosure x = {x} :=
      Reach.reach_eq_singleton_of_succ_empty s.preds s.base.allF hp
    simp [seriesHeight, this]

/-- **The chain enumerates the series exactly**: on a well-formed, acyclic layer in which no
item is followed by two different items, `chainFrom a` lists precisely the items that come
after `a`, each of them once, in order. -/
theorem mem_chainFrom_iff (h : s.sWellFormed = true) (hac : s.sAcyclic = true)
    (hss : s.singleSuccessor = true) (a x : Qid) : x ∈ s.chainFrom a ↔ s.After x a := by
  constructor
  · exact after_of_mem_chainFromAux _ a x
  · intro hxa
    refine mem_chainFromAux_of_after h hac hss _ x a hxa ?_
    have := seriesHeight_le h x
    omega

theorem chainFrom_nodup (h : s.sWellFormed = true) (hac : s.sAcyclic = true) (a : Qid) :
    (s.chainFrom a).Nodup := chainFromAux_nodup h hac _ a

theorem chainFrom_isChain (a : Qid) :
    List.IsChain (fun x y : Qid => s.Follows y x) (s.chainFrom a) := chainFromAux_isChain _ a

theorem head?_chainFrom (a : Qid) : (s.chainFrom a).head? = some a := head?_chainFromAux _ a

end SKB

end Wikidata
