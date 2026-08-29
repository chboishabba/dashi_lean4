import RequestProject.Taxa

/-!
# Lineages and lowest common ancestors of Wikidata taxa

`RequestProject.Taxa` decides *whether* one taxon descends from another.  This file walks
the hierarchy itself:

* `TKB.lineage a` climbs from a taxon to its root along `parent taxon` (P171) and returns
  the lineage in order — *Homo sapiens*, *Homo*, *Hominidae*, …;
* `TKB.lcaOf? a b` returns the **lowest common ancestor** of two taxa: the last taxon their
  lineages share.

Both are certified.  On a well-formed, acyclic layer in which no taxon has two parent taxa
the lineage lists **exactly** the ancestors of the taxon (`TKB.mem_lineage_iff`), lists each
of them once (`TKB.lineage_nodup`), consecutive entries are parent and child
(`TKB.lineage_isChain`), and the list starts at the taxon itself (`TKB.head?_lineage`).  The
lowest common ancestor is an ancestor of both taxa (`TKB.lca_sound`), it is the *lowest*
such — every common ancestor is an ancestor of it (`TKB.lca_least`) — and it exists whenever
the two taxa have any common ancestor at all (`TKB.lca_isSome`); together these determine it
uniquely (`TKB.lca_unique`).
-/

namespace Wikidata
namespace TKB

variable {k : TKB}

/-! ### The lineage of a taxon -/

/-- The parent taxon the walk continues with, if there is one. -/
def parentOf? (k : TKB) (a : Qid) : Option Qid := (k.parentsL a).head?

/-- Climb towards the root from `a`, taking at most `n` steps. -/
def lineageAux (k : TKB) : ℕ → Qid → List Qid
  | 0, a => [a]
  | n + 1, a =>
      a :: match k.parentOf? a with
        | none => []
        | some p => k.lineageAux n p

/-- The lineage of a taxon: the taxon, its parent taxon, and so on up to the root. -/
def lineage (k : TKB) (a : Qid) : List Qid := k.lineageAux (k.base.items.length + 1) a

theorem lineageAux_succ_of_some {n : ℕ} {a p : Qid} (h : k.parentOf? a = some p) :
    k.lineageAux (n + 1) a = a :: k.lineageAux n p := by
  simp [lineageAux, h]

theorem lineageAux_succ_of_none {n : ℕ} {a : Qid} (h : k.parentOf? a = none) :
    k.lineageAux (n + 1) a = [a] := by
  simp [lineageAux, h]

theorem head?_lineageAux (n : ℕ) (a : Qid) : (k.lineageAux n a).head? = some a := by
  cases n <;> rfl

theorem mem_lineageAux_self (n : ℕ) (a : Qid) : a ∈ k.lineageAux n a := by
  cases n <;> simp [lineageAux]

theorem parentTaxon_of_parentOf? {a p : Qid} (h : k.parentOf? a = some p) : k.ParentTaxon a p :=
  mem_parentsL.1 (List.mem_of_mem_head? h)

/-- The walk has no choice to make: with single parents, the recorded parent taxon is the
only one. -/
theorem parentOf?_eq_some (hsp : k.singleParent = true) {a e : Qid} (h : k.ParentTaxon a e) :
    k.parentOf? a = some e := by
  have hmem : e ∈ k.parentsL a := mem_parentsL.2 h
  cases hl : k.parentsL a with
  | nil => rw [hl] at hmem; simp at hmem
  | cons y ys =>
      have hy : k.ParentTaxon a y := mem_parentsL.1 (by rw [hl]; simp)
      have hye : y = e := parent_functional hsp hy h
      simp [parentOf?, hl, hye]

/-- A taxon with no recorded parent taxon is a root. -/
theorem isRootB_of_parentOf?_none {a : Qid} (h : k.parentOf? a = none) : k.isRootB a = true := by
  simp only [parentOf?, List.head?_eq_none_iff] at h
  simp [isRootB, h]

/-- **Soundness of the lineage**: everything it lists really is an ancestor. -/
theorem descent_of_mem_lineageAux :
    ∀ (n : ℕ) (a x : Qid), x ∈ k.lineageAux n a → k.DescendsFrom a x := by
  intro n
  induction n with
  | zero =>
      intro a x hx
      simp only [lineageAux, List.mem_singleton] at hx
      exact hx ▸ Relation.ReflTransGen.refl
  | succ m ih =>
      intro a x hx
      cases hp : k.parentOf? a with
      | none =>
          rw [lineageAux_succ_of_none hp] at hx
          simp only [List.mem_singleton] at hx
          exact hx ▸ Relation.ReflTransGen.refl
      | some p =>
          rw [lineageAux_succ_of_some hp] at hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.head (parentTaxon_of_parentOf? hp) (ih p x hx)

theorem taxonDepth_le_of_descent (h : k.tWellFormed = true) {a b : Qid}
    (hab : k.isDescendantB a b = true) : k.taxonDepth b ≤ k.taxonDepth a :=
  Finset.card_le_card (ancestorClosure_subset h hab)

/-- The lineage lists each taxon at most once. -/
theorem lineageAux_nodup (h : k.tWellFormed = true) (hac : k.tAcyclic = true) :
    ∀ (n : ℕ) (a : Qid), (k.lineageAux n a).Nodup := by
  intro n
  induction n with
  | zero => intro a; simp [lineageAux]
  | succ m ih =>
      intro a
      cases hp : k.parentOf? a with
      | none => rw [lineageAux_succ_of_none hp]; simp
      | some p =>
          rw [lineageAux_succ_of_some hp]
          refine List.nodup_cons.2 ⟨fun hmem => ?_, ih p⟩
          have hpa : k.DescendsFrom p a := descent_of_mem_lineageAux m p a hmem
          have hstrict : k.isStrictDescendantB a p = true :=
            strictDescent_of_parent h hac (parentTaxon_of_parentOf? hp)
          have h1 : k.taxonDepth p < k.taxonDepth a := taxonDepth_lt h hac hstrict
          have h2 : k.taxonDepth a ≤ k.taxonDepth p :=
            taxonDepth_le_of_descent h ((isDescendantB_iff h p a).2 hpa)
          omega

/-- Consecutive entries of a lineage are a taxon and its parent taxon. -/
theorem lineageAux_isChain :
    ∀ (n : ℕ) (a : Qid), List.IsChain k.ParentTaxon (k.lineageAux n a) := by
  intro n
  induction n with
  | zero => intro a; exact List.isChain_singleton a
  | succ m ih =>
      intro a
      cases hp : k.parentOf? a with
      | none => rw [lineageAux_succ_of_none hp]; exact List.isChain_singleton a
      | some p =>
          rw [lineageAux_succ_of_some hp]
          refine List.isChain_cons.2 ⟨fun y hy => ?_, ih p⟩
          rw [head?_lineageAux] at hy
          exact (Option.some_inj.1 hy) ▸ parentTaxon_of_parentOf? hp

/-- **Completeness of the lineage**, with an explicit budget. -/
theorem mem_lineageAux_of_descent (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) :
    ∀ (n : ℕ) (a x : Qid), k.DescendsFrom a x → k.taxonDepth a ≤ k.taxonDepth x + n →
      x ∈ k.lineageAux n a := by
  intro n
  induction n with
  | zero =>
      intro a x hax hle
      have hxa : a = x := by
        by_contra hne
        have hs : k.isStrictDescendantB a x = true := by
          simp only [isStrictDescendantB, Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨(isDescendantB_iff h a x).2 hax, hne⟩
        have := taxonDepth_lt h hac hs
        omega
      exact hxa ▸ mem_lineageAux_self 0 a
  | succ m ih =>
      intro a x hax hle
      rcases Relation.ReflTransGen.cases_head hax with rfl | ⟨e, hae, hex⟩
      · exact mem_lineageAux_self _ _
      · rw [lineageAux_succ_of_some (parentOf?_eq_some hsp hae)]
        refine List.mem_cons_of_mem _ (ih e x hex ?_)
        have h1 : k.taxonDepth e < k.taxonDepth a :=
          taxonDepth_lt h hac (strictDescent_of_parent h hac hae)
        omega

/-- The number of ancestors of a taxon is bounded by the size of the base. -/
theorem taxonDepth_le (h : k.tWellFormed = true) (x : Qid) :
    k.taxonDepth x ≤ k.base.items.length + 1 := by
  by_cases hx : x ∈ k.base.items
  · have hsub : k.ancestorClosure x ⊆ k.base.items.toFinset := by
      intro b hb
      have hxb : k.isDescendantB x b = true := by simpa [isDescendantB] using hb
      simpa using mem_items_of_descent h hx ((isDescendantB_iff h x b).1 hxb)
    have := Finset.card_le_card hsub
    have hlen : k.base.items.toFinset.card ≤ k.base.items.length := List.toFinset_card_le _
    simp only [taxonDepth]
    omega
  · have hp : k.parentsF x = ∅ := parentsF_eq_empty_of_not_mem h hx
    have : k.ancestorClosure x = {x} :=
      Reach.reach_eq_singleton_of_succ_empty k.parentsF k.base.allF hp
    simp [taxonDepth, this]

/-- **The lineage enumerates the ancestors exactly**: on a well-formed, acyclic layer in
which no taxon has two parent taxa, `lineage a` lists precisely the taxa `a` descends from,
each of them once, from `a` upwards. -/
theorem mem_lineage_iff (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) (a x : Qid) : x ∈ k.lineage a ↔ k.DescendsFrom a x := by
  constructor
  · exact descent_of_mem_lineageAux _ a x
  · intro hax
    refine mem_lineageAux_of_descent h hac hsp _ a x hax ?_
    have := taxonDepth_le h a
    omega

theorem lineage_nodup (h : k.tWellFormed = true) (hac : k.tAcyclic = true) (a : Qid) :
    (k.lineage a).Nodup := lineageAux_nodup h hac _ a

theorem lineage_isChain (a : Qid) : List.IsChain k.ParentTaxon (k.lineage a) :=
  lineageAux_isChain _ a

theorem head?_lineage (a : Qid) : (k.lineage a).head? = some a := head?_lineageAux _ a

/-! ### The lowest common ancestor -/

/-- Climb from `a` until an ancestor of `b` is found, taking at most `n` steps. -/
def lcaAux (k : TKB) : ℕ → Qid → Qid → Option Qid
  | 0, _, _ => none
  | n + 1, a, b =>
      if k.isDescendantB b a then some a
      else
        match k.parentOf? a with
        | none => none
        | some p => k.lcaAux n p b

/-- The **lowest common ancestor** of two taxa: the first taxon on the lineage of `a` that
`b` also descends from. -/
def lcaOf? (k : TKB) (a b : Qid) : Option Qid := k.lcaAux (k.base.items.length + 1) a b

theorem lcaAux_succ {n : ℕ} {a b : Qid} :
    k.lcaAux (n + 1) a b =
      if k.isDescendantB b a then some a
      else match k.parentOf? a with
        | none => none
        | some p => k.lcaAux n p b := rfl

/-- **Soundness**: what the search returns is a common ancestor of the two taxa. -/
theorem lcaAux_sound (h : k.tWellFormed = true) :
    ∀ (n : ℕ) (a b c : Qid), k.lcaAux n a b = some c →
      k.DescendsFrom a c ∧ k.DescendsFrom b c := by
  intro n
  induction n with
  | zero => intro a b c hc; simp [lcaAux] at hc
  | succ m ih =>
      intro a b c hc
      rw [lcaAux_succ] at hc
      by_cases hd : k.isDescendantB b a = true
      · rw [if_pos hd] at hc
        rw [← Option.some_inj.1 hc]
        exact ⟨Relation.ReflTransGen.refl, (isDescendantB_iff h b a).1 hd⟩
      · rw [if_neg (by simpa using hd)] at hc
        cases hp : k.parentOf? a with
        | none => rw [hp] at hc; simp at hc
        | some p =>
            rw [hp] at hc
            obtain ⟨hpc, hbc⟩ := ih p b c hc
            exact ⟨Relation.ReflTransGen.head (parentTaxon_of_parentOf? hp) hpc, hbc⟩

/-- **Leastness**: every common ancestor of the two taxa is an ancestor of the one the
search returns — what it finds really is the *lowest* common ancestor. -/
theorem lcaAux_least (h : k.tWellFormed = true) (hsp : k.singleParent = true) :
    ∀ (n : ℕ) (a b c d : Qid), k.lcaAux n a b = some c →
      k.DescendsFrom a d → k.DescendsFrom b d → k.DescendsFrom c d := by
  intro n
  induction n with
  | zero => intro a b c d hc; simp [lcaAux] at hc
  | succ m ih =>
      intro a b c d hc had hbd
      rw [lcaAux_succ] at hc
      by_cases hd : k.isDescendantB b a = true
      · rw [if_pos hd] at hc
        rw [← Option.some_inj.1 hc]
        exact had
      · rw [if_neg (by simpa using hd)] at hc
        have hne : a ≠ d := by
          rintro rfl
          exact hd ((isDescendantB_iff h b a).2 hbd)
        cases hp : k.parentOf? a with
        | none => rw [hp] at hc; simp at hc
        | some p =>
            rw [hp] at hc
            have hpd : k.DescendsFrom p d := by
              rcases Relation.ReflTransGen.cases_head had with rfl | ⟨e, hae, hed⟩
              · exact absurd rfl hne
              · rwa [parent_functional hsp hae (parentTaxon_of_parentOf? hp)] at hed
            exact ih p b c d hc hpd hbd

/-- **Existence**: two taxa with a common ancestor have a lowest one. -/
theorem lcaAux_isSome (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) :
    ∀ (n : ℕ) (a b : Qid), k.taxonDepth a ≤ n →
      (∃ d, k.DescendsFrom a d ∧ k.DescendsFrom b d) → (k.lcaAux n a b).isSome := by
  intro n
  induction n with
  | zero => intro a b hle; exact absurd (taxonDepth_pos k a) (by omega)
  | succ m ih =>
      intro a b hle hcommon
      rw [lcaAux_succ]
      by_cases hd : k.isDescendantB b a = true
      · rw [if_pos hd]; rfl
      · rw [if_neg (by simpa using hd)]
        obtain ⟨d, had, hbd⟩ := hcommon
        have hne : a ≠ d := by
          rintro rfl
          exact hd ((isDescendantB_iff h b a).2 hbd)
        cases hp : k.parentOf? a with
        | none =>
            exact absurd (eq_of_descent_root had (isRootB_of_parentOf?_none hp)) hne
        | some p =>
            have hpd : k.DescendsFrom p d := by
              rcases Relation.ReflTransGen.cases_head had with rfl | ⟨e, hae, hed⟩
              · exact absurd rfl hne
              · rwa [parent_functional hsp hae (parentTaxon_of_parentOf? hp)] at hed
            have hlt : k.taxonDepth p < k.taxonDepth a :=
              taxonDepth_lt h hac (strictDescent_of_parent h hac (parentTaxon_of_parentOf? hp))
            exact ih p b (by omega) ⟨d, hpd, hbd⟩

/-- The lowest common ancestor of two taxa is an ancestor of both. -/
theorem lca_sound (h : k.tWellFormed = true) {a b c : Qid} (hc : k.lcaOf? a b = some c) :
    k.DescendsFrom a c ∧ k.DescendsFrom b c := lcaAux_sound h _ a b c hc

/-- Every common ancestor of two taxa is an ancestor of their lowest common ancestor. -/
theorem lca_least (h : k.tWellFormed = true) (hsp : k.singleParent = true) {a b c d : Qid}
    (hc : k.lcaOf? a b = some c) (had : k.DescendsFrom a d) (hbd : k.DescendsFrom b d) :
    k.DescendsFrom c d := lcaAux_least h hsp _ a b c d hc had hbd

/-- Two taxa with any common ancestor have a lowest common ancestor. -/
theorem lca_isSome (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) {a b : Qid}
    (hcommon : ∃ d, k.DescendsFrom a d ∧ k.DescendsFrom b d) : (k.lcaOf? a b).isSome := by
  refine lcaAux_isSome h hac hsp _ a b ?_ hcommon
  exact taxonDepth_le h a

/-- **The lowest common ancestor is characterised by its two properties**: it is the unique
common ancestor of `a` and `b` that every common ancestor of `a` and `b` sits above. -/
theorem lca_unique (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) {a b c e : Qid} (hc : k.lcaOf? a b = some c)
    (hea : k.DescendsFrom a e) (heb : k.DescendsFrom b e)
    (hleast : ∀ d, k.DescendsFrom a d → k.DescendsFrom b d → k.DescendsFrom e d) : e = c := by
  obtain ⟨hac', hbc'⟩ := lca_sound h hc
  have h1 : k.DescendsFrom e c := hleast c hac' hbc'
  have h2 : k.DescendsFrom c e := lca_least h hsp hc hea heb
  exact descent_antisymm h hac ((isDescendantB_iff h e c).2 h1) ((isDescendantB_iff h c e).2 h2)

end TKB
end Wikidata
