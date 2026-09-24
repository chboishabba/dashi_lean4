import RequestProject.Engine
import RequestProject.Merge

/-!
# Constructing new facts: saturation and certified justifications

This file is the reasoning core of the command line tool (`RequestProject.Cli.Main`,
subcommands `derive` and `why`).  Given a knowledge base it *constructs new facts*:

* `KB.newSubL` — the `subclass of` (P279) statements that are **derivable but not
  asserted**, and `KB.newInstL` — likewise for `instance of` (P31);
* `KB.saturate` — the knowledge base with all of those added.

Everything is certified:

* `KB.newSubL_sound` / `KB.newInstL_sound`: a constructed fact really is derivable
  in the input, so the tool never invents information;
* `KB.saturate_isSubclassOf` / `KB.saturate_isInstanceOf`: saturation is
  *conservative* — it derives exactly the same facts as the input;
* `KB.saturate_valid`: saturation preserves validity;
* `KB.newSubL_saturate` / `KB.newInstL_saturate`: the tool reaches a fixed point
  after a single pass.

For explanations, a *chain* is a list of items `a = c₀, c₁, …, cₙ = b` each linked
to the next by an asserted P279 statement.  `KB.checkSubChain` checks a chain and
`KB.subChain?` searches for one; `KB.checkSubChain_sound` says a chain that passes
the check witnesses a derived `subclass of` fact, and `KB.subChain?_sound` says the
search only ever returns chains that pass the check.
-/

namespace Wikidata
namespace KB

/-! ### The facts a knowledge base derives but does not assert -/

/-- The `subclass of` statements that are derivable in `kb` but not asserted by it
(trivial statements `a ⊑ a` are not reported). -/
def newSubL (kb : KB) : List (Qid × Qid) :=
  (kb.items.flatMap fun a => (kb.superclassesOfL a).map fun b => (a, b)).filter
    fun p => (p.1 != p.2) && !kb.sub.contains p

/-- The `instance of` statements that are derivable in `kb` but not asserted by it. -/
def newInstL (kb : KB) : List (Qid × Qid) :=
  (kb.items.flatMap fun a => (kb.classesOf a).map fun c => (a, c)).filter
    fun p => !kb.inst.contains p

/-- The knowledge base with every derivable `subclass of` and `instance of`
statement made explicit. -/
def saturate (kb : KB) : KB :=
  { kb with sub := kb.sub ++ kb.newSubL, inst := kb.inst ++ kb.newInstL }

variable {kb : KB}

theorem mem_newSubL {p : Qid × Qid} :
    p ∈ kb.newSubL ↔
      (p.1 ∈ kb.items ∧ p.2 ∈ kb.items ∧ kb.isSubclassOf p.1 p.2 = true) ∧
        p.1 ≠ p.2 ∧ p ∉ kb.sub := by
  obtain ⟨a, b⟩ := p
  simp only [newSubL, List.mem_filter, List.mem_flatMap, List.mem_map, superclassesOfL,
    Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, hx, y, hy, hxy, rfl⟩, hne, hns⟩
    subst hxy
    exact ⟨⟨hx, hy.1, hy.2⟩, hne, by simpa using hns⟩
  · rintro ⟨⟨ha, hb, hsub⟩, hne, hns⟩
    exact ⟨⟨a, ha, b, ⟨hb, hsub⟩, rfl, rfl⟩, hne, by simpa using hns⟩

theorem mem_newInstL {p : Qid × Qid} :
    p ∈ kb.newInstL ↔
      (p.1 ∈ kb.items ∧ p.2 ∈ kb.items ∧ kb.isInstanceOf p.1 p.2 = true) ∧ p ∉ kb.inst := by
  obtain ⟨a, c⟩ := p
  simp only [newInstL, List.mem_filter, List.mem_flatMap, List.mem_map, classesOf,
    Bool.not_eq_eq_eq_not, Bool.not_true, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, hx, y, hy, hxy, rfl⟩, hns⟩
    subst hxy
    exact ⟨⟨hx, hy.1, hy.2⟩, by simpa using hns⟩
  · rintro ⟨⟨ha, hc, hinst⟩, hns⟩
    exact ⟨⟨a, ha, c, ⟨hc, hinst⟩, rfl, rfl⟩, by simpa using hns⟩

/-- **Soundness of fact construction (P279)**: every newly reported `subclass of`
statement is one the input already derives. -/
theorem newSubL_sound {p : Qid × Qid} (h : p ∈ kb.newSubL) : kb.isSubclassOf p.1 p.2 = true :=
  (mem_newSubL.1 h).1.2.2

/-- **Soundness of fact construction (P31)**: every newly reported `instance of`
statement is one the input already derives. -/
theorem newInstL_sound {p : Qid × Qid} (h : p ∈ kb.newInstL) : kb.isInstanceOf p.1 p.2 = true :=
  (mem_newInstL.1 h).1.2.2

/-- New facts are genuinely new: they are not already asserted. -/
theorem newSubL_not_asserted {p : Qid × Qid} (h : p ∈ kb.newSubL) : p ∉ kb.sub :=
  (mem_newSubL.1 h).2.2

theorem newInstL_not_asserted {p : Qid × Qid} (h : p ∈ kb.newInstL) : p ∉ kb.inst :=
  (mem_newInstL.1 h).2

/-! ### Saturation -/

@[simp] theorem saturate_items : kb.saturate.items = kb.items := rfl
@[simp] theorem saturate_levels : kb.saturate.levels = kb.levels := rfl
@[simp] theorem saturate_disj : kb.saturate.disj = kb.disj := rfl
@[simp] theorem saturate_levelOf (q : Qid) : kb.saturate.levelOf q = kb.levelOf q := rfl

theorem saturate_Sub {a b : Qid} :
    kb.saturate.Sub a b ↔ kb.Sub a b ∨ (a, b) ∈ kb.newSubL := by
  simp [Sub, saturate, List.mem_append]

theorem saturate_Inst {a c : Qid} :
    kb.saturate.Inst a c ↔ kb.Inst a c ∨ (a, c) ∈ kb.newInstL := by
  simp [Inst, saturate, List.mem_append]

/-- Saturation preserves well-formedness. -/
theorem saturate_wellFormed (hwf : kb.wellFormed = true) : kb.saturate.wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [saturate, List.mem_append] at hp
    rcases hp with hp | hp
    · simpa using hwf.1.1 p hp
    · have h := mem_newSubL.1 hp
      simp [saturate, h.1.1, h.1.2.1]
  · intro p hp
    simp only [saturate, List.mem_append] at hp
    rcases hp with hp | hp
    · simpa using hwf.1.2 p hp
    · have h := mem_newInstL.1 hp
      simp [saturate, h.1.1, h.1.2.1]
  · intro p hp
    simpa using hwf.2 p hp

/-- Every `subclass of` step of the saturated base is derivable in the input. -/
theorem reflTransGen_sub_of_saturate (hwf : kb.wellFormed = true) {a b : Qid}
    (h : Relation.ReflTransGen kb.saturate.Sub a b) : Relation.ReflTransGen kb.Sub a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
      rcases saturate_Sub.1 hxy with h | h
      · exact ih.tail h
      · exact ih.trans ((isSubclassOf_iff hwf _ _).1 (newSubL_sound h))

/-- **Saturation is conservative for `subclass of`**: it makes derived statements
explicit without changing what is derivable. -/
theorem saturate_isSubclassOf (hwf : kb.wellFormed = true) (a b : Qid) :
    kb.saturate.isSubclassOf a b = kb.isSubclassOf a b := by
  have hwf' := saturate_wellFormed hwf
  by_cases h : kb.isSubclassOf a b = true
  · have hchain : Relation.ReflTransGen kb.saturate.Sub a b :=
      Relation.ReflTransGen.mono (fun _ _ hxy => saturate_Sub.2 (Or.inl hxy))
        ((isSubclassOf_iff hwf a b).1 h)
    simp [(isSubclassOf_iff hwf' a b).2 hchain, h]
  · simp only [Bool.not_eq_true] at h
    have hne : kb.saturate.isSubclassOf a b ≠ true := by
      intro hc
      have := (isSubclassOf_iff hwf a b).2
        (reflTransGen_sub_of_saturate hwf ((isSubclassOf_iff hwf' a b).1 hc))
      simp [h] at this
    simp [h, Bool.eq_false_iff.2 hne]

/-- **Saturation is conservative for `instance of`**. -/
theorem saturate_isInstanceOf (hwf : kb.wellFormed = true) (a c : Qid) :
    kb.saturate.isInstanceOf a c = kb.isInstanceOf a c := by
  have hwf' := saturate_wellFormed hwf
  by_cases h : kb.isInstanceOf a c = true
  · obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf a c).1 h
    have hdc' : Relation.ReflTransGen kb.saturate.Sub d c :=
      Relation.ReflTransGen.mono (fun _ _ hxy => saturate_Sub.2 (Or.inl hxy)) hdc
    simp [h, (isInstanceOf_iff hwf' a c).2 ⟨d, saturate_Inst.2 (Or.inl hd), hdc'⟩]
  · simp only [Bool.not_eq_true] at h
    have hne : kb.saturate.isInstanceOf a c ≠ true := by
      intro hc
      obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf' a c).1 hc
      have hdc' : Relation.ReflTransGen kb.Sub d c := reflTransGen_sub_of_saturate hwf hdc
      have hyes : kb.isInstanceOf a c = true := by
        rcases saturate_Inst.1 hd with hd' | hd'
        · exact (isInstanceOf_iff hwf a c).2 ⟨d, hd', hdc'⟩
        · have h1 : kb.isInstanceOf a d = true := newInstL_sound hd'
          obtain ⟨e, he, hed⟩ := (isInstanceOf_iff hwf a d).1 h1
          exact (isInstanceOf_iff hwf a c).2 ⟨e, he, hed.trans hdc'⟩
      simp [hyes] at h
    simp [h, Bool.eq_false_iff.2 hne]

/-- Along a chain of `subclass of` statements the level is constant, and it is
positive as soon as the chain is non-trivial. -/
theorem level_of_reflTransGen_sub (hlv : kb.levelsOk = true) {a b : Qid}
    (h : Relation.ReflTransGen kb.Sub a b) :
    kb.levelOf a = kb.levelOf b ∧ (a ≠ b → 0 < kb.levelOf a) := by
  induction h with
  | refl => exact ⟨rfl, fun h => absurd rfl h⟩
  | @tail x y hax hxy ih =>
      have hs := level_sub hlv hxy
      refine ⟨ih.1.trans hs.1, fun _ => ?_⟩
      by_cases hx : a = x
      · subst hx; omega
      · have := ih.2 hx; omega

/-- Saturation preserves the level discipline. -/
theorem saturate_levelsOk (hv : kb.valid = true) : kb.saturate.levelsOk = true := by
  have hwf := valid_wellFormed hv
  have hlv := valid_levelsOk hv
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro p hp
    simp only [saturate, List.mem_append] at hp
    rcases hp with hp | hp
    · simpa [saturate_levelOf] using level_inst hlv hp
    · have hmem := mem_newInstL.1 hp
      obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf p.1 p.2).1 hmem.1.2.2
      have h1 : kb.levelOf d = kb.levelOf p.1 + 1 := level_inst hlv hd
      have h2 : kb.levelOf d = kb.levelOf p.2 := (level_of_reflTransGen_sub hlv hdc).1
      simp only [saturate_levelOf]
      omega
  · intro p hp
    simp only [saturate, List.mem_append] at hp
    rcases hp with hp | hp
    · simpa [saturate_levelOf] using level_sub hlv hp
    · have hmem := mem_newSubL.1 hp
      have hchain := (isSubclassOf_iff hwf p.1 p.2).1 hmem.1.2.2
      have key := level_of_reflTransGen_sub hlv hchain
      simp only [saturate_levelOf]
      exact ⟨key.1, key.2 hmem.2.1⟩

/-- Saturation preserves acyclicity. -/
theorem saturate_acyclic (hv : kb.valid = true) : kb.saturate.acyclic = true := by
  have hwf := valid_wellFormed hv
  have hac := valid_acyclic hv
  simp only [acyclic, List.all_eq_true, saturate_items] at hac ⊢
  intro a ha b hb
  simpa [saturate_isSubclassOf hwf] using hac a ha b hb

/-- Saturation preserves disjointness. -/
theorem saturate_disjointOk (hv : kb.valid = true) : kb.saturate.disjointOk = true := by
  have hwf := valid_wellFormed hv
  have hd := valid_disjointOk hv
  simp only [disjointOk, List.all_eq_true, saturate_items, saturate_disj] at hd ⊢
  intro p hp a ha
  simpa [saturate_isInstanceOf hwf] using hd p hp a ha

/-- **Saturation preserves validity**: the constructed knowledge base is again a
legitimate Wikidata ontology. -/
theorem saturate_valid (hv : kb.valid = true) : kb.saturate.valid = true := by
  simp only [valid, Bool.and_eq_true]
  exact ⟨⟨⟨saturate_wellFormed (valid_wellFormed hv), saturate_levelsOk hv⟩,
    saturate_acyclic hv⟩, saturate_disjointOk hv⟩

/-- **Saturation is a fixed point for `subclass of`**: a second pass of the tool
finds nothing new. -/
theorem newSubL_saturate (hwf : kb.wellFormed = true) : kb.saturate.newSubL = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  have h := mem_newSubL.1 hp
  refine h.2.2 ?_
  have hsub : kb.isSubclassOf p.1 p.2 = true := by
    simpa [saturate_isSubclassOf hwf] using h.1.2.2
  have hor : p ∈ kb.sub ∨ p ∈ kb.newSubL := by
    by_cases hmem : p ∈ kb.sub
    · exact Or.inl hmem
    · exact Or.inr (mem_newSubL.2 ⟨⟨by simpa using h.1.1, by simpa using h.1.2.1, hsub⟩,
        h.2.1, hmem⟩)
  simpa [saturate, List.mem_append] using hor

/-- **Saturation is a fixed point for `instance of`**. -/
theorem newInstL_saturate (hwf : kb.wellFormed = true) : kb.saturate.newInstL = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  have h := mem_newInstL.1 hp
  refine h.2 ?_
  have hinst : kb.isInstanceOf p.1 p.2 = true := by
    simpa [saturate_isInstanceOf hwf] using h.1.2.2
  have hor : p ∈ kb.inst ∨ p ∈ kb.newInstL := by
    by_cases hmem : p ∈ kb.inst
    · exact Or.inl hmem
    · exact Or.inr (mem_newInstL.2 ⟨⟨by simpa using h.1.1, by simpa using h.1.2.1, hinst⟩, hmem⟩)
  simpa [saturate, List.mem_append] using hor

/-- The saturated base entails the original one (and, being conservative, nothing
more). -/
theorem saturate_entails (hwf : kb.wellFormed = true) : kb.saturate.Entails kb = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [saturate_isSubclassOf hwf]
    exact (isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single hp)
  · rw [saturate_isInstanceOf hwf]
    exact isInstanceOf_of_inst hp

/-! ### Certified justifications

A chain `a = c₀, c₁, …, cₙ = b` of asserted P279 statements explains why `a` is a
subclass of `b`. -/

/-- Checks that `cs` is a chain of asserted `subclass of` statements from `a` to `b`. -/
def checkSubChain (kb : KB) : Qid → List Qid → Qid → Bool
  | a, [], b => a == b
  | a, c :: cs, b => kb.sub.contains (a, c) && kb.checkSubChain c cs b

/-- **Certified explanations**: a chain that passes the check witnesses a derived
`subclass of` statement. -/
theorem checkSubChain_sound (kb : KB) :
    ∀ (a : Qid) (cs : List Qid) (b : Qid), kb.checkSubChain a cs b = true →
      Relation.ReflTransGen kb.Sub a b
  | a, [], b, h => by
      simp only [checkSubChain, beq_iff_eq] at h
      exact h ▸ Relation.ReflTransGen.refl
  | a, c :: cs, b, h => by
      simp only [checkSubChain, Bool.and_eq_true, List.contains_iff_mem] at h
      exact Relation.ReflTransGen.head (show kb.Sub a c from h.1)
        (checkSubChain_sound kb c cs b h.2)

/-- Searches for a chain of asserted `subclass of` statements from `a` to `b`;
`fuel` bounds the length of the chain. -/
def subChain? (kb : KB) : ℕ → Qid → Qid → Option (List Qid)
  | 0, a, b => if a == b then some [] else none
  | n + 1, a, b =>
      if a == b then some []
      else (kb.supersL a).findSome? fun c => (kb.subChain? n c b).map fun cs => c :: cs

/-- **The search only returns genuine explanations.** -/
theorem subChain?_sound (kb : KB) :
    ∀ (n : ℕ) (a b : Qid) (cs : List Qid), kb.subChain? n a b = some cs →
      kb.checkSubChain a cs b = true
  | 0, a, b, cs, h => by
      simp only [subChain?] at h
      split at h
      · rename_i hab
        simp only [Option.some.injEq] at h
        subst h
        simpa [checkSubChain] using hab
      · exact absurd h (by simp)
  | n + 1, a, b, cs, h => by
      simp only [subChain?] at h
      split at h
      · rename_i hab
        simp only [Option.some.injEq] at h
        subst h
        simpa [checkSubChain] using hab
      · obtain ⟨l₁, c, l₂, hsplit, hfc, -⟩ := List.findSome?_eq_some_iff.1 h
        obtain ⟨cs', hcs', rfl⟩ := Option.map_eq_some_iff.1 hfc
        have hmem : c ∈ kb.supersL a := by
          rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
        have hsub : (a, c) ∈ kb.sub := by
          simpa [supersL, List.mem_map, List.mem_filter] using hmem
        simp only [checkSubChain, Bool.and_eq_true, List.contains_iff_mem]
        exact ⟨hsub, subChain?_sound kb n c b cs' hcs'⟩

/-- The chain returned by the search, if any, is a certified derivation. -/
theorem subChain?_derives (kb : KB) {n : ℕ} {a b : Qid} {cs : List Qid}
    (h : kb.subChain? n a b = some cs) : Relation.ReflTransGen kb.Sub a b :=
  checkSubChain_sound kb a cs b (subChain?_sound kb n a b cs h)

/-- A convenient default: search for an explanation using as much fuel as there are
items. -/
def explainSubclass (kb : KB) (a b : Qid) : Option (List Qid) :=
  kb.subChain? kb.items.length a b

theorem explainSubclass_derives {a b : Qid} {cs : List Qid}
    (h : kb.explainSubclass a b = some cs) : Relation.ReflTransGen kb.Sub a b :=
  subChain?_derives kb h

end KB
end Wikidata
