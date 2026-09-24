import RequestProject.Engine
import RequestProject.PropertyEngine

/-!
# Property paths: the query language of the ontology

Queries against Wikidata are written with *property paths*: `wdt:P31/wdt:P279*`
("instance of, then any number of subclass steps"), `^wdt:P361` (the inverse of
`part of`), alternatives, and so on.  This file formalises that little language
and its evaluation.

* `Wikidata.PathExpr` — path expressions: the empty path, an atomic property, the
  inverse, composition, alternation and the reflexive–transitive closure.
* `Wikidata.PathExpr.Eval` — their semantics over an arbitrary labelled relation.
* `Wikidata.PathExpr.Eqv` — semantic equivalence of path expressions, together
  with the laws of the *algebra of paths*: composition is associative with the
  empty path as unit, alternation is a commutative idempotent semigroup,
  composition distributes over alternation, inversion is an involutive
  anti-automorphism, and the closure satisfies its unfolding law, is idempotent
  and commutes with inversion.
* `Wikidata.PathExpr.evalF` — the **executable** evaluation of a path expression
  over a finite labelled graph, returning the finite set of answers, and
  `Wikidata.PathExpr.mem_evalF_iff`, which certifies it: the computed answer set
  is exactly the semantics.

The point of it all is `Wikidata.KB.evalF_instanceOf`: over a knowledge base, the
Wikidata idiom `wdt:P31/wdt:P279*` computes exactly the derived `instance of`
relation, and `wdt:P279*` computes exactly derived `subclass of`; abstractly,
`Wikidata.PathExpr.eval_p31_star_p279_iff` says the same about the ontology
semantics.  Over the property layer, a property declared transitive answers the
path `p/p*` (`Wikidata.PKB.evalF_trans_atom`).
-/

namespace Wikidata

/-- A property path expression over a type `P` of property identifiers. -/
inductive PathExpr (P : Type*) where
  /-- The empty path: relates every item to itself. -/
  | id : PathExpr P
  /-- A single property step. -/
  | atom (p : P) : PathExpr P
  /-- The inverse path, written `^p` in SPARQL. -/
  | inv (e : PathExpr P) : PathExpr P
  /-- Composition of paths, written `e/f`. -/
  | seq (e f : PathExpr P) : PathExpr P
  /-- Alternation, written `e|f`. -/
  | alt (e f : PathExpr P) : PathExpr P
  /-- The reflexive–transitive closure, written `e*`. -/
  | star (e : PathExpr P) : PathExpr P
deriving DecidableEq, Repr, Inhabited

namespace PathExpr

variable {P : Type*}

/-- The semantics of a path expression over a labelled relation `G`. -/
def Eval {I : Type*} (G : P → I → I → Prop) : PathExpr P → I → I → Prop
  | .id, s, o => s = o
  | .atom p, s, o => G p s o
  | .inv e, s, o => Eval G e o s
  | .seq e f, s, o => ∃ m, Eval G e s m ∧ Eval G f m o
  | .alt e f, s, o => Eval G e s o ∨ Eval G f s o
  | .star e, s, o => Relation.ReflTransGen (Eval G e) s o

@[simp] theorem eval_id {I : Type*} {G : P → I → I → Prop} {s o : I} :
    Eval G .id s o ↔ s = o := Iff.rfl

@[simp] theorem eval_atom {I : Type*} {G : P → I → I → Prop} {p : P} {s o : I} :
    Eval G (.atom p) s o ↔ G p s o := Iff.rfl

@[simp] theorem eval_inv {I : Type*} {G : P → I → I → Prop} {e : PathExpr P} {s o : I} :
    Eval G (.inv e) s o ↔ Eval G e o s := Iff.rfl

@[simp] theorem eval_seq {I : Type*} {G : P → I → I → Prop} {e f : PathExpr P} {s o : I} :
    Eval G (.seq e f) s o ↔ ∃ m, Eval G e s m ∧ Eval G f m o := Iff.rfl

@[simp] theorem eval_alt {I : Type*} {G : P → I → I → Prop} {e f : PathExpr P} {s o : I} :
    Eval G (.alt e f) s o ↔ Eval G e s o ∨ Eval G f s o := Iff.rfl

@[simp] theorem eval_star {I : Type*} {G : P → I → I → Prop} {e : PathExpr P} {s o : I} :
    Eval G (.star e) s o ↔ Relation.ReflTransGen (Eval G e) s o := Iff.rfl

/-! ### The algebra of paths -/

/-- Two path expressions are equivalent when they have the same semantics over
every labelled relation. -/
def Eqv (e f : PathExpr P) : Prop :=
  ∀ (I : Type) (G : P → I → I → Prop) (s o : I), Eval G e s o ↔ Eval G f s o

@[refl] theorem Eqv.refl (e : PathExpr P) : Eqv e e := fun _ _ _ _ => Iff.rfl

theorem Eqv.symm {e f : PathExpr P} (h : Eqv e f) : Eqv f e :=
  fun I G s o => (h I G s o).symm

theorem Eqv.trans {e f g : PathExpr P} (h : Eqv e f) (h' : Eqv f g) : Eqv e g :=
  fun I G s o => (h I G s o).trans (h' I G s o)

/-- Composition is associative. -/
theorem seq_assoc (e f g : PathExpr P) : Eqv (.seq (.seq e f) g) (.seq e (.seq f g)) := by
  intro I G s o
  constructor
  · rintro ⟨m, ⟨n, hn, hnm⟩, hmo⟩; exact ⟨n, hn, m, hnm, hmo⟩
  · rintro ⟨n, hn, m, hnm, hmo⟩; exact ⟨m, ⟨n, hn, hnm⟩, hmo⟩

/-- The empty path is a left unit for composition. -/
theorem id_seq (e : PathExpr P) : Eqv (.seq .id e) e := by
  intro I G s o
  constructor
  · rintro ⟨m, rfl, h⟩; exact h
  · intro h; exact ⟨s, rfl, h⟩

/-- The empty path is a right unit for composition. -/
theorem seq_id (e : PathExpr P) : Eqv (.seq e .id) e := by
  intro I G s o
  constructor
  · rintro ⟨m, h, rfl⟩; exact h
  · intro h; exact ⟨o, h, rfl⟩

/-- Alternation is commutative. -/
theorem alt_comm (e f : PathExpr P) : Eqv (.alt e f) (.alt f e) :=
  fun _ _ _ _ => Or.comm

/-- Alternation is associative. -/
theorem alt_assoc (e f g : PathExpr P) : Eqv (.alt (.alt e f) g) (.alt e (.alt f g)) :=
  fun _ _ _ _ => or_assoc

/-- Alternation is idempotent. -/
theorem alt_self (e : PathExpr P) : Eqv (.alt e e) e := fun _ _ _ _ => or_self_iff

/-- Composition distributes over alternation on the left. -/
theorem seq_alt (e f g : PathExpr P) :
    Eqv (.seq e (.alt f g)) (.alt (.seq e f) (.seq e g)) := by
  intro I G s o
  constructor
  · rintro ⟨m, hm, hf | hg⟩
    · exact Or.inl ⟨m, hm, hf⟩
    · exact Or.inr ⟨m, hm, hg⟩
  · rintro (⟨m, hm, hf⟩ | ⟨m, hm, hg⟩)
    · exact ⟨m, hm, Or.inl hf⟩
    · exact ⟨m, hm, Or.inr hg⟩

/-- Composition distributes over alternation on the right. -/
theorem alt_seq (e f g : PathExpr P) :
    Eqv (.seq (.alt e f) g) (.alt (.seq e g) (.seq f g)) := by
  intro I G s o
  constructor
  · rintro ⟨m, he | hf, hm⟩
    · exact Or.inl ⟨m, he, hm⟩
    · exact Or.inr ⟨m, hf, hm⟩
  · rintro (⟨m, he, hm⟩ | ⟨m, hf, hm⟩)
    · exact ⟨m, Or.inl he, hm⟩
    · exact ⟨m, Or.inr hf, hm⟩

/-- Inversion is involutive. -/
theorem inv_inv (e : PathExpr P) : Eqv (.inv (.inv e)) e := fun _ _ _ _ => Iff.rfl

/-- The inverse of the empty path is the empty path. -/
theorem inv_id : Eqv (P := P) (.inv .id) .id := fun _ _ _ _ => eq_comm

/-- Inversion reverses composition. -/
theorem inv_seq (e f : PathExpr P) : Eqv (.inv (.seq e f)) (.seq (.inv f) (.inv e)) := by
  intro I G s o
  constructor
  · rintro ⟨m, hm, hmo⟩; exact ⟨m, hmo, hm⟩
  · rintro ⟨m, hm, hmo⟩; exact ⟨m, hmo, hm⟩

/-- Inversion commutes with alternation. -/
theorem inv_alt (e f : PathExpr P) : Eqv (.inv (.alt e f)) (.alt (.inv e) (.inv f)) :=
  fun _ _ _ _ => Iff.rfl

/-- Inversion commutes with the closure. -/
theorem inv_star (e : PathExpr P) : Eqv (.inv (.star e)) (.star (.inv e)) := by
  intro I G s o
  simp only [eval_inv, eval_star]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head hbc ih
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head hbc ih

/-- The closure of the empty path is the empty path. -/
theorem star_id : Eqv (P := P) (.star .id) .id := by
  intro I G s o
  simp only [eval_star, eval_id]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans hbc
  · rintro rfl; exact Relation.ReflTransGen.refl

/-- The unfolding law of the closure: `e* = ε | e/e*`. -/
theorem star_unfold (e : PathExpr P) :
    Eqv (.star e) (.alt .id (.seq e (.star e))) := by
  intro I G s o
  simp only [eval_star, eval_alt, eval_id, eval_seq]
  constructor
  · intro h
    rcases h.cases_head with rfl | ⟨m, hm, hmo⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨m, hm, hmo⟩
  · rintro (rfl | ⟨m, hm, hmo⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hm hmo

/-- The closure absorbs a single step: `e/e* ` is contained in `e*`. -/
theorem seq_star_le (e : PathExpr P) (I : Type) (G : P → I → I → Prop) (s o : I)
    (h : Eval G (.seq e (.star e)) s o) : Eval G (.star e) s o := by
  obtain ⟨m, hm, hmo⟩ := h
  exact Relation.ReflTransGen.head hm hmo

/-- The closure is idempotent. -/
theorem star_star (e : PathExpr P) : Eqv (.star (.star e)) (.star e) := by
  intro I G s o
  simp only [eval_star]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.trans hbc
  · intro h; exact Relation.ReflTransGen.single h

/-- Composing the closure with itself gives the closure. -/
theorem star_seq_star (e : PathExpr P) : Eqv (.seq (.star e) (.star e)) (.star e) := by
  intro I G s o
  simp only [eval_seq, eval_star]
  constructor
  · rintro ⟨m, hm, hmo⟩; exact hm.trans hmo
  · intro h; exact ⟨s, Relation.ReflTransGen.refl, h⟩

/-- The semantics is monotone in the underlying relation. -/
theorem eval_mono {I : Type*} {G H : P → I → I → Prop} (hGH : ∀ p s o, G p s o → H p s o)
    (e : PathExpr P) {s o : I} (h : Eval G e s o) : Eval H e s o := by
  induction e generalizing s o with
  | id => exact h
  | atom p => exact hGH p s o h
  | inv e ih => exact ih h
  | seq e f ihe ihf => obtain ⟨m, hm, hmo⟩ := h; exact ⟨m, ihe hm, ihf hmo⟩
  | alt e f ihe ihf => exact h.imp ihe ihf
  | star e ih => exact h.mono (fun _ _ hxy => ih hxy)

/-! ### Executable evaluation over a finite labelled graph -/

section Exec

variable {P : Type*} (all : Finset Qid) (step : P → Qid → Finset Qid)

/-- The executable evaluation of a path expression: the finite set of answers to
the query, computed from the node set `all` and the one-step function `step`. -/
def evalF : PathExpr P → Qid → Finset Qid
  | .id, s => if s ∈ all then {s} else ∅
  | .atom p, s => step p s
  | .inv e, s => all.filter (fun x => s ∈ evalF e x)
  | .seq e f, s => (evalF e s).biUnion (fun m => evalF f m)
  | .alt e f, s => evalF e s ∪ evalF f s
  | .star e, s => if s ∈ all then Reach.reach (fun x => evalF e x) all s else ∅

/-- The relation read off the one-step function. -/
def stepRel (p : P) (s o : Qid) : Prop := o ∈ step p s

variable (hsub : ∀ p x, step p x ⊆ all) (hempty : ∀ p x, x ∉ all → step p x = ∅)


include hsub in
/-- Every answer is a node of the graph. -/
theorem evalF_subset (e : PathExpr P) (s : Qid) : evalF all step e s ⊆ all := by
  induction e generalizing s with
  | id => by_cases hs : s ∈ all <;> simp [evalF, hs]
  | atom p => exact hsub p s
  | inv e _ => intro x hx; exact (Finset.mem_filter.1 hx).1
  | seq e f _ ihf =>
    intro x hx
    obtain ⟨m, _, hm⟩ := Finset.mem_biUnion.1 hx
    exact ihf m hm
  | alt e f ihe ihf =>
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact ihe s h
    · exact ihf s h
  | star e ih =>
    intro x hx
    by_cases hs : s ∈ all
    · simp only [evalF, hs, if_true] at hx
      exact Reach.iter_subset_all _ (fun y => ih y) hs _ hx
    · simp [evalF, hs] at hx

include hsub hempty in
/-- A node outside the graph has no answers. -/
theorem evalF_eq_empty (e : PathExpr P) {s : Qid} (hs : s ∉ all) : evalF all step e s = ∅ := by
  induction e generalizing s with
  | id => simp [evalF, hs]
  | atom p => exact hempty p s hs
  | inv e ih =>
    refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨hxall, hmem⟩ := Finset.mem_filter.1 hx
    exact hs (evalF_subset all step hsub e x hmem)
  | seq e f ihe _ =>
    refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨m, hm, _⟩ := Finset.mem_biUnion.1 hx
    simp [ihe hs] at hm
  | alt e f ihe ihf => simp [evalF, ihe hs, ihf hs]
  | star e _ => simp [evalF, hs]

include hsub hempty in
/-- Along a path, one endpoint is a node of the graph exactly when the other is. -/
theorem mem_all_iff_of_eval {e : PathExpr P} {s o : Qid}
    (h : Eval (stepRel step) e s o) : s ∈ all ↔ o ∈ all := by
  induction e generalizing s o with
  | id => cases h; rfl
  | atom p =>
    constructor
    · intro _; exact hsub p s h
    · intro _
      by_contra hs
      simp [stepRel, hempty p s hs] at h
  | inv e ih => exact (ih h).symm
  | seq e f ihe ihf =>
    obtain ⟨m, hm, hmo⟩ := h
    exact (ihe hm).trans (ihf hmo)
  | alt e f ihe ihf =>
    rcases h with h | h
    · exact ihe h
    · exact ihf h
  | star e ih =>
    induction h with
    | refl => rfl
    | tail _ hbc ihc => exact ihc.trans (ih hbc)

include hsub hempty in
/-- **The evaluation of path expressions is certified**: the computed answer set
is exactly the semantics of the path expression over the graph. -/
theorem mem_evalF_iff (e : PathExpr P) {s : Qid} (hs : s ∈ all) (o : Qid) :
    o ∈ evalF all step e s ↔ Eval (stepRel step) e s o := by
  induction e generalizing s o with
  | id => simp [evalF, hs, eq_comm]
  | atom p => simp [evalF, stepRel]
  | inv e ih =>
    simp only [evalF, Finset.mem_filter, eval_inv]
    constructor
    · rintro ⟨ho, hmem⟩; exact (ih ho s).1 hmem
    · intro h
      have ho : o ∈ all := ((mem_all_iff_of_eval all step hsub hempty h).2 hs)
      exact ⟨ho, (ih ho s).2 h⟩
  | seq e f ihe ihf =>
    simp only [evalF, Finset.mem_biUnion, eval_seq]
    constructor
    · rintro ⟨m, hm, hmo⟩
      have hmall : m ∈ all := evalF_subset all step hsub e s hm
      exact ⟨m, (ihe hs m).1 hm, (ihf hmall o).1 hmo⟩
    · rintro ⟨m, hm, hmo⟩
      have hmall : m ∈ all := (mem_all_iff_of_eval all step hsub hempty hm).1 hs
      exact ⟨m, (ihe hs m).2 hm, (ihf hmall o).2 hmo⟩
  | alt e f ihe ihf => simp [evalF, ihe hs, ihf hs]
  | star e ih =>
    simp only [evalF, hs, if_true, eval_star]
    rw [Reach.mem_reach_iff_of_closed _ (fun y => evalF_subset all step hsub e y)
      (fun y hy => evalF_eq_empty all step hsub hempty e hy)]
    constructor
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ihb =>
        have hb : b ∈ all := by
          cases hab with
          | refl => exact hs
          | tail _ hstep => exact evalF_subset all step hsub e _ hstep
        exact ihb.tail ((ih hb c).1 hbc)
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ihb =>
        have hb : b ∈ all :=
          (mem_all_iff_of_eval all step hsub hempty (e := .star e) hab).1 hs
        exact ihb.tail ((ih hb c).2 hbc)

end Exec

end PathExpr

/-! ### The ontology paths `wdt:P279*` and `wdt:P31/wdt:P279*` -/

/-- The two structural properties of the ontology layer, as path atoms. -/
inductive Link where
  /-- `instance of` (P31). -/
  | p31 : Link
  /-- `subclass of` (P279). -/
  | p279 : Link
deriving DecidableEq, Repr, Inhabited

namespace Ontology

variable {I : Type*} (O : Ontology I)

/-- The labelled relation of an ontology: the direct P31 and P279 statements. -/
def linkRel : Link → I → I → Prop
  | .p31 => O.P31
  | .p279 => O.P279

/-- `wdt:P279*` is derived `subclass of`. -/
theorem eval_star_p279_iff {a b : I} :
    PathExpr.Eval O.linkRel (.star (.atom .p279)) a b ↔ O.SubclassOf a b := Iff.rfl

/-- **`wdt:P31/wdt:P279*` is derived `instance of`** — the Wikidata query idiom is
exactly the inheritance rule of the ontology. -/
theorem eval_p31_star_p279_iff {a c : I} :
    PathExpr.Eval O.linkRel (.seq (.atom .p31) (.star (.atom .p279))) a c ↔ O.InstanceOf a c :=
  Iff.rfl

end Ontology

/-! ### Running the ontology paths on a finite knowledge base -/

namespace KB

variable (kb : KB)

/-- The one-step function of a knowledge base for the two structural properties. -/
def linkStep : Link → Qid → Finset Qid
  | .p31, q => (kb.directClassesL q).toFinset
  | .p279, q => kb.supers q

theorem linkStep_subset (hwf : kb.wellFormed = true) (l : Link) (q : Qid) :
    kb.linkStep l q ⊆ kb.allF := by
  cases l with
  | p31 =>
    intro d hd
    have : kb.Inst q d := mem_directClassesL.1 (by simpa [linkStep] using hd)
    simpa [mem_allF] using (wf_inst hwf this).2
  | p279 => simpa [linkStep] using supers_subset_all hwf q

theorem linkStep_eq_empty (hwf : kb.wellFormed = true) (l : Link) {q : Qid} (hq : q ∉ kb.allF) :
    kb.linkStep l q = ∅ := by
  cases l with
  | p31 =>
    refine Finset.eq_empty_iff_forall_notMem.2 fun d hd => ?_
    have : kb.Inst q d := mem_directClassesL.1 (by simpa [linkStep] using hd)
    exact hq (by simpa [mem_allF] using (wf_inst hwf this).1)
  | p279 => simpa [linkStep] using supers_eq_empty_of_not_mem hwf (by simpa [mem_allF] using hq)

theorem stepRel_p31 {a d : Qid} :
    PathExpr.stepRel kb.linkStep .p31 a d ↔ kb.Inst a d := by
  simp [PathExpr.stepRel, linkStep, mem_directClassesL]

theorem stepRel_p279 {a b : Qid} :
    PathExpr.stepRel kb.linkStep .p279 a b ↔ kb.Sub a b := by
  simp [PathExpr.stepRel, linkStep, mem_supers]

/-- **`wdt:P279*` computes derived `subclass of`.** -/
theorem mem_evalF_star_p279 (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∈ kb.items) (b : Qid) :
    b ∈ PathExpr.evalF kb.allF kb.linkStep (.star (.atom .p279)) a ↔
      kb.isSubclassOf a b = true := by
  rw [PathExpr.mem_evalF_iff kb.allF kb.linkStep (kb.linkStep_subset hwf)
    (fun l q hq => kb.linkStep_eq_empty hwf l hq) _ (by simpa [mem_allF] using ha),
    isSubclassOf_iff hwf]
  simp only [PathExpr.eval_star]
  constructor
  · intro h; exact h.mono (fun _ _ hxy => (kb.stepRel_p279).1 hxy)
  · intro h; exact h.mono (fun _ _ hxy => (kb.stepRel_p279).2 hxy)

/-- **`wdt:P31/wdt:P279*` computes derived `instance of`** — the standard Wikidata
query idiom, certified against the ontology semantics. -/
theorem mem_evalF_instanceOf (hwf : kb.wellFormed = true) {a : Qid} (ha : a ∈ kb.items) (c : Qid) :
    c ∈ PathExpr.evalF kb.allF kb.linkStep (.seq (.atom .p31) (.star (.atom .p279))) a ↔
      kb.isInstanceOf a c = true := by
  rw [PathExpr.mem_evalF_iff kb.allF kb.linkStep (kb.linkStep_subset hwf)
    (fun l q hq => kb.linkStep_eq_empty hwf l hq) _ (by simpa [mem_allF] using ha),
    isInstanceOf_iff hwf]
  simp only [PathExpr.eval_seq, PathExpr.eval_star, PathExpr.eval_atom]
  constructor
  · rintro ⟨d, hd, hdc⟩
    exact ⟨d, (kb.stepRel_p31).1 hd, hdc.mono (fun _ _ hxy => (kb.stepRel_p279).1 hxy)⟩
  · rintro ⟨d, hd, hdc⟩
    exact ⟨d, (kb.stepRel_p31).2 hd, hdc.mono (fun _ _ hxy => (kb.stepRel_p279).2 hxy)⟩

end KB

/-! ### Paths in the property layer -/

namespace PKB

variable (pkb : PKB)

/-- **A property declared transitive answers the path `p/p*`**: the transitive
query of the engine is the evaluation of that path expression. -/
theorem mem_evalF_seq_star (h : pkb.pWellFormed = true) (p : Pid) {s : Qid}
    (hs : s ∈ pkb.base.items) (o : Qid) :
    o ∈ PathExpr.evalF pkb.base.allF pkb.stepPairs (.seq (.atom p) (.star (.atom p))) s ↔
      pkb.chainB p s o = true := by
  rw [PathExpr.mem_evalF_iff pkb.base.allF pkb.stepPairs
    (fun q x => stepPairs_subset_items h q x)
    (fun q x hx => stepPairs_eq_empty_of_not_mem h (p := q) hx) _
    (by simpa [KB.mem_allF] using hs)]
  simp only [PathExpr.eval_seq, PathExpr.eval_star, PathExpr.eval_atom, chainB,
    decide_eq_true_eq, PathExpr.stepRel]
  constructor
  · rintro ⟨m, hm, hmo⟩
    exact ⟨m, hm, (mem_reach_stepPairs_iff h p m o).2 hmo⟩
  · rintro ⟨m, hm, hmo⟩
    exact ⟨m, hm, (mem_reach_stepPairs_iff h p m o).1 hmo⟩

/-- Hence, for a property declared transitive, the path `p/p*` computes exactly
what the engine's statement query computes. -/
theorem mem_evalF_relatedB (h : pkb.pWellFormed = true) {p : Pid} (hp : pkb.isTransB p = true)
    {s : Qid} (hs : s ∈ pkb.base.items) (o : Qid) :
    o ∈ PathExpr.evalF pkb.base.allF pkb.stepPairs (.seq (.atom p) (.star (.atom p))) s ↔
      pkb.relatedB p s o = true := by
  rw [pkb.mem_evalF_seq_star h p hs o, relatedB, if_pos hp]

end PKB

/-! ### A worked query

Douglas Adams (Q42) is an instance of *human* (Q5), which is a subclass of
*person* (Q215627), which is a subclass of *entity* (Q35120). -/

namespace PathExample

open Wikidata PathExpr

/-- A tiny fragment to run queries against. -/
def kbq : KB where
  name := "query fragment"
  items := [.wd "Q42", .wd "Q5", .wd "Q215627", .wd "Q35120"]
  levels := [(.wd "Q42", 0), (.wd "Q5", 1), (.wd "Q215627", 1), (.wd "Q35120", 1)]
  sub := [(.wd "Q5", .wd "Q215627"), (.wd "Q215627", .wd "Q35120")]
  inst := [(.wd "Q42", .wd "Q5")]

theorem kbq_valid : kbq.valid = true := by decide

/-- The query `wdt:P31/wdt:P279*` at Douglas Adams returns human, person and
entity — exactly the classes the engine derives. -/
theorem query_instanceOf :
    evalF kbq.allF kbq.linkStep (.seq (.atom .p31) (.star (.atom .p279))) (.wd "Q42") =
      {Qid.wd "Q5", Qid.wd "Q215627", Qid.wd "Q35120"} := by decide

/-- The inverse query `^wdt:P279` at *entity* returns its direct subclasses. -/
theorem query_inv_p279 :
    evalF kbq.allF kbq.linkStep (.inv (.atom .p279)) (.wd "Q35120") = {Qid.wd "Q215627"} := by
  decide

/-- The reflexive–transitive query `wdt:P279*` at *human* returns human itself and
its superclasses. -/
theorem query_star_p279 :
    evalF kbq.allF kbq.linkStep (.star (.atom .p279)) (.wd "Q5") =
      {Qid.wd "Q5", Qid.wd "Q215627", Qid.wd "Q35120"} := by decide

/-- Douglas Adams is not returned by `wdt:P279*` at *human*: he is an instance,
not a subclass. -/
theorem query_star_p279_not_instance :
    Qid.wd "Q42" ∉ evalF kbq.allF kbq.linkStep (.star (.atom .p279)) (.wd "Q5") := by decide

/-- The general certification, specialised to this fragment: the idiom computes
the derived `instance of` relation. -/
theorem query_agrees (c : Qid) :
    c ∈ evalF kbq.allF kbq.linkStep (.seq (.atom .p31) (.star (.atom .p279))) (.wd "Q42") ↔
      kbq.isInstanceOf (.wd "Q42") c = true :=
  kbq.mem_evalF_instanceOf (KB.valid_wellFormed kbq_valid) (by decide) c

end PathExample

end Wikidata
