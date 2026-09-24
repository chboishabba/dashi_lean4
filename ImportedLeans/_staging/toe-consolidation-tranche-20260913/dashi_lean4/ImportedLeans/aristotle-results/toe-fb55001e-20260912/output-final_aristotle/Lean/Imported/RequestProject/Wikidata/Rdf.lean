import RequestProject.Wikidata.Layers

/-!
# The RDF layers

Two further layers sit below the statement layers of `Layers.lean`, and they must
not be conflated:

* the **reified** layer (`reify`), which encodes every statement together with its
  rank through a statement node — it is *lossless*: a decoder recovers the
  statement list exactly (`dereify_reify`), hence `reify` is injective on
  statement lists (`reify_injective`);
* the **direct** layer (`directTriples`), which flattens only the truthy
  statements into subject/predicate/object triples — it is deliberately *lossy*:
  it forgets rank (`direct_layer_forgets_rank`).

On the direct layer we give an entailment relation with the two RDFS-style class
rules (transitivity of `P279`, and closing `P31` under `P279`) and prove it
*exact*, not merely sound:

* `entails_subclass_iff` — an entailed `P279` triple is exactly a nontrivial
  subclass path;
* `entails_instance_iff` — an entailed `P31` triple is exactly an instance fact;
* `entails_inert` — entailment invents nothing outside those two predicates;
* `isSubclassOf_iff_entails`, `isInstanceOf_iff_entails` — the executable
  checkers of `Core.lean` agree with RDF entailment.

Keeping the four guarantees (losslessness, soundness, `P279` exactness, `P31`
exactness) separate is the point: each is a different statement about a different
layer.
-/

namespace Wikidata

namespace Rdf

/-- A term of the RDF encoding. -/
inductive Term
  | item (q : Qid)
  | prop (p : Pid)
  | node (n : Nat)
  | rankTerm (r : Rank)
  | key (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- An RDF triple. -/
structure Triple where
  subj : Term
  pred : Term
  obj : Term
  deriving DecidableEq, Repr, Inhabited

/-- The predicate linking an item to one of its statement nodes. -/
def claimKey : Term := Term.key "claim"

/-- The predicate recording the rank of a statement node. -/
def rankKey : Term := Term.key "rank"

/-! ## The reified layer -/

/-- The three triples encoding one statement at statement node `n`. -/
def reifyStatement (n : Nat) (st : Statement) : List Triple :=
  [⟨Term.item st.subject, claimKey, Term.node n⟩,
   ⟨Term.node n, Term.prop st.property, Term.item st.value⟩,
   ⟨Term.node n, rankKey, Term.rankTerm st.rank⟩]

/-- Reification of a statement list, numbering statement nodes from `n`. -/
def reifyFrom : Nat → List Statement → List Triple
  | _, [] => []
  | n, st :: rest => reifyStatement n st ++ reifyFrom (n + 1) rest

/-- The reified RDF layer of a knowledge base. -/
def reify (kb : KB) : List Triple := reifyFrom 0 kb.statements

/-- The decoder for the reified layer. -/
def dereify : List Triple → List Statement
  | ⟨Term.item s, Term.key "claim", Term.node _⟩ ::
      ⟨Term.node _, Term.prop p, Term.item v⟩ ::
      ⟨Term.node _, Term.key "rank", Term.rankTerm r⟩ :: rest =>
    ⟨s, p, v, r⟩ :: dereify rest
  | _ => []

theorem dereify_reifyFrom (n : Nat) (sts : List Statement) :
    dereify (reifyFrom n sts) = sts := by
  induction sts generalizing n with
  | nil => rfl
  | cons st rest ih =>
      show dereify (reifyStatement n st ++ reifyFrom (n + 1) rest) = st :: rest
      cases st
      simp only [reifyStatement, List.cons_append, List.nil_append, claimKey, rankKey, dereify, ih]

/-- **Losslessness of the reified layer**: reification is exactly invertible. -/
theorem dereify_reify (kb : KB) : dereify (reify kb) = kb.statements :=
  dereify_reifyFrom 0 kb.statements

/-- Reification is injective on statement lists. -/
theorem reify_injective {kb₁ kb₂ : KB} (h : reify kb₁ = reify kb₂) :
    kb₁.statements = kb₂.statements := by
  rw [← dereify_reify kb₁, ← dereify_reify kb₂, h]

/-- Every statement is present in the reified layer, rank included. -/
theorem reifyFrom_triples (n : Nat) {sts : List Statement} {st : Statement} (h : st ∈ sts) :
    ∃ m, ⟨Term.item st.subject, claimKey, Term.node m⟩ ∈ reifyFrom n sts ∧
      (⟨Term.node m, Term.prop st.property, Term.item st.value⟩ : Triple) ∈ reifyFrom n sts ∧
      (⟨Term.node m, rankKey, Term.rankTerm st.rank⟩ : Triple) ∈ reifyFrom n sts := by
  induction sts generalizing n with
  | nil => exact absurd h (by simp)
  | cons st' rest ih =>
      rcases List.mem_cons.1 h with rfl | hrest
      · exact ⟨n, by simp [reifyFrom, reifyStatement], by simp [reifyFrom, reifyStatement],
          by simp [reifyFrom, reifyStatement]⟩
      · obtain ⟨m, h1, h2, h3⟩ := ih (n + 1) hrest
        exact ⟨m, by simp [reifyFrom, h1], by simp [reifyFrom, h2], by simp [reifyFrom, h3]⟩

theorem mem_reify (kb : KB) {st : Statement} (h : st ∈ kb.statements) :
    ∃ m, ⟨Term.item st.subject, claimKey, Term.node m⟩ ∈ reify kb ∧
      (⟨Term.node m, Term.prop st.property, Term.item st.value⟩ : Triple) ∈ reify kb ∧
      (⟨Term.node m, rankKey, Term.rankTerm st.rank⟩ : Triple) ∈ reify kb :=
  reifyFrom_triples 0 h

/-! ## The direct layer -/

/-- The direct RDF layer: the truthy statements, flattened. -/
def directTriples (kb : KB) : List Triple :=
  (kb.statements.filter (IsTruthy kb)).map
    (fun st => ⟨Term.item st.subject, Term.prop st.property, Term.item st.value⟩)

/-- The direct layer already lives at the truthy statement layer. -/
theorem directTriples_truthyLayer (kb : KB) :
    directTriples (truthyLayer kb) = directTriples kb := by
  have hf : IsTruthy (truthyLayer kb) = IsTruthy kb := funext (isTruthy_truthyLayer kb)
  simp only [directTriples, hf]
  congr 1
  show (kb.statements.filter (IsTruthy kb)).filter (IsTruthy kb) = _
  rw [List.filter_filter]
  simp

theorem mem_directTriples_iff (kb : KB) (a b : Qid) (p : Pid) :
    (⟨Term.item a, Term.prop p, Term.item b⟩ : Triple) ∈ directTriples kb ↔
      ∃ st ∈ kb.statements, IsTruthy kb st = true ∧
        st.subject = a ∧ st.property = p ∧ st.value = b := by
  simp only [directTriples, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨st, ⟨hst, htr⟩, heq⟩
    injection heq with h1 h2 h3
    injection h1 with hs
    injection h2 with hp
    injection h3 with hv
    exact ⟨st, hst, htr, hs, hp, hv⟩
  · rintro ⟨st, hst, htr, rfl, rfl, rfl⟩
    exact ⟨st, ⟨hst, htr⟩, rfl⟩

/-- Direct `P279` triples are exactly the subclass edges. -/
theorem mem_directTriples_p279_iff (kb : KB) (a b : Qid) :
    (⟨Term.item a, Term.prop P279, Term.item b⟩ : Triple) ∈ directTriples kb ↔
      DirectSubclass kb a b := by
  rw [mem_directTriples_iff]
  simp only [DirectSubclass, subclassEdges, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨st, hst, htr, h1, h2, h3⟩
    exact ⟨st, ⟨hst, h2, htr⟩, by simp [h1, h3]⟩
  · rintro ⟨st, ⟨hst, hp, htr⟩, heq⟩
    injection heq with h1 h2
    exact ⟨st, hst, htr, h1, hp, h2⟩

/-- Direct `P31` triples are exactly the instance edges. -/
theorem mem_directTriples_p31_iff (kb : KB) (x c : Qid) :
    (⟨Term.item x, Term.prop P31, Term.item c⟩ : Triple) ∈ directTriples kb ↔
      (x, c) ∈ instanceEdges kb := by
  rw [mem_directTriples_iff]
  simp only [instanceEdges, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨st, hst, htr, h1, h2, h3⟩
    exact ⟨st, ⟨hst, h2, htr⟩, by simp [h1, h3]⟩
  · rintro ⟨st, ⟨hst, hp, htr⟩, heq⟩
    injection heq with h1 h2
    exact ⟨st, hst, htr, h1, hp, h2⟩

/-- The direct layer forgets rank: two knowledge bases with the same direct
layer can have different reified layers. -/
theorem direct_layer_forgets_rank :
    ∃ kb₁ kb₂ : KB, directTriples kb₁ = directTriples kb₂ ∧ reify kb₁ ≠ reify kb₂ := by
  refine ⟨⟨[⟨1⟩, ⟨2⟩], [⟨⟨1⟩, P279, ⟨2⟩, Rank.normal⟩]⟩,
    ⟨[⟨1⟩, ⟨2⟩], [⟨⟨1⟩, P279, ⟨2⟩, Rank.preferred⟩]⟩, by decide, by decide⟩

/-! ## Entailment on the direct layer -/

/-- RDFS-style class entailment: the base triples, closed under transitivity of
`P279` and under lifting `P31` along `P279`. -/
inductive Entails (ts : List Triple) : Triple → Prop
  | base {t : Triple} : t ∈ ts → Entails ts t
  | subclassTrans {a b c : Qid} :
      Entails ts ⟨Term.item a, Term.prop P279, Term.item b⟩ →
      Entails ts ⟨Term.item b, Term.prop P279, Term.item c⟩ →
      Entails ts ⟨Term.item a, Term.prop P279, Term.item c⟩
  | instanceSubclass {x c d : Qid} :
      Entails ts ⟨Term.item x, Term.prop P31, Term.item c⟩ →
      Entails ts ⟨Term.item c, Term.prop P279, Term.item d⟩ →
      Entails ts ⟨Term.item x, Term.prop P31, Term.item d⟩

theorem p279_ne_p31 : P279 ≠ P31 := by decide

/-- The intended model of the direct layer of `kb`. -/
def Sat (kb : KB) : Triple → Prop
  | ⟨Term.item a, Term.prop p, Term.item b⟩ =>
      if p = P279 then Relation.TransGen (DirectSubclass kb) a b
      else if p = P31 then InstanceOf kb a b
      else (⟨Term.item a, Term.prop p, Term.item b⟩ : Triple) ∈ directTriples kb
  | t => t ∈ directTriples kb

theorem sat_of_mem {kb : KB} {t : Triple} (h : t ∈ directTriples kb) : Sat kb t := by
  match t with
  | ⟨Term.item a, Term.prop p, Term.item b⟩ =>
      by_cases h279 : p = P279
      · subst h279
        exact by
          simp only [Sat]
          exact Relation.TransGen.single ((mem_directTriples_p279_iff kb a b).1 h)
      · by_cases h31 : p = P31
        · subst h31
          simp only [Sat, if_neg h279]
          exact ⟨b, (mem_directTriples_p31_iff kb a b).1 h, Relation.ReflTransGen.refl⟩
        · simpa only [Sat, if_neg h279, if_neg h31] using h
  | ⟨Term.item _, Term.prop _, Term.prop _⟩ => exact h
  | ⟨Term.item _, Term.prop _, Term.node _⟩ => exact h
  | ⟨Term.item _, Term.prop _, Term.rankTerm _⟩ => exact h
  | ⟨Term.item _, Term.prop _, Term.key _⟩ => exact h
  | ⟨Term.item _, Term.item _, _⟩ => exact h
  | ⟨Term.item _, Term.node _, _⟩ => exact h
  | ⟨Term.item _, Term.rankTerm _, _⟩ => exact h
  | ⟨Term.item _, Term.key _, _⟩ => exact h
  | ⟨Term.prop _, _, _⟩ => exact h
  | ⟨Term.node _, _, _⟩ => exact h
  | ⟨Term.rankTerm _, _, _⟩ => exact h
  | ⟨Term.key _, _, _⟩ => exact h

/-- **Soundness of entailment**: everything entailed by the direct layer holds in
the intended model. -/
theorem entails_sound {kb : KB} {t : Triple} (h : Entails (directTriples kb) t) : Sat kb t := by
  induction h with
  | base hmem => exact sat_of_mem hmem
  | @subclassTrans a b c _ _ ih₁ ih₂ =>
      simp only [Sat] at ih₁ ih₂ ⊢
      exact ih₁.trans ih₂
  | @instanceSubclass x c d _ _ ih₁ ih₂ =>
      simp only [Sat, if_neg p279_ne_p31.symm] at ih₁ ⊢
      simp only [Sat] at ih₂
      exact instanceOf_of_subclassOf ih₁ ih₂.to_reflTransGen

/-- **Exactness of `P279` entailment**. -/
theorem entails_subclass_iff (kb : KB) (a b : Qid) :
    Entails (directTriples kb) ⟨Term.item a, Term.prop P279, Term.item b⟩ ↔
      Relation.TransGen (DirectSubclass kb) a b := by
  constructor
  · intro h
    simpa only [Sat] using entails_sound h
  · intro h
    induction h with
    | single hab => exact Entails.base ((mem_directTriples_p279_iff kb a _).2 hab)
    | tail _ hbc ih =>
        exact Entails.subclassTrans ih (Entails.base ((mem_directTriples_p279_iff kb _ _).2 hbc))

/-- **Exactness of `P31` entailment**. -/
theorem entails_instance_iff (kb : KB) (x c : Qid) :
    Entails (directTriples kb) ⟨Term.item x, Term.prop P31, Term.item c⟩ ↔ InstanceOf kb x c := by
  constructor
  · intro h
    simpa only [Sat, if_neg p279_ne_p31.symm] using entails_sound h
  · rintro ⟨c₀, hc₀, hsub⟩
    have hbase : Entails (directTriples kb) ⟨Term.item x, Term.prop P31, Term.item c₀⟩ :=
      Entails.base ((mem_directTriples_p31_iff kb x c₀).2 hc₀)
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hsub with rfl | htr
    · exact hbase
    · exact Entails.instanceSubclass hbase ((entails_subclass_iff kb c₀ c).2 htr)

/-- Entailment is inert outside the class predicates: no new triple with any
other predicate is produced. -/
theorem entails_inert {kb : KB} {a b : Qid} {p : Pid} (hp279 : p ≠ P279) (hp31 : p ≠ P31)
    (h : Entails (directTriples kb) ⟨Term.item a, Term.prop p, Term.item b⟩) :
    (⟨Term.item a, Term.prop p, Term.item b⟩ : Triple) ∈ directTriples kb := by
  simpa only [Sat, if_neg hp279, if_neg hp31] using entails_sound h

/-! ## Agreement with the executable engine -/

/-- The executable checker for an entailed `P279` triple: at least one real
subclass step, then reflexive-transitive closure. -/
def entailsSubclassOk (kb : KB) (a b : Qid) : Bool :=
  (superclasses kb a).any (fun c => isSubclassOf kb c b)

/-- **Exactness of the entailed-`P279` checker.** -/
theorem entailsSubclassOk_iff (kb : KB) (a b : Qid) :
    entailsSubclassOk kb a b = true ↔
      Entails (directTriples kb) ⟨Term.item a, Term.prop P279, Term.item b⟩ := by
  rw [entails_subclass_iff]
  simp only [entailsSubclassOk, List.any_eq_true, Relation.TransGen.head'_iff,
    isSubclassOf_iff, mem_superclasses_iff]
  rfl

/-- The executable checker for an entailed `P31` triple. -/
def entailsInstanceOk (kb : KB) (x c : Qid) : Bool := isInstanceOf kb x c

theorem entailsInstanceOk_iff (kb : KB) (x c : Qid) :
    entailsInstanceOk kb x c = true ↔
      Entails (directTriples kb) ⟨Term.item x, Term.prop P31, Term.item c⟩ := by
  rw [entailsInstanceOk, isInstanceOf_iff]
  exact (entails_instance_iff kb x c).symm

/-- **The executable subclass checker computes RDF entailment.** -/
theorem isSubclassOf_iff_entails (kb : KB) (a b : Qid) :
    isSubclassOf kb a b = true ↔
      a = b ∨ Entails (directTriples kb) ⟨Term.item a, Term.prop P279, Term.item b⟩ := by
  rw [isSubclassOf_iff, SubclassOf, Relation.reflTransGen_iff_eq_or_transGen]
  exact or_congr eq_comm (entails_subclass_iff kb a b).symm

/-- **The executable instance checker computes RDF entailment.** -/
theorem isInstanceOf_iff_entails (kb : KB) (x c : Qid) :
    isInstanceOf kb x c = true ↔
      Entails (directTriples kb) ⟨Term.item x, Term.prop P31, Term.item c⟩ := by
  rw [isInstanceOf_iff]
  exact (entails_instance_iff kb x c).symm

end Rdf

end Wikidata
