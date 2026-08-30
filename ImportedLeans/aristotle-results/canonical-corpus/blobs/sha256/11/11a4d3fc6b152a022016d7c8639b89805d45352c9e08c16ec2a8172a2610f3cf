import RequestProject.Ranks

/-!
# The RDF rendering of the data model

Wikidata is published as RDF, and the exported graph has two layers.

* The **truthy** layer: for every truthy statement (see `RequestProject.Ranks`) a single
  triple `wd:Q42 wdt:P31 wd:Q5`, using the *direct* property IRI `wdt:`.
* The **full** layer: every statement, whatever its rank, is *reified*.  The subject is
  linked to a fresh **statement node** by the property IRI `p:`, and the node carries the
  value (`ps:`), the rank (`wikibase:rank`) and one triple per qualifier (`pq:`).

This file formalises both layers and their relationship to the claim model.

The results are:

* `Rdf.recoverAt_fullGraph` — the reified layer is **lossless**: the `i`-th statement of
  a claim set can be read back off the exported graph, qualifiers and rank included.
* `Rdf.fullGraph_injective` — hence the export is injective: different claim sets give
  different graphs.
* `Rdf.mem_truthyGraph_iff` — a direct (`wdt:`) triple is in the export exactly when its
  object is one of the values a default query returns, so the truthy layer computes the
  same thing as `Claim.truthyValues`.
* `Rdf.rank_ne_deprecated_of_mem_truthyGraph` — no deprecated statement ever produces a
  direct triple, while `Rdf.mem_fullGraph_of_mem` shows the full layer keeps everything.
* `Rdf.entails_sub_iff` / `Rdf.entails_inst_iff` — the RDFS-style entailment rules on the
  exported ontology graph (reflexivity and transitivity of `wdt:P279`, and `wdt:P31`
  followed by `wdt:P279`) derive exactly the `subclass of` and `instance of` facts that
  the engine of `RequestProject.Engine` computes.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment at the end is a stylised excerpt.
-/

namespace Wikidata
namespace Rdf

open Claim

/-- A term of the exported RDF graph: an entity IRI, one of the four property IRI
namespaces Wikidata uses, a statement node, the rank vocabulary, or a literal. -/
inductive Term where
  /-- An entity IRI, `wd:Q42`. -/
  | ent (q : Qid)
  /-- A direct property IRI, `wdt:P31`. -/
  | truthyProp (p : Pid)
  /-- A statement property IRI, `p:P31`, linking a subject to a statement node. -/
  | stmtProp (p : Pid)
  /-- A statement-value property IRI, `ps:P31`. -/
  | valueProp (p : Pid)
  /-- A qualifier property IRI, `pq:P585`. -/
  | qualProp (p : Pid)
  /-- A statement node, `wds:...`; here identified by a number. -/
  | node (i : Nat)
  /-- The predicate `wikibase:rank`. -/
  | rankProp
  /-- A rank IRI, `wikibase:PreferredRank` and friends. -/
  | rankVal (r : Rank)
  /-- A literal value. -/
  | lit (v : Value)
deriving DecidableEq, Repr, Inhabited

/-- An RDF triple. -/
abbrev Triple := Term × Term × Term

/-- An RDF graph, as a list of triples. -/
abbrev Graph := List Triple

/-- The object term of a statement value: item values become entity IRIs, everything
else becomes a literal. -/
def objOf : Value → Term
  | .item q => .ent q
  | v => .lit v

/-- Reading a value back off an object term. -/
def termValue : Term → Option Value
  | .ent q => some (.item q)
  | .lit v => some v
  | _ => none

@[simp] theorem termValue_objOf (v : Value) : termValue (objOf v) = some v := by
  cases v <;> rfl

theorem objOf_injective : Function.Injective objOf := by
  intro v w h
  have : termValue (objOf v) = termValue (objOf w) := by rw [h]
  simpa using this

/-! ### The export -/

/-- The reification of a single claim at the statement node `i`. -/
def block (c : Claim) (i : Nat) : Graph :=
  (Term.ent c.subject, Term.stmtProp c.pid, Term.node i) ::
  (Term.node i, Term.valueProp c.pid, objOf c.value) ::
  (Term.node i, Term.rankProp, Term.rankVal c.rank) ::
  c.quals.map (fun qv => (Term.node i, Term.qualProp qv.1, objOf qv.2))

/-- The reified export of a claim set, numbering the statement nodes from `n`. -/
def blocksFrom (n : Nat) : Claim.Set → Graph
  | [] => []
  | c :: cs => block c n ++ blocksFrom (n + 1) cs

/-- The **full** layer of the export: every statement, reified. -/
def fullGraph (cs : Claim.Set) : Graph := blocksFrom 0 cs

/-- The **truthy** layer of the export: one direct (`wdt:`) triple per truthy statement. -/
def truthyGraph (cs : Claim.Set) : Graph :=
  (Claim.truthy cs).map (fun c => (Term.ent c.subject, Term.truthyProp c.pid, objOf c.value))

/-- The exported RDF graph of a claim set: the truthy layer on top of the full layer. -/
def graph (cs : Claim.Set) : Graph := fullGraph cs ++ truthyGraph cs

/-! ### Reading the graph back -/

/-- The subject and property of the statement node `i`. -/
def subjPropAt (g : Graph) (i : Nat) : Option (Qid × Pid) :=
  g.findSome? (fun t =>
    match t with
    | (.ent s, .stmtProp p, .node j) => if j = i then some (s, p) else none
    | _ => none)

/-- The value of the statement node `i`. -/
def valueAt (g : Graph) (i : Nat) : Option Value :=
  g.findSome? (fun t =>
    match t with
    | (.node j, .valueProp _, o) => if j = i then termValue o else none
    | _ => none)

/-- The rank of the statement node `i`. -/
def rankAt (g : Graph) (i : Nat) : Option Rank :=
  g.findSome? (fun t =>
    match t with
    | (.node j, .rankProp, .rankVal r) => if j = i then some r else none
    | _ => none)

/-- The qualifiers of the statement node `i`. -/
def qualsAt (g : Graph) (i : Nat) : List (Pid × Value) :=
  g.filterMap (fun t =>
    match t with
    | (.node j, .qualProp p, o) => if j = i then (termValue o).map (fun v => (p, v)) else none
    | _ => none)

/-- The claim reified at the statement node `i`, read back off the graph. -/
def recoverAt (g : Graph) (i : Nat) : Option Claim := do
  let sp ← subjPropAt g i
  let v ← valueAt g i
  let r ← rankAt g i
  pure { subject := sp.1, pid := sp.2, value := v, rank := r, quals := qualsAt g i }

/-! ### The reified layer is lossless -/

@[simp] theorem subjPropAt_block_self (c : Claim) (n : Nat) :
    subjPropAt (block c n) n = some (c.subject, c.pid) := by
  simp [subjPropAt, block]

theorem subjPropAt_block_ne (c : Claim) {n i : Nat} (h : i ≠ n) :
    subjPropAt (block c n) i = none := by
  simp only [subjPropAt, block, List.findSome?_cons, List.findSome?_eq_none_iff,
    if_neg (Ne.symm h)]
  intro x hx
  obtain ⟨qv, -, rfl⟩ := List.mem_map.1 hx
  rfl

@[simp] theorem valueAt_block_self (c : Claim) (n : Nat) :
    valueAt (block c n) n = some c.value := by
  simp [valueAt, block]

theorem valueAt_block_ne (c : Claim) {n i : Nat} (h : i ≠ n) :
    valueAt (block c n) i = none := by
  simp only [valueAt, block, List.findSome?_cons, List.findSome?_eq_none_iff,
    if_neg (Ne.symm h)]
  intro x hx
  obtain ⟨qv, -, rfl⟩ := List.mem_map.1 hx
  rfl

@[simp] theorem rankAt_block_self (c : Claim) (n : Nat) :
    rankAt (block c n) n = some c.rank := by
  simp [rankAt, block]

theorem rankAt_block_ne (c : Claim) {n i : Nat} (h : i ≠ n) :
    rankAt (block c n) i = none := by
  simp only [rankAt, block, List.findSome?_cons, List.findSome?_eq_none_iff,
    if_neg (Ne.symm h)]
  intro x hx
  obtain ⟨qv, -, rfl⟩ := List.mem_map.1 hx
  rfl

@[simp] theorem qualsAt_block_self (c : Claim) (n : Nat) :
    qualsAt (block c n) n = c.quals := by
  simp only [qualsAt, block, List.filterMap_cons, List.filterMap_map, Function.comp_def,
    termValue_objOf]
  simp

theorem qualsAt_block_ne (c : Claim) {n i : Nat} (h : i ≠ n) :
    qualsAt (block c n) i = [] := by
  simp only [qualsAt, block, List.filterMap_cons, List.filterMap_map, Function.comp_def,
    if_neg (Ne.symm h), List.filterMap_eq_nil_iff]
  simp

/-! ### Splitting the lookups along a concatenation -/

theorem subjPropAt_append (g h : Graph) (i : Nat) :
    subjPropAt (g ++ h) i = (subjPropAt g i).or (subjPropAt h i) := List.findSome?_append

theorem valueAt_append (g h : Graph) (i : Nat) :
    valueAt (g ++ h) i = (valueAt g i).or (valueAt h i) := List.findSome?_append

theorem rankAt_append (g h : Graph) (i : Nat) :
    rankAt (g ++ h) i = (rankAt g i).or (rankAt h i) := List.findSome?_append

theorem qualsAt_append (g h : Graph) (i : Nat) :
    qualsAt (g ++ h) i = qualsAt g i ++ qualsAt h i := List.filterMap_append

/-- Every statement node of `blocksFrom n cs` is numbered at least `n`. -/
theorem subjPropAt_blocksFrom_lt {cs : Claim.Set} {n i : Nat} (h : i < n) :
    subjPropAt (blocksFrom n cs) i = none := by
  induction cs generalizing n with
  | nil => rfl
  | cons c t ih =>
      rw [blocksFrom, subjPropAt_append, subjPropAt_block_ne c (Nat.ne_of_lt h),
        ih (n := n + 1) (by omega)]
      rfl

theorem valueAt_blocksFrom_lt {cs : Claim.Set} {n i : Nat} (h : i < n) :
    valueAt (blocksFrom n cs) i = none := by
  induction cs generalizing n with
  | nil => rfl
  | cons c t ih =>
      rw [blocksFrom, valueAt_append, valueAt_block_ne c (Nat.ne_of_lt h),
        ih (n := n + 1) (by omega)]
      rfl

theorem rankAt_blocksFrom_lt {cs : Claim.Set} {n i : Nat} (h : i < n) :
    rankAt (blocksFrom n cs) i = none := by
  induction cs generalizing n with
  | nil => rfl
  | cons c t ih =>
      rw [blocksFrom, rankAt_append, rankAt_block_ne c (Nat.ne_of_lt h),
        ih (n := n + 1) (by omega)]
      rfl

theorem qualsAt_blocksFrom_lt {cs : Claim.Set} {n i : Nat} (h : i < n) :
    qualsAt (blocksFrom n cs) i = [] := by
  induction cs generalizing n with
  | nil => rfl
  | cons c t ih =>
      rw [blocksFrom, qualsAt_append, qualsAt_block_ne c (Nat.ne_of_lt h),
        ih (n := n + 1) (by omega)]
      rfl

/-- There are as many statement nodes as there are statements. -/
theorem subjPropAt_blocksFrom_ge {cs : Claim.Set} {n j : Nat} (h : n + cs.length ≤ j) :
    subjPropAt (blocksFrom n cs) j = none := by
  induction cs generalizing n with
  | nil => rfl
  | cons c t ih =>
      simp only [List.length_cons] at h
      rw [blocksFrom, subjPropAt_append, subjPropAt_block_ne c (by omega),
        ih (n := n + 1) (by omega)]
      rfl

/-! ### The reified layer is lossless -/

theorem recoverAt_block_append (c : Claim) (n : Nat) (g : Graph) (hg : qualsAt g n = []) :
    recoverAt (block c n ++ g) n = some c := by
  simp [recoverAt, subjPropAt_append, valueAt_append, rankAt_append, qualsAt_append, hg]

theorem recoverAt_append_of_none {g h : Graph} {i : Nat} (h1 : subjPropAt g i = none)
    (h2 : valueAt g i = none) (h3 : rankAt g i = none) (h4 : qualsAt g i = []) :
    recoverAt (g ++ h) i = recoverAt h i := by
  simp [recoverAt, subjPropAt_append, valueAt_append, rankAt_append, qualsAt_append,
    h1, h2, h3, h4]

/-- **The reified layer is lossless**: every statement of a claim set can be read back
off its exported graph — subject, property, value, rank and qualifiers. -/
theorem recoverAt_blocksFrom (cs : Claim.Set) (n i : Nat) (h : i < cs.length) :
    recoverAt (blocksFrom n cs) (n + i) = some cs[i] := by
  induction cs generalizing n i with
  | nil => simp at h
  | cons c t ih =>
      cases i with
      | zero =>
          rw [Nat.add_zero, blocksFrom]
          exact recoverAt_block_append c n _ (qualsAt_blocksFrom_lt (by omega))
      | succ k =>
          have hk : k < t.length := by simpa using Nat.lt_of_succ_lt_succ h
          have hidx : n + (k + 1) = (n + 1) + k := by omega
          rw [blocksFrom, hidx,
            recoverAt_append_of_none (subjPropAt_block_ne c (by omega))
              (valueAt_block_ne c (by omega)) (rankAt_block_ne c (by omega))
              (qualsAt_block_ne c (by omega))]
          simpa using ih (n + 1) k hk

/-- The export of a claim set determines each of its statements. -/
theorem recoverAt_fullGraph (cs : Claim.Set) (i : Nat) (h : i < cs.length) :
    recoverAt (fullGraph cs) i = some cs[i] := by
  simpa [fullGraph] using recoverAt_blocksFrom cs 0 i h

/-- Beyond the last statement nothing is recovered. -/
theorem recoverAt_fullGraph_eq_none (cs : Claim.Set) {i : Nat} (h : cs.length ≤ i) :
    recoverAt (fullGraph cs) i = none := by
  have hz := subjPropAt_blocksFrom_ge (cs := cs) (n := 0) (j := i) (by simpa using h)
  simp [recoverAt, fullGraph, hz]

/-- The exported graph determines the claim set: the export is injective. -/
theorem fullGraph_injective : Function.Injective fullGraph := by
  intro cs ds h
  have hlen : cs.length = ds.length := by
    by_contra hne
    rcases Nat.lt_or_ge cs.length ds.length with hlt | hge
    · have h1 := recoverAt_fullGraph ds cs.length hlt
      have h2 := recoverAt_fullGraph_eq_none cs (le_refl cs.length)
      rw [h] at h2
      rw [h1] at h2
      exact absurd h2 (by simp)
    · have hlt : ds.length < cs.length := lt_of_le_of_ne hge (Ne.symm hne)
      have h1 := recoverAt_fullGraph cs ds.length hlt
      have h2 := recoverAt_fullGraph_eq_none ds (le_refl ds.length)
      rw [← h] at h2
      rw [h1] at h2
      exact absurd h2 (by simp)
  refine List.ext_getElem hlen ?_
  intro i hi hi'
  have h1 := recoverAt_fullGraph cs i hi
  have h2 := recoverAt_fullGraph ds i hi'
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

/-- The block of the `i`-th statement really is part of the export. -/
theorem block_subset_blocksFrom (cs : Claim.Set) (n i : Nat) (h : i < cs.length) :
    ∀ x ∈ block cs[i] (n + i), x ∈ blocksFrom n cs := by
  induction cs generalizing n i with
  | nil => simp at h
  | cons c t ih =>
      cases i with
      | zero =>
          intro x hx
          rw [blocksFrom]
          exact List.mem_append_left _ (by simpa using hx)
      | succ k =>
          intro x hx
          have hk : k < t.length := by simpa using Nat.lt_of_succ_lt_succ h
          rw [blocksFrom]
          refine List.mem_append_right _ (ih (n + 1) k hk x ?_)
          simpa [show n + 1 + k = n + (k + 1) by omega] using hx

/-- Nothing is thrown away by the full layer: every statement, whatever its rank, is
reified in it. -/
theorem mem_fullGraph_of_mem {cs : Claim.Set} {c : Claim} (hc : c ∈ cs) :
    ∃ i, (Term.ent c.subject, Term.stmtProp c.pid, Term.node i) ∈ fullGraph cs ∧
      (Term.node i, Term.rankProp, Term.rankVal c.rank) ∈ fullGraph cs := by
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  refine ⟨i, ?_, ?_⟩ <;>
  · have hsub := block_subset_blocksFrom cs 0 i hi
    rw [Nat.zero_add, hci] at hsub
    exact hsub _ (by simp [block])

/-! ### The truthy layer -/

/-- A direct (`wdt:`) triple is exported exactly for the values a default query returns. -/
theorem mem_truthyGraph_iff {cs : Claim.Set} {s : Qid} {p : Pid} {v : Value} :
    (Term.ent s, Term.truthyProp p, objOf v) ∈ truthyGraph cs ↔ v ∈ Claim.truthyValues cs s p := by
  constructor
  · intro h
    obtain ⟨c, hc, hEq⟩ := List.mem_map.1 h
    obtain ⟨hcs, ht⟩ := Claim.mem_truthy_iff.1 hc
    have h1 : c.subject = s := by
      have := congrArg Prod.fst hEq
      simpa using this
    have h2 : c.pid = p := by
      have := congrArg (fun t => t.2.1) hEq
      simpa using this
    have h3 : c.value = v := objOf_injective (by
      have := congrArg (fun t => t.2.2) hEq
      simpa using this)
    have : c ∈ (Claim.group cs s p).filter (fun c => decide (Claim.isTruthy cs c)) := by
      simp [List.mem_filter, Claim.mem_group_iff, hcs, h1, h2, ht]
    exact h3 ▸ List.mem_map_of_mem this
  · intro h
    obtain ⟨c, hc, hv⟩ := List.mem_map.1 h
    rw [List.mem_filter] at hc
    obtain ⟨hg, ht⟩ := hc
    obtain ⟨hcs, hs, hp⟩ := Claim.mem_group_iff.1 hg
    refine List.mem_map.2 ⟨c, Claim.mem_truthy_iff.2 ⟨hcs, by simpa using ht⟩, ?_⟩
    simp [hs, hp, hv]

/-- Every direct triple comes from a statement that is not deprecated. -/
theorem rank_ne_deprecated_of_mem_truthyGraph {cs : Claim.Set} {t : Triple}
    (h : t ∈ truthyGraph cs) :
    ∃ c ∈ cs, c.rank ≠ Rank.deprecated ∧
      t = (Term.ent c.subject, Term.truthyProp c.pid, objOf c.value) := by
  obtain ⟨c, hc, hEq⟩ := List.mem_map.1 h
  obtain ⟨hcs, ht⟩ := Claim.mem_truthy_iff.1 hc
  exact ⟨c, hcs, ht.1, hEq.symm⟩

/-- The truthy layer of a claim set with no non-deprecated statement is empty. -/
theorem truthyGraph_eq_nil_of_all_deprecated {cs : Claim.Set}
    (h : ∀ c ∈ cs, c.rank = Rank.deprecated) : truthyGraph cs = [] := by
  rcases hnil : truthyGraph cs with _ | ⟨t, rest⟩
  · rfl
  · exfalso
    have : t ∈ truthyGraph cs := by rw [hnil]; exact List.mem_cons_self
    obtain ⟨c, hc, hne, -⟩ := rank_ne_deprecated_of_mem_truthyGraph this
    exact hne (h c hc)

/-! ### RDFS-style entailment on the ontology graph -/

/-- `subclass of`. -/
def pSubclassOf : Pid := .wd "P279"

/-- `instance of`. -/
def pInstanceOf : Pid := .wd "P31"

/-- The direct triples exported for the ontology layer of a knowledge base. -/
def kbGraph (kb : KB) : Graph :=
  kb.sub.map (fun r => (Term.ent r.1, Term.truthyProp pSubclassOf, Term.ent r.2)) ++
  kb.inst.map (fun r => (Term.ent r.1, Term.truthyProp pInstanceOf, Term.ent r.2))

/-- RDFS-style entailment: the triples of the graph, closed under reflexivity and
transitivity of `wdt:P279` and under `wdt:P31` followed by `wdt:P279`. -/
inductive Entails (g : Graph) : Triple → Prop
  /-- Every triple of the graph is entailed. -/
  | base {t : Triple} : t ∈ g → Entails g t
  /-- `rdfs:subClassOf` is reflexive. -/
  | refl (a : Qid) : Entails g (Term.ent a, Term.truthyProp pSubclassOf, Term.ent a)
  /-- `rdfs:subClassOf` is transitive. -/
  | trans {a b c : Qid} :
      Entails g (Term.ent a, Term.truthyProp pSubclassOf, Term.ent b) →
      Entails g (Term.ent b, Term.truthyProp pSubclassOf, Term.ent c) →
      Entails g (Term.ent a, Term.truthyProp pSubclassOf, Term.ent c)
  /-- An instance of a class is an instance of its superclasses. -/
  | inst {a b c : Qid} :
      Entails g (Term.ent a, Term.truthyProp pInstanceOf, Term.ent b) →
      Entails g (Term.ent b, Term.truthyProp pSubclassOf, Term.ent c) →
      Entails g (Term.ent a, Term.truthyProp pInstanceOf, Term.ent c)

theorem pSubclassOf_ne_pInstanceOf : pSubclassOf ≠ pInstanceOf := by decide

/-- What a triple of the ontology graph says about the knowledge base: a `wdt:P279`
triple asserts derived `subclass of`, a `wdt:P31` triple derived `instance of`, and any
other triple says nothing. -/
def Denote (kb : KB) : Triple → Prop
  | (.ent a, .truthyProp p, .ent b) =>
      if p = pSubclassOf then Relation.ReflTransGen kb.Sub a b
      else if p = pInstanceOf then ∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d b
      else False
  | _ => False

@[simp] theorem denote_sub (kb : KB) (a b : Qid) :
    Denote kb (Term.ent a, Term.truthyProp pSubclassOf, Term.ent b) ↔
      Relation.ReflTransGen kb.Sub a b := by
  simp [Denote]

@[simp] theorem denote_inst (kb : KB) (a b : Qid) :
    Denote kb (Term.ent a, Term.truthyProp pInstanceOf, Term.ent b) ↔
      ∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d b := by
  simp [Denote, show pInstanceOf ≠ pSubclassOf from Ne.symm pSubclassOf_ne_pInstanceOf]

/-- **Soundness** of the entailment rules: everything the RDFS rules derive from the
exported ontology graph is a fact of the knowledge base. -/
theorem entails_sound {kb : KB} {t : Triple} (h : Entails (kbGraph kb) t) : Denote kb t := by
  induction h with
  | base hmem =>
      rcases List.mem_append.1 hmem with hm | hm
      · obtain ⟨r, hr, hEq⟩ := List.mem_map.1 hm
        subst hEq
        exact (denote_sub kb r.1 r.2).2 (Relation.ReflTransGen.single hr)
      · obtain ⟨r, hr, hEq⟩ := List.mem_map.1 hm
        subst hEq
        exact (denote_inst kb r.1 r.2).2 ⟨r.2, hr, Relation.ReflTransGen.refl⟩
  | refl a => exact (denote_sub kb a a).2 Relation.ReflTransGen.refl
  | trans _ _ ih₁ ih₂ =>
      simp only [denote_sub] at *
      exact ih₁.trans ih₂
  | inst _ _ ih₁ ih₂ =>
      simp only [denote_sub, denote_inst] at *
      obtain ⟨d, hd, hdb⟩ := ih₁
      exact ⟨d, hd, hdb.trans ih₂⟩

/-- **Completeness** for the class hierarchy: every derived `subclass of` fact is
entailed by the graph. -/
theorem entails_of_reflTransGen {kb : KB} {a b : Qid} (h : Relation.ReflTransGen kb.Sub a b) :
    Entails (kbGraph kb) (Term.ent a, Term.truthyProp pSubclassOf, Term.ent b) := by
  induction h with
  | refl => exact Entails.refl a
  | tail _ hstep ih =>
      exact Entails.trans ih (Entails.base
        (List.mem_append_left _ (List.mem_map.2 ⟨(_, _), hstep, rfl⟩)))

/-- The RDFS entailment of a `wdt:P279` triple is exactly derived `subclass of`. -/
theorem entails_sub_iff {kb : KB} {a b : Qid} :
    Entails (kbGraph kb) (Term.ent a, Term.truthyProp pSubclassOf, Term.ent b) ↔
      Relation.ReflTransGen kb.Sub a b :=
  ⟨fun h => (denote_sub kb a b).1 (entails_sound h), entails_of_reflTransGen⟩

/-- The RDFS entailment of a `wdt:P31` triple is exactly derived `instance of`. -/
theorem entails_inst_iff {kb : KB} {a b : Qid} :
    Entails (kbGraph kb) (Term.ent a, Term.truthyProp pInstanceOf, Term.ent b) ↔
      ∃ d, kb.Inst a d ∧ Relation.ReflTransGen kb.Sub d b := by
  refine ⟨fun h => (denote_inst kb a b).1 (entails_sound h), ?_⟩
  rintro ⟨d, hd, hdb⟩
  exact Entails.inst (Entails.base (List.mem_append_right _
    (List.mem_map.2 ⟨(a, d), hd, rfl⟩))) (entails_of_reflTransGen hdb)

/-- The entailed `subclass of` triples are exactly the ones the engine computes. -/
theorem entails_iff_isSubclassOf {kb : KB} (hwf : kb.wellFormed = true) {a : Qid}
    (ha : a ∈ kb.items) (b : Qid) :
    Entails (kbGraph kb) (Term.ent a, Term.truthyProp pSubclassOf, Term.ent b) ↔
      kb.isSubclassOf a b = true := by
  rw [entails_sub_iff, KB.isSubclassOf_iff_of_mem hwf ha]


/-! ### A worked fragment

The Berlin fragment of `RequestProject.Ranks` (three `population` statements at three
different ranks, each with a `point in time` qualifier, plus two item-valued statements),
exported to RDF. -/

namespace RdfExample

open RankExample

/-- The full layer reifies all five statements: `3 + 1` triples for each of the three
qualified population statements and `3` for each of the two unqualified ones. -/
theorem berlin_fullGraph_length : (fullGraph berlin).length = 18 := by decide

/-- The truthy layer has one direct triple per truthy statement: the preferred
population, the country and the "capital of". -/
theorem berlin_truthyGraph :
    truthyGraph berlin =
      [(Term.ent (Q "Q64"), Term.truthyProp (P "P1082"), Term.lit (.quantity 3644826)),
       (Term.ent (Q "Q64"), Term.truthyProp (P "P17"), Term.ent (Q "Q183")),
       (Term.ent (Q "Q64"), Term.truthyProp (P "P1376"), Term.ent (Q "Q183"))] := by decide

/-- The deprecated population value gets **no** direct triple ... -/
theorem berlin_deprecated_not_truthy :
    (Term.ent (Q "Q64"), Term.truthyProp (P "P1082"), objOf (.quantity 100)) ∉
      truthyGraph berlin := by decide

/-- ... but it is still reified in the full layer, rank and qualifier included, and can
be read back off the graph. -/
theorem berlin_recover_deprecated :
    recoverAt (fullGraph berlin) 2 =
      some { subject := Q "Q64", pid := P "P1082", value := .quantity 100,
             rank := .deprecated, quals := [(P "P2241", .item (Q "Q1193907"))] } := by decide

/-- The superseded, still visible, statement is recovered as well. -/
theorem berlin_recover_normal :
    recoverAt (fullGraph berlin) 1 =
      some { subject := Q "Q64", pid := P "P1082", value := .quantity 3292365,
             rank := .normal, quals := [(P "P585", .time 2011)] } := by decide

/-- There are exactly five statement nodes. -/
theorem berlin_recover_five : recoverAt (fullGraph berlin) 5 = none :=
  recoverAt_fullGraph_eq_none berlin (by decide)

/-- A small ontology graph: Douglas Adams is an instance of human, human a subclass of
person, person a subclass of entity. -/
def kbFragment : KB :=
  { name := "rdf-fragment"
    items := [Q "Q42", Q "Q5", Q "Q215627", Q "Q35120"]
    levels := [(Q "Q42", 0), (Q "Q5", 1), (Q "Q215627", 1), (Q "Q35120", 1)]
    sub := [(Q "Q5", Q "Q215627"), (Q "Q215627", Q "Q35120")]
    inst := [(Q "Q42", Q "Q5")] }

theorem kbFragment_valid : kbFragment.valid = true := by decide

/-- The RDFS rules on the exported graph derive that Douglas Adams is an entity, a fact
that is nowhere in the graph itself. -/
theorem entails_adams_entity :
    Entails (kbGraph kbFragment)
      (Term.ent (Q "Q42"), Term.truthyProp pInstanceOf, Term.ent (Q "Q35120")) := by
  refine entails_inst_iff.2 ⟨Q "Q5", show (Q "Q42", Q "Q5") ∈ kbFragment.inst by decide, ?_⟩
  exact Relation.ReflTransGen.head (show (Q "Q5", Q "Q215627") ∈ kbFragment.sub by decide)
    (Relation.ReflTransGen.single (show (Q "Q215627", Q "Q35120") ∈ kbFragment.sub by decide))

/-- The same fact, read off the engine. -/
theorem adams_entity_computed : kbFragment.isInstanceOf (Q "Q42") (Q "Q35120") = true := by
  decide

/-- Nothing spurious: the graph does not entail that human is a subclass of Douglas
Adams. -/
theorem not_entails_human_sub_adams :
    ¬ Entails (kbGraph kbFragment)
        (Term.ent (Q "Q5"), Term.truthyProp pSubclassOf, Term.ent (Q "Q42")) := by
  intro h
  have := (entails_iff_isSubclassOf (kb := kbFragment) (by decide) (by decide) (Q "Q42")).1 h
  exact absurd this (by decide)

end RdfExample

end Rdf
end Wikidata
