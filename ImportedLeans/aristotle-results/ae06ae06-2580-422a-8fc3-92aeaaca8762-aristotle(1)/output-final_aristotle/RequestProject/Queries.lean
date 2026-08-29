import RequestProject.Examples
import RequestProject.FastEval
import RequestProject.Normalize

/-!
# Conjunctive queries over the ontology

Wikidata is queried, in practice, with basic graph patterns: a conjunction of triple
patterns whose subjects and objects are either fixed items or variables, evaluated
against the *entailed* graph (`wdt:P279*`, `wdt:P31/wdt:P279*`) rather than against the
raw statements.  This file adds such a query language to the executable ontology of
`RequestProject.Engine`, together with an evaluator and a proof that the evaluator is
both sound and complete for the abstract semantics of `RequestProject.Core`.

* `Wikidata.Query.Atom` is a single pattern: derived `subclass of`, derived
  `instance of`, a direct P279 or P31 statement, classhood, or a disequality; a query
  (`Wikidata.Query.BGP`) is a list of atoms, read conjunctively.
* `Wikidata.Query.Atom.Sat` is the meaning of an atom under a total assignment of items
  to variables, stated in terms of the abstract ontology `KB.toOntology` — so
  `subclass of` means `Ontology.SubclassOf`, and so on.
* `Wikidata.Query.eval` is the evaluator: it returns the list of bindings of the
  query's variables that make the query true.
* `Wikidata.Query.eval_sound` — every binding returned is total on the variables of the
  query and satisfies it.
* `Wikidata.Query.eval_complete` — conversely, every assignment satisfying the query by
  items of the knowledge base is returned (up to the variables the query mentions).
* `Wikidata.Query.mem_eval_iff` packages the two: the evaluator returns exactly the
  satisfying assignments.
* `Wikidata.Query.evalT_eq_eval` — evaluating against a precomputed closure table (what
  the command line tool does) changes no answer.
* `Wikidata.Query.Sat_normalize` — normalising a knowledge base answers every query
  exactly as before; `Wikidata.Query.Sat_of_entails`, `Sat_merge_left`,
  `Sat_merge_right` — a base that entails another answers at least as much, for queries
  about the derived relations.

The last section runs some queries against the worked Wikidata fragment of
`RequestProject.Examples`.
-/

namespace Wikidata
namespace Query

/-- A term of a query: a variable or a fixed item. -/
inductive Tm where
  /-- A query variable, given by its name. -/
  | var (n : String)
  /-- A fixed item. -/
  | item (q : Qid)
deriving DecidableEq, Repr, Inhabited

/-- A single pattern of a query. -/
inductive Atom where
  /-- Derived `subclass of`: `s` is a subclass of `o` (P279, reflexive–transitive). -/
  | sub (s o : Tm)
  /-- Derived `instance of`: `s` is an instance of `o` (P31 followed by P279 steps). -/
  | inst (s o : Tm)
  /-- A *directly asserted* `subclass of` (P279) statement. -/
  | dsub (s o : Tm)
  /-- A *directly asserted* `instance of` (P31) statement. -/
  | dinst (s o : Tm)
  /-- The item is a class, i.e. sits at metaclass level at least `1`. -/
  | isClass (s : Tm)
  /-- The two terms denote different items. -/
  | ne (s o : Tm)
deriving DecidableEq, Repr, Inhabited

/-- A basic graph pattern: a conjunction of atoms. -/
abbrev BGP := List Atom

/-- A binding of (some of) the query variables to items. -/
abbrev Env := List (String × Qid)

/-! ### Variables -/

/-- The variables of a term. -/
def Tm.vars : Tm → List String
  | .var n => [n]
  | .item _ => []

/-- The variables of an atom. -/
def Atom.vars : Atom → List String
  | .sub s o | .inst s o | .dsub s o | .dinst s o | .ne s o => s.vars ++ o.vars
  | .isClass s => s.vars

/-- The variables of a query. -/
def bgpVars (q : BGP) : List String := q.flatMap Atom.vars

/-! ### Bindings -/

/-- The item a term denotes under a partial binding, if it is determined. -/
def Tm.resolve (e : Env) : Tm → Option Qid
  | .var n => e.lookup n
  | .item q => some q

/-- The item a term denotes under a total assignment. -/
def Tm.den (g : String → Qid) : Tm → Qid
  | .var n => g n
  | .item q => q

/-- `e` binds every variable of `ns`. -/
def Covers (e : Env) (ns : List String) : Prop := ∀ n ∈ ns, (e.lookup n).isSome

/-- `e'` binds everything `e` binds, the same way. -/
def Extends (e e' : Env) : Prop := ∀ n v, e.lookup n = some v → e'.lookup n = some v

/-- The partial binding `e` is a restriction of the total assignment `g`. -/
def AgreesWith (e : Env) (g : String → Qid) : Prop := ∀ n v, e.lookup n = some v → g n = v

theorem Extends.refl (e : Env) : Extends e e := fun _ _ h => h

theorem Extends.trans {e₁ e₂ e₃ : Env} (h₁ : Extends e₁ e₂) (h₂ : Extends e₂ e₃) :
    Extends e₁ e₃ := fun n v h => h₂ n v (h₁ n v h)

theorem Covers.mono {e e' : Env} {ns : List String} (hext : Extends e e') (h : Covers e ns) :
    Covers e' ns := by
  intro n hn
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h n hn)
  simp [hext n v hv]

theorem Tm.resolve_den {e : Env} {g : String → Qid} (hag : AgreesWith e g) {t : Tm} {q : Qid}
    (h : t.resolve e = some q) : t.den g = q := by
  cases t with
  | var n => exact hag n q h
  | item q' => simpa [Tm.den] using (Option.some_injective _ h).symm ▸ rfl

theorem Tm.resolve_eq_den {e : Env} {g : String → Qid} (hag : AgreesWith e g) {t : Tm}
    (hc : Covers e t.vars) : t.resolve e = some (t.den g) := by
  cases t with
  | var n =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hc n (by simp [Tm.vars]))
      rw [Tm.resolve, hv, Tm.den, hag n v hv]
  | item q => rfl

theorem Tm.resolve_mono {e e' : Env} (hext : Extends e e') {t : Tm} {q : Qid}
    (h : t.resolve e = some q) : t.resolve e' = some q := by
  cases t with
  | var n => exact hext n q h
  | item _ => exact h

/-! ### Checking an atom -/

/-- Check a binary pattern once both terms are resolved. -/
def checkBin (e : Env) (s o : Tm) (r : Qid → Qid → Bool) : Bool :=
  match s.resolve e, o.resolve e with
  | some x, some y => r x y
  | _, _ => false

/-- Check a unary pattern once its term is resolved. -/
def checkUn (e : Env) (s : Tm) (r : Qid → Bool) : Bool :=
  match s.resolve e with
  | some x => r x
  | none => false

/-- Decide whether an atom holds under a binding; `false` if some variable is unbound. -/
def Atom.check (kb : KB) (e : Env) : Atom → Bool
  | .sub s o => checkBin e s o kb.isSubclassOf
  | .inst s o => checkBin e s o kb.isInstanceOf
  | .dsub s o => checkBin e s o (fun x y => decide ((x, y) ∈ kb.sub))
  | .dinst s o => checkBin e s o (fun x y => decide ((x, y) ∈ kb.inst))
  | .isClass s => checkUn e s kb.isClassB
  | .ne s o => checkBin e s o (fun x y => decide (x ≠ y))

/-- The meaning of an atom under a total assignment, in the abstract ontology of a
validated knowledge base. -/
def Atom.Sat (kb : KB) (hv : kb.valid = true) (g : String → Qid) : Atom → Prop
  | .sub s o => (kb.toOntology hv).SubclassOf (s.den g) (o.den g)
  | .inst s o => (kb.toOntology hv).InstanceOf (s.den g) (o.den g)
  | .dsub s o => kb.Sub (s.den g) (o.den g)
  | .dinst s o => kb.Inst (s.den g) (o.den g)
  | .isClass s => (kb.toOntology hv).IsClass (s.den g)
  | .ne s o => s.den g ≠ o.den g

/-- A query is satisfied by an assignment when all of its atoms are. -/
def Sat (kb : KB) (hv : kb.valid = true) (g : String → Qid) (q : BGP) : Prop :=
  ∀ a ∈ q, Atom.Sat kb hv g a

theorem Atom.check_mono {kb : KB} {e e' : Env} (hext : Extends e e') {a : Atom}
    (h : a.check kb e = true) : a.check kb e' = true := by
  cases a <;>
    simp only [Atom.check, checkBin, checkUn] at h ⊢ <;>
    · first
      | (rcases hs : Tm.resolve e _ with _ | x
         · rw [hs] at h; simp at h
         · rcases ho : Tm.resolve e _ with _ | y
           · rw [hs, ho] at h; simp at h
           · rw [Tm.resolve_mono hext hs, Tm.resolve_mono hext ho]
             rw [hs, ho] at h; exact h)
      | (rcases hs : Tm.resolve e _ with _ | x
         · rw [hs] at h; simp at h
         · rw [Tm.resolve_mono hext hs]; rw [hs] at h; exact h)

/-- **The check computes the semantics**: on a binding that covers its variables, the
Boolean check of an atom agrees with its meaning in the abstract ontology. -/
theorem Atom.check_iff_sat {kb : KB} (hv : kb.valid = true) {e : Env} {g : String → Qid}
    (hag : AgreesWith e g) {a : Atom} (hc : Covers e a.vars) :
    a.check kb e = true ↔ a.Sat kb hv g := by
  have hsplit : ∀ s o : Tm, a.vars = s.vars ++ o.vars → Covers e s.vars ∧ Covers e o.vars := by
    intro s o hvars
    constructor <;> intro n hn <;> exact hc n (by rw [hvars]; simp [hn])
  cases a with
  | sub s o =>
      obtain ⟨h1, h2⟩ := hsplit s o rfl
      rw [Atom.check, checkBin, Tm.resolve_eq_den hag h1, Tm.resolve_eq_den hag h2]
      exact kb.isSubclassOf_iff_subclassOf hv _ _
  | inst s o =>
      obtain ⟨h1, h2⟩ := hsplit s o rfl
      rw [Atom.check, checkBin, Tm.resolve_eq_den hag h1, Tm.resolve_eq_den hag h2]
      exact kb.isInstanceOf_iff_instanceOf hv _ _
  | dsub s o =>
      obtain ⟨h1, h2⟩ := hsplit s o rfl
      rw [Atom.check, checkBin, Tm.resolve_eq_den hag h1, Tm.resolve_eq_den hag h2]
      simp [Atom.Sat, KB.Sub]
  | dinst s o =>
      obtain ⟨h1, h2⟩ := hsplit s o rfl
      rw [Atom.check, checkBin, Tm.resolve_eq_den hag h1, Tm.resolve_eq_den hag h2]
      simp [Atom.Sat, KB.Inst]
  | isClass s =>
      have h1 : Covers e s.vars := hc
      rw [Atom.check, checkUn, Tm.resolve_eq_den hag h1]
      simp [Atom.Sat, KB.isClassB, Ontology.IsClass]
  | ne s o =>
      obtain ⟨h1, h2⟩ := hsplit s o rfl
      rw [Atom.check, checkBin, Tm.resolve_eq_den hag h1, Tm.resolve_eq_den hag h2]
      simp [Atom.Sat]

/-! ### The evaluator -/

/-- Extend a binding so that it covers the given variables, in all possible ways using
the items of the knowledge base. -/
def extendVars (kb : KB) : List String → Env → List Env
  | [], e => [e]
  | n :: ns, e =>
      if (e.lookup n).isSome then extendVars kb ns e
      else kb.items.flatMap (fun q => extendVars kb ns ((n, q) :: e))

/-- All the ways of extending a binding to one satisfying the atom. -/
def stepAtom (kb : KB) (a : Atom) (e : Env) : List Env :=
  (extendVars kb a.vars e).filter (fun e' => a.check kb e')

/-- Evaluate a query starting from a partial binding. -/
def evalFrom (kb : KB) : BGP → Env → List Env
  | [], e => [e]
  | a :: as, e => (stepAtom kb a e).flatMap (fun e' => evalFrom kb as e')

/-- **The evaluator**: all bindings of the query's variables that satisfy it. -/
def eval (kb : KB) (q : BGP) : List Env := evalFrom kb q []

/-- The answers to a query, projected onto the chosen output variables. -/
def answers (kb : KB) (q : BGP) (outs : List String) : List (List Qid) :=
  ((eval kb q).map (fun e => outs.filterMap (fun n => e.lookup n))).dedup

/-! ### Soundness and completeness -/

/-- Every value a binding assigns is an item of the knowledge base. -/
def ValuesIn (kb : KB) (e : Env) : Prop := ∀ n v, e.lookup n = some v → v ∈ kb.items

theorem lookup_cons_ne (e : Env) (n m : String) (q : Qid) (hne : m ≠ n) :
    ((n, q) :: e).lookup m = e.lookup m := by
  have hb : (m == n) = false := by simpa using hne
  simp [List.lookup_cons, hb]

theorem lookup_cons_of_ne {e : Env} {n m : String} {q v : Qid} (hne : m ≠ n)
    (h : e.lookup m = some v) : ((n, q) :: e).lookup m = some v := by
  rw [lookup_cons_ne e n m q hne, h]

theorem extendVars_extends (kb : KB) (ns : List String) (e e' : Env)
    (h : e' ∈ extendVars kb ns e) : Extends e e' := by
  induction ns generalizing e with
  | nil => simp [extendVars] at h; subst h; exact Extends.refl _
  | cons n ns ih =>
      rw [extendVars] at h
      split at h
      · exact ih e h
      · rename_i hnone
        simp only [List.mem_flatMap] at h
        obtain ⟨q, _, hq⟩ := h
        refine Extends.trans (fun m v hm => ?_) (ih _ hq)
        have hne : m ≠ n := by
          rintro rfl; rw [hm] at hnone; simp at hnone
        exact lookup_cons_of_ne hne hm

theorem extendVars_covers (kb : KB) (ns : List String) (e e' : Env)
    (h : e' ∈ extendVars kb ns e) : Covers e' ns := by
  induction ns generalizing e with
  | nil => intro n hn; simp at hn
  | cons n ns ih =>
      rw [extendVars] at h
      split at h
      · rename_i hsome
        intro m hm
        rcases List.mem_cons.1 hm with rfl | hm
        · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
          simp [extendVars_extends kb ns e e' h m v hv]
        · exact ih e h m hm
      · simp only [List.mem_flatMap] at h
        obtain ⟨q, _, hq⟩ := h
        intro m hm
        rcases List.mem_cons.1 hm with rfl | hm
        · have : ((m, q) :: e).lookup m = some q := by simp
          simp [extendVars_extends kb ns _ e' hq m q this]
        · exact ih _ hq m hm

theorem extendVars_agrees (kb : KB) (ns : List String) (e : Env) (g : String → Qid)
    (hag : AgreesWith e g) (hitems : ∀ n ∈ ns, g n ∈ kb.items) :
    ∃ e' ∈ extendVars kb ns e, AgreesWith e' g := by
  induction ns generalizing e with
  | nil => exact ⟨e, by simp [extendVars], hag⟩
  | cons n ns ih =>
      rw [extendVars]
      split
      · exact ih e hag (fun m hm => hitems m (by simp [hm]))
      · rename_i hnone
        have hag' : AgreesWith ((n, g n) :: e) g := by
          intro m v hm
          by_cases h : m = n
          · subst h
            rw [show ((m, g m) :: e).lookup m = some (g m) by simp] at hm
            exact Option.some.inj hm
          · rw [lookup_cons_ne e n m (g n) h] at hm
            exact hag m v hm
        obtain ⟨e', he', hage'⟩ := ih ((n, g n) :: e) hag' (fun m hm => hitems m (by simp [hm]))
        refine ⟨e', ?_, hage'⟩
        simp only [List.mem_flatMap]
        exact ⟨g n, hitems n (by simp), he'⟩

theorem extendVars_valuesIn (kb : KB) (ns : List String) (e e' : Env) (hv : ValuesIn kb e)
    (h : e' ∈ extendVars kb ns e) : ValuesIn kb e' := by
  induction ns generalizing e with
  | nil => simp [extendVars] at h; subst h; exact hv
  | cons n ns ih =>
      rw [extendVars] at h
      split at h
      · exact ih e hv h
      · simp only [List.mem_flatMap] at h
        obtain ⟨q, hq, hmem⟩ := h
        refine ih ((n, q) :: e) ?_ hmem
        intro m w hm
        by_cases hmn : m = n
        · subst hmn
          rw [show ((m, q) :: e).lookup m = some q by simp] at hm
          exact (Option.some.inj hm) ▸ hq
        · rw [lookup_cons_ne e n m q hmn] at hm
          exact hv m w hm

theorem evalFrom_valuesIn (kb : KB) (q : BGP) (e e' : Env) (hv : ValuesIn kb e)
    (h : e' ∈ evalFrom kb q e) : ValuesIn kb e' := by
  induction q generalizing e with
  | nil => simp [evalFrom] at h; subst h; exact hv
  | cons a as ih =>
      rw [evalFrom] at h
      simp only [List.mem_flatMap] at h
      obtain ⟨e₁, h₁, h₂⟩ := h
      rw [stepAtom, List.mem_filter] at h₁
      exact ih e₁ (extendVars_valuesIn kb a.vars e e₁ hv h₁.1) h₂

/-- Every value in an answer of the evaluator is an item of the knowledge base. -/
theorem eval_valuesIn (kb : KB) (q : BGP) {e : Env} (h : e ∈ eval kb q) : ValuesIn kb e :=
  evalFrom_valuesIn kb q [] e (by intro n v hn; simp at hn) h

theorem evalFrom_extends (kb : KB) (q : BGP) (e e' : Env) (h : e' ∈ evalFrom kb q e) :
    Extends e e' := by
  induction q generalizing e with
  | nil => simp [evalFrom] at h; subst h; exact Extends.refl _
  | cons a as ih =>
      rw [evalFrom] at h
      simp only [List.mem_flatMap] at h
      obtain ⟨e₁, h₁, h₂⟩ := h
      rw [stepAtom, List.mem_filter] at h₁
      exact Extends.trans (extendVars_extends kb a.vars e e₁ h₁.1) (ih e₁ h₂)

theorem evalFrom_sound (kb : KB) (q : BGP) (e e' : Env) (h : e' ∈ evalFrom kb q e) :
    Covers e' (bgpVars q) ∧ ∀ a ∈ q, a.check kb e' = true := by
  induction q generalizing e with
  | nil =>
      exact ⟨fun n hn => by simp [bgpVars] at hn, fun a ha => by simp at ha⟩
  | cons a as ih =>
      rw [evalFrom] at h
      simp only [List.mem_flatMap] at h
      obtain ⟨e₁, h₁, h₂⟩ := h
      rw [stepAtom, List.mem_filter] at h₁
      have hext : Extends e₁ e' := evalFrom_extends kb as e₁ e' h₂
      obtain ⟨hcov, hchk⟩ := ih e₁ h₂
      constructor
      · intro m hm
        rw [bgpVars, List.flatMap_cons, List.mem_append] at hm
        rcases hm with hm | hm
        · exact (extendVars_covers kb a.vars e e₁ h₁.1).mono hext m hm
        · exact hcov m hm
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact Atom.check_mono hext (by simpa using h₁.2)
        · exact hchk b hb

/-- **Soundness of the evaluator**: every binding it returns is defined on all the
variables of the query and makes every atom true. -/
theorem eval_sound (kb : KB) (q : BGP) {e : Env} (h : e ∈ eval kb q) :
    Covers e (bgpVars q) ∧ ∀ a ∈ q, a.check kb e = true :=
  evalFrom_sound kb q [] e h

/-- Soundness, semantically: any total assignment restricting to a returned binding
satisfies the query in the abstract ontology. -/
theorem eval_sat (kb : KB) (hv : kb.valid = true) (q : BGP) {e : Env} (h : e ∈ eval kb q)
    {g : String → Qid} (hag : AgreesWith e g) : Sat kb hv g q := by
  obtain ⟨hcov, hchk⟩ := eval_sound kb q h
  intro a ha
  refine (Atom.check_iff_sat hv hag ?_).1 (hchk a ha)
  intro m hm
  exact hcov m (by rw [bgpVars]; simp only [List.mem_flatMap]; exact ⟨a, ha, hm⟩)

theorem evalFrom_complete (kb : KB) (hv : kb.valid = true) (q : BGP) (g : String → Qid)
    (hsat : Sat kb hv g q) (hitems : ∀ n ∈ bgpVars q, g n ∈ kb.items) (e : Env)
    (hag : AgreesWith e g) : ∃ e' ∈ evalFrom kb q e, AgreesWith e' g := by
  induction q generalizing e with
  | nil => exact ⟨e, by simp [evalFrom], hag⟩
  | cons a as ih =>
      have hva : ∀ n ∈ a.vars, g n ∈ kb.items := by
        intro n hn
        have : n ∈ bgpVars (a :: as) := by
          rw [bgpVars, List.flatMap_cons, List.mem_append]
          exact Or.inl hn
        exact hitems n this
      have hvas : ∀ n ∈ bgpVars as, g n ∈ kb.items := by
        intro n hn
        have : n ∈ bgpVars (a :: as) := by
          rw [bgpVars, List.flatMap_cons, List.mem_append]
          exact Or.inr hn
        exact hitems n this
      obtain ⟨e₁, he₁, hag₁⟩ := extendVars_agrees kb a.vars e g hag hva
      have hcov : Covers e₁ a.vars := extendVars_covers kb a.vars e e₁ he₁
      have hchk : a.check kb e₁ = true :=
        (Atom.check_iff_sat hv hag₁ hcov).2 (hsat a (by simp))
      obtain ⟨e', he', hage'⟩ :=
        ih (fun b hb => hsat b (by simp [hb])) hvas e₁ hag₁
      refine ⟨e', ?_, hage'⟩
      rw [evalFrom]
      simp only [List.mem_flatMap]
      exact ⟨e₁, by rw [stepAtom, List.mem_filter]; exact ⟨he₁, by simpa using hchk⟩, he'⟩

/-- **Completeness of the evaluator**: every assignment of items of the knowledge base
that satisfies the query is returned, as far as the query's variables are concerned. -/
theorem eval_complete (kb : KB) (hv : kb.valid = true) (q : BGP) (g : String → Qid)
    (hsat : Sat kb hv g q) (hitems : ∀ n ∈ bgpVars q, g n ∈ kb.items) :
    ∃ e ∈ eval kb q, AgreesWith e g ∧ Covers e (bgpVars q) := by
  obtain ⟨e, he, hag⟩ := evalFrom_complete kb hv q g hsat hitems [] (by intro n v h; simp at h)
  exact ⟨e, he, hag, (eval_sound kb q he).1⟩

/-- **The evaluator computes exactly the satisfying assignments.** For an assignment
taking values among the items of the knowledge base, the query holds in the abstract
ontology precisely when the evaluator returns a binding it restricts to. -/
theorem mem_eval_iff (kb : KB) (hv : kb.valid = true) (q : BGP) (g : String → Qid)
    (hitems : ∀ n ∈ bgpVars q, g n ∈ kb.items) :
    (∃ e ∈ eval kb q, AgreesWith e g ∧ Covers e (bgpVars q)) ↔ Sat kb hv g q := by
  constructor
  · rintro ⟨e, he, hag, -⟩
    exact eval_sat kb hv q he hag
  · intro hsat
    exact eval_complete kb hv q g hsat hitems

/-- An unsatisfiable query has no answers, and conversely: emptiness of the evaluator's
output is exactly unsatisfiability over the items of the knowledge base. -/
theorem eval_eq_nil_iff (kb : KB) (hv : kb.valid = true) (q : BGP) (hne : kb.items ≠ []) :
    eval kb q = [] ↔
      ∀ g : String → Qid, (∀ n ∈ bgpVars q, g n ∈ kb.items) → ¬ Sat kb hv g q := by
  obtain ⟨q₀, hq₀⟩ := List.exists_mem_of_ne_nil _ hne
  constructor
  · intro h g hg hsat
    obtain ⟨e, he, -⟩ := eval_complete kb hv q g hsat hg
    rw [h] at he; simp at he
  · intro h
    by_contra hnil
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hnil
    obtain ⟨hcov, -⟩ := eval_sound kb q he
    refine h (fun n => (e.lookup n).getD q₀) ?_ (eval_sat kb hv q he ?_)
    · intro n hn
      obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 (hcov n hn)
      have : v ∈ kb.items := eval_valuesIn kb q he n v hv'
      simpa [hv'] using this
    · intro n v hv'; simp [hv']

/-! ### Queries under normalisation and under growth

Two invariance results, in terms of the semantics rather than of the evaluator:
normalising a knowledge base answers every query exactly as before, and a base that
entails another answers at least as much — as long as the query asks about the derived
relations, since a *directly asserted* statement can of course be lost when one base is
merely entailed by another. -/

/-- A validated base normalises to a validated base. -/
theorem normalize_valid_of_valid {kb : KB} (hv : kb.valid = true) : kb.normalize.valid = true := by
  rw [KB.normalize_valid (KB.valid_wellFormed hv)]; exact hv

/-- **Normalisation answers every atom exactly as before.** -/
theorem Atom.Sat_normalize {kb : KB} (hv : kb.valid = true) (hv' : kb.normalize.valid = true)
    (g : String → Qid) (a : Atom) : a.Sat kb.normalize hv' g ↔ a.Sat kb hv g := by
  cases a <;>
    simp [Atom.Sat, Ontology.SubclassOf, Ontology.InstanceOf, Ontology.IsClass,
      KB.normalize_Sub_eq, KB.normalize_Inst_eq]

/-- **Normalisation answers every query exactly as before.** -/
theorem Sat_normalize {kb : KB} (hv : kb.valid = true) (hv' : kb.normalize.valid = true)
    (g : String → Qid) (q : BGP) : Sat kb.normalize hv' g q ↔ Sat kb hv g q := by
  constructor <;> intro h a ha
  · exact (Atom.Sat_normalize hv hv' g a).1 (h a ha)
  · exact (Atom.Sat_normalize hv hv' g a).2 (h a ha)

/-- An atom that only asks about the *derived* relations (or about nothing at all, in
the case of a disequality). -/
def Atom.derivedOnly : Atom → Bool
  | .sub _ _ | .inst _ _ | .ne _ _ => true
  | .dsub _ _ | .dinst _ _ | .isClass _ => false

/-- **Monotonicity**: a knowledge base that entails another satisfies every atom about
the derived relations that the other satisfies. -/
theorem Atom.Sat_of_entails {kb kb' : KB} (hv : kb.valid = true) (hv' : kb'.valid = true)
    (hent : kb'.Entails kb = true) {a : Atom} (ha : a.derivedOnly = true) {g : String → Qid}
    (h : a.Sat kb hv g) : a.Sat kb' hv' g := by
  have hwf := KB.valid_wellFormed hv
  have hwf' := KB.valid_wellFormed hv'
  cases a with
  | sub s o =>
      rw [Atom.Sat, ← KB.isSubclassOf_iff_subclassOf hv'] at *
      exact KB.entails_subclass hwf' hwf hent ((KB.isSubclassOf_iff_subclassOf hv _ _).2 h)
  | inst s o =>
      rw [Atom.Sat, ← KB.isInstanceOf_iff_instanceOf hv'] at *
      exact KB.entails_instance hwf' hwf hent ((KB.isInstanceOf_iff_instanceOf hv _ _).2 h)
  | ne s o => exact h
  | dsub s o => simp [Atom.derivedOnly] at ha
  | dinst s o => simp [Atom.derivedOnly] at ha
  | isClass s => simp [Atom.derivedOnly] at ha

/-- Monotonicity, for a whole query. -/
theorem Sat_of_entails {kb kb' : KB} (hv : kb.valid = true) (hv' : kb'.valid = true)
    (hent : kb'.Entails kb = true) {q : BGP} (hq : ∀ a ∈ q, a.derivedOnly = true)
    {g : String → Qid} (h : Sat kb hv g q) : Sat kb' hv' g q :=
  fun a ha => Atom.Sat_of_entails hv hv' hent (hq a ha) (h a ha)

/-- **Importing a knowledge base keeps every answer**: what the left-hand base answered
about the derived relations, the merge answers too. -/
theorem Sat_merge_left {kb kb' : KB} (hv : kb.valid = true) (hwf' : kb'.wellFormed = true)
    (hvm : (kb.merge kb').valid = true) {q : BGP} (hq : ∀ a ∈ q, a.derivedOnly = true)
    {g : String → Qid} (h : Sat kb hv g q) : Sat (kb.merge kb') hvm g q :=
  Sat_of_entails hv hvm (KB.merge_entails_left (KB.valid_wellFormed hv) hwf') hq h

/-- ... and so does the right-hand base. -/
theorem Sat_merge_right {kb kb' : KB} (hwf : kb.wellFormed = true) (hv' : kb'.valid = true)
    (hvm : (kb.merge kb').valid = true) {q : BGP} (hq : ∀ a ∈ q, a.derivedOnly = true)
    {g : String → Qid} (h : Sat kb' hv' g q) : Sat (kb.merge kb') hvm g q :=
  Sat_of_entails hv' hvm (KB.merge_entails_right hwf (KB.valid_wellFormed hv')) hq h

/-! ### Evaluating against a precomputed closure table

Every `subclass of` check recomputes the superclasses of an item.  For anything larger
than a toy fragment one wants the closure table of `RequestProject.FastEval`, computed
once and reused; `Wikidata.Query.evalT_eq_eval` says this changes no answer. -/

/-- The check of an atom, answered from a precomputed closure table. -/
def Atom.checkT (kb : KB) (T : List (Qid × Finset Qid)) (e : Env) : Atom → Bool
  | .sub s o => checkBin e s o (kb.isSubclassOfT T)
  | .inst s o => checkBin e s o (kb.isInstanceOfT T)
  | .dsub s o => checkBin e s o (fun x y => decide ((x, y) ∈ kb.sub))
  | .dinst s o => checkBin e s o (fun x y => decide ((x, y) ∈ kb.inst))
  | .isClass s => checkUn e s kb.isClassB
  | .ne s o => checkBin e s o (fun x y => decide (x ≠ y))

/-- All the ways of extending a binding to one satisfying the atom, against a table. -/
def stepAtomT (kb : KB) (T : List (Qid × Finset Qid)) (a : Atom) (e : Env) : List Env :=
  (extendVars kb a.vars e).filter (fun e' => a.checkT kb T e')

/-- Evaluate a query from a partial binding, against a table. -/
def evalFromT (kb : KB) (T : List (Qid × Finset Qid)) : BGP → Env → List Env
  | [], e => [e]
  | a :: as, e => (stepAtomT kb T a e).flatMap (fun e' => evalFromT kb T as e')

/-- The evaluator, run against a precomputed closure table. -/
def evalT (kb : KB) (q : BGP) : List Env := evalFromT kb kb.closureTable q []

/-- The answers of the table-based evaluator, projected onto the output variables. -/
def answersT (kb : KB) (q : BGP) (outs : List String) : List (List Qid) :=
  ((evalT kb q).map (fun e => outs.filterMap (fun n => e.lookup n))).dedup

@[simp] theorem checkT_closureTable (kb : KB) (e : Env) (a : Atom) :
    a.checkT kb kb.closureTable e = a.check kb e := by
  cases a <;> simp [Atom.checkT, Atom.check, checkBin, checkUn]

theorem stepAtomT_closureTable (kb : KB) (a : Atom) (e : Env) :
    stepAtomT kb kb.closureTable a e = stepAtom kb a e := by
  simp [stepAtomT, stepAtom]

theorem evalFromT_closureTable (kb : KB) (q : BGP) (e : Env) :
    evalFromT kb kb.closureTable q e = evalFrom kb q e := by
  induction q generalizing e with
  | nil => rfl
  | cons a as ih =>
      rw [evalFromT, evalFrom, stepAtomT_closureTable]
      exact List.flatMap_congr fun e' _ => ih e'

/-- **Using the closure table changes no answer.** -/
theorem evalT_eq_eval (kb : KB) (q : BGP) : evalT kb q = eval kb q :=
  evalFromT_closureTable kb q []

/-- ... and neither does it change the projected answers. -/
theorem answersT_eq_answers (kb : KB) (q : BGP) (outs : List String) :
    answersT kb q outs = answers kb q outs := by
  simp [answersT, answers, evalT_eq_eval]

/-! ### Queries against the worked Wikidata fragment

The knowledge base is `Wikidata.Examples.wdCore`: Douglas Adams (`Q42`) is a human
(`Q5`), humans are persons (`Q215627`), persons are entities (`Q35120`), `human` is an
instance of the metaclass `Q55983715`, which is an instance of `Q19478619`, and `film`
(`Q11424`) is a class with no instances. -/

section Demo

open Wikidata.Examples

/-- `?x` ranges over the instances of `entity`. -/
def qInstancesOfEntity : BGP := [Atom.inst (.var "x") (.item (Q "Q35120"))]

/-- Only Douglas Adams is an instance of `entity`, even though no statement says so:
the answer is found through the chain `human ⊑ person ⊑ entity`. -/
theorem answers_qInstancesOfEntity :
    answers wdCore qInstancesOfEntity ["x"] = [[Q "Q42"]] := by decide

/-- The single answer, as a binding. -/
theorem eval_qInstancesOfEntity : eval wdCore qInstancesOfEntity = [[("x", Q "Q42")]] := by
  decide

/-- The answer is correct in the abstract ontology: any assignment sending `?x` to
Douglas Adams satisfies the query. -/
theorem sat_qInstancesOfEntity (g : String → Qid) (hg : g "x" = Q "Q42") :
    Sat wdCore wdCore_valid g qInstancesOfEntity := by
  refine eval_sat wdCore wdCore_valid qInstancesOfEntity (e := [("x", Q "Q42")]) ?_ ?_
  · rw [eval_qInstancesOfEntity]; simp
  · intro n v hn
    have hn' : n = "x" ∧ v = Q "Q42" := by
      by_cases h : n = "x"
      · subst h; simpa using hn.symm
      · rw [lookup_cons_ne [] "x" n (Q "Q42") h] at hn; simp at hn
    obtain ⟨rfl, rfl⟩ := hn'
    exact hg

/-- ... and it is the only answer: an item of the knowledge base satisfying the query
*has* to be Douglas Adams.  This is completeness of the evaluator in action. -/
theorem unique_instance_of_entity (g : String → Qid) (hg : g "x" ∈ wdCore.items)
    (hsat : Sat wdCore wdCore_valid g qInstancesOfEntity) : g "x" = Q "Q42" := by
  have hitems : ∀ n ∈ bgpVars qInstancesOfEntity, g n ∈ wdCore.items := by
    intro n hn
    have : n = "x" := by simpa [qInstancesOfEntity, bgpVars, Atom.vars, Tm.vars] using hn
    subst this; exact hg
  obtain ⟨e, he, hag, -⟩ :=
    eval_complete wdCore wdCore_valid qInstancesOfEntity g hsat hitems
  rw [eval_qInstancesOfEntity] at he
  have : e = [("x", Q "Q42")] := by simpa using he
  subst this
  exact hag "x" (Q "Q42") (by simp)

/-- A join on two variables: the two-step `subclass of` chains ending at `entity`,
using only directly asserted statements. -/
def qSubChain : BGP :=
  [Atom.dsub (.var "x") (.var "y"), Atom.dsub (.var "y") (.item (Q "Q35120"))]

theorem answers_qSubChain : answers wdCore qSubChain ["x", "y"] = [[Q "Q5", Q "Q215627"]] := by
  decide

/-- Classes that are themselves instances of something — the items one level below a
metaclass. -/
def qClassInstances : BGP := [Atom.inst (.var "x") (.var "c"), Atom.isClass (.var "x")]

theorem answers_qClassInstances :
    answers wdCore qClassInstances ["x", "c"] =
      [[Q "Q5", Q "Q55983715"], [Q "Q55983715", Q "Q19478619"]] := by decide

/-- The proper subclasses of `entity`. -/
def qProperSubclasses : BGP :=
  [Atom.sub (.var "x") (.item (Q "Q35120")), Atom.ne (.var "x") (.item (Q "Q35120"))]

theorem answers_qProperSubclasses :
    answers wdCore qProperSubclasses ["x"] = [[Q "Q5"], [Q "Q215627"]] := by decide

/-- Normalising the fragment answers the query exactly as before — an instance of
`Sat_normalize`. -/
theorem sat_normalize_qInstancesOfEntity (g : String → Qid) :
    Sat wdCore.normalize (normalize_valid_of_valid wdCore_valid) g qInstancesOfEntity ↔
      Sat wdCore wdCore_valid g qInstancesOfEntity :=
  Sat_normalize wdCore_valid _ g qInstancesOfEntity

/-- Importing the film fragment keeps the answer: Douglas Adams is still an instance of
`entity` in the merged base — an instance of `Sat_merge_left`. -/
theorem sat_merge_qInstancesOfEntity (g : String → Qid) (hg : g "x" = Q "Q42") :
    Sat (wdCore.merge filmKB) merged_valid g qInstancesOfEntity :=
  Sat_merge_left wdCore_valid (KB.valid_wellFormed filmKB_valid) merged_valid
    (by intro a ha; simp [qInstancesOfEntity] at ha; subst ha; rfl)
    (sat_qInstancesOfEntity g hg)

/-- `film` has no instances in the fragment, so the query for them has no answers. -/
def qInstancesOfFilm : BGP := [Atom.inst (.var "x") (.item (Q "Q11424"))]

theorem eval_qInstancesOfFilm : eval wdCore qInstancesOfFilm = [] := by decide

/-- Emptiness of the answer list is genuine unsatisfiability: nothing in the knowledge
base is an instance of `film`. -/
theorem no_instance_of_film (g : String → Qid) (hg : g "x" ∈ wdCore.items) :
    ¬ Sat wdCore wdCore_valid g qInstancesOfFilm := by
  refine (eval_eq_nil_iff wdCore wdCore_valid qInstancesOfFilm (by decide)).1
    eval_qInstancesOfFilm g ?_
  intro n hn
  have : n = "x" := by simpa [qInstancesOfFilm, bgpVars, Atom.vars, Tm.vars] using hn
  subst this; exact hg

end Demo

end Query
end Wikidata
