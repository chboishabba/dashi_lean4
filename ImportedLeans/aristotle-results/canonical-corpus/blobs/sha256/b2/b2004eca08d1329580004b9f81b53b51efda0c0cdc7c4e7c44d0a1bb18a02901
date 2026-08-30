import RequestProject.TypeProperties

/-!
# Entity schemas: cardinality shapes over the property layer

Wikidata's *EntitySchema* namespace holds schemas (written in ShEx) that say what
the statements of an item must look like: which properties it must carry, how
often, and whether anything else is allowed.  This file formalises the
cardinality core of that idea over the executable property layer
`Wikidata.PKB`:

* a `Wikidata.PropSpec` constrains one property by a minimum and an optional
  maximum number of statements;
* a `Wikidata.Shape` is a list of such constraints, possibly **closed** — a closed
  shape forbids statements with any other property;
* `PKB.conformsB` decides conformance of an item to a shape.

The results are:

* the check is characterised exactly (`conformsB_iff`), and a conforming item of a
  closed shape provably carries no statement outside the shape
  (`mem_specs_of_conformsB_closed`);
* conformance to the conjunction of two open shapes is conformance to both
  (`conformsB_meet`), so shapes form a conjunctive schema language;
* a shape with no upper bounds is **monotone**: asserting further statements never
  breaks conformance (`conformsB_addStmts`), while a maximum can of course be
  exceeded — both are exhibited on a worked fragment;
* the `properties for this type` (P1963) completeness check of
  `RequestProject.TypeProperties` is exactly conformance to the shape requiring
  one statement for each expected property
  (`completeFor_iff_conformsB_minShape`), which identifies the soft P1963
  constraint as the cardinality-`1` fragment of the schema language.
-/

namespace Wikidata

/-- A cardinality constraint on one property: at least `minCard` statements and,
if `maxCard` is given, at most that many. -/
structure PropSpec where
  /-- The constrained property. -/
  prop : Pid
  /-- The minimum number of statements required. -/
  minCard : ℕ := 0
  /-- The maximum number of statements allowed, if bounded. -/
  maxCard : Option ℕ := none
deriving Repr, DecidableEq, Inhabited

/-- An entity schema: a list of cardinality constraints, `closed` when no other
property may be used. -/
structure Shape where
  /-- The identifier of the schema, e.g. `"E10"`. -/
  sid : String
  /-- The cardinality constraints. -/
  specs : List PropSpec := []
  /-- A closed shape forbids statements with properties it does not mention. -/
  closed : Bool := false
deriving Repr, DecidableEq, Inhabited

namespace Shape

/-- The conjunction of two schemas. -/
def meet (sh th : Shape) : Shape where
  sid := sh.sid ++ "&" ++ th.sid
  specs := sh.specs ++ th.specs
  closed := sh.closed || th.closed

end Shape

namespace PKB

variable (pkb : PKB)

/-- The statements about `s` made with `p` or with a subproperty of it. -/
def stmtsOf (p : Pid) (s : Qid) : List (Pid × Qid × Qid) :=
  pkb.stmts.filter (fun t => pkb.isSubPropertyOf t.1 p && t.2.1 == s)

/-- How many statements about `s` are made with `p` (or a subproperty). -/
def countOf (p : Pid) (s : Qid) : ℕ := (pkb.stmtsOf p s).length

/-- Does the item satisfy one cardinality constraint? -/
def specOkB (c : PropSpec) (s : Qid) : Bool :=
  (c.minCard ≤ pkb.countOf c.prop s) &&
    (match c.maxCard with
      | none => true
      | some m => pkb.countOf c.prop s ≤ m)

/-- Does the item use only properties mentioned by the shape? -/
def usesOnlyB (sh : Shape) (s : Qid) : Bool :=
  pkb.stmts.all fun t =>
    !(t.2.1 == s) || sh.specs.any (fun c => pkb.isSubPropertyOf t.1 c.prop)

/-- Conformance of an item to an entity schema. -/
def conformsB (sh : Shape) (s : Qid) : Bool :=
  sh.specs.all (fun c => pkb.specOkB c s) && (!sh.closed || pkb.usesOnlyB sh s)

/-- The schema obtained by asserting further statements. -/
def addStmts (ts : List (Pid × Qid × Qid)) : PKB := { pkb with stmts := pkb.stmts ++ ts }

variable {pkb}

theorem mem_stmtsOf {p : Pid} {s : Qid} {t : Pid × Qid × Qid} :
    t ∈ pkb.stmtsOf p s ↔ t ∈ pkb.stmts ∧ pkb.isSubPropertyOf t.1 p = true ∧ t.2.1 = s := by
  simp [stmtsOf, List.mem_filter]

theorem conformsB_iff {sh : Shape} {s : Qid} :
    pkb.conformsB sh s = true ↔
      (∀ c ∈ sh.specs, pkb.specOkB c s = true) ∧
        (sh.closed = true → pkb.usesOnlyB sh s = true) := by
  simp only [conformsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hc => ?_⟩
    rcases h2 with h2 | h2
    · exact absurd hc (by simp [h2])
    · exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hc : sh.closed = true
    · exact Or.inr (h2 hc)
    · exact Or.inl (by simpa using hc)

theorem specOkB_iff {c : PropSpec} {s : Qid} :
    pkb.specOkB c s = true ↔
      c.minCard ≤ pkb.countOf c.prop s ∧ ∀ m, c.maxCard = some m → pkb.countOf c.prop s ≤ m := by
  cases hm : c.maxCard with
  | none => simp [specOkB, hm]
  | some m => simp [specOkB, hm]

/-- **A closed shape really is closed**: every statement about a conforming item is
made with a property the shape mentions. -/
theorem mem_specs_of_conformsB_closed {sh : Shape} {s : Qid} (hcl : sh.closed = true)
    (h : pkb.conformsB sh s = true) {q : Pid} {o : Qid} (hst : (q, s, o) ∈ pkb.stmts) :
    ∃ c ∈ sh.specs, pkb.isSubPropertyOf q c.prop = true := by
  have hu := (conformsB_iff.1 h).2 hcl
  simp only [usesOnlyB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, List.any_eq_true] at hu
  rcases hu (q, s, o) hst with h1 | h1
  · exact absurd rfl h1
  · exact h1

/-- **Conjunction of schemas**: for open shapes, conforming to the conjunction is
conforming to both. -/
theorem conformsB_meet {sh th : Shape} {s : Qid} (hs : sh.closed = false)
    (ht : th.closed = false) :
    pkb.conformsB (Shape.meet sh th) s = true ↔
      pkb.conformsB sh s = true ∧ pkb.conformsB th s = true := by
  have hcl : (Shape.meet sh th).closed = false := by simp [Shape.meet, hs, ht]
  rw [conformsB_iff, conformsB_iff, conformsB_iff]
  simp only [hs, ht, Bool.or_self, Bool.false_eq_true, false_implies, and_true, Shape.meet,
    List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-! ### Monotonicity -/

@[simp] theorem addStmts_isSubPropertyOf (ts : List (Pid × Qid × Qid)) (p q : Pid) :
    (pkb.addStmts ts).isSubPropertyOf p q = pkb.isSubPropertyOf p q := rfl

theorem stmtsOf_addStmts (ts : List (Pid × Qid × Qid)) (p : Pid) (s : Qid) :
    (pkb.addStmts ts).stmtsOf p s =
      pkb.stmtsOf p s ++ ts.filter (fun t => pkb.isSubPropertyOf t.1 p && t.2.1 == s) := by
  simp only [stmtsOf, addStmts, List.filter_append]
  rfl

theorem countOf_le_addStmts (ts : List (Pid × Qid × Qid)) (p : Pid) (s : Qid) :
    pkb.countOf p s ≤ (pkb.addStmts ts).countOf p s := by
  simp [countOf, stmtsOf_addStmts]

/-- **Shapes without upper bounds are monotone**: asserting further statements never
breaks conformance to an open shape all of whose constraints are lower bounds. -/
theorem conformsB_addStmts {sh : Shape} {s : Qid} (hopen : sh.closed = false)
    (hmax : ∀ c ∈ sh.specs, c.maxCard = none) (ts : List (Pid × Qid × Qid))
    (h : pkb.conformsB sh s = true) : (pkb.addStmts ts).conformsB sh s = true := by
  refine conformsB_iff.2 ⟨fun c hc => ?_, by simp [hopen]⟩
  have hmin := (specOkB_iff.1 ((conformsB_iff.1 h).1 c hc)).1
  refine specOkB_iff.2 ⟨le_trans hmin (countOf_le_addStmts ts c.prop s), ?_⟩
  intro m hm
  exact absurd (hmax c hc) (by rw [hm]; simp)

end PKB

namespace Profile

variable {pf : Profile}

/-- The schema requiring at least one statement for each of the listed properties. -/
def minShape (ps : List Pid) : Shape where
  sid := "min-one"
  specs := ps.map (fun p => { prop := p, minCard := 1 })
  closed := false

theorem hasPropertyB_iff_countOf_pos {a : Qid} {p : Pid} :
    pf.hasPropertyB a p = true ↔ 0 < pf.base.countOf p a := by
  rw [hasPropertyB_iff]
  simp only [PKB.countOf, List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨q, o, hmem, hsub⟩
    exact ⟨(q, a, o), PKB.mem_stmtsOf.2 ⟨hmem, hsub, rfl⟩⟩
  · rintro ⟨⟨q, s, o⟩, ht⟩
    obtain ⟨hmem, hsub, rfl⟩ := PKB.mem_stmtsOf.1 ht
    exact ⟨q, o, hmem, hsub⟩

/-- **The P1963 completeness check is a schema**: an item is complete for its
modelling profile exactly when it conforms to the schema demanding one statement
for each expected property. -/
theorem completeFor_iff_conformsB_minShape {a : Qid} :
    pf.completeFor a = true ↔ pf.base.conformsB (minShape (pf.expectedOf a)) a = true := by
  rw [completeFor_iff, PKB.conformsB_iff]
  simp only [minShape, List.mem_map, Bool.false_eq_true, false_implies, and_true]
  constructor
  · rintro h c ⟨p, hp, rfl⟩
    refine PKB.specOkB_iff.2 ⟨?_, by simp⟩
    have := hasPropertyB_iff_countOf_pos.1 (h p hp)
    simpa using this
  · intro h p hp
    have := (PKB.specOkB_iff.1 (h { prop := p, minCard := 1 } ⟨p, hp, rfl⟩)).1
    exact hasPropertyB_iff_countOf_pos.2 (by simpa using this)

end Profile

/-! ## A worked fragment

A schema for humans: exactly one `date of birth` (P569), at least one
`country of citizenship` (P27), and nothing else. -/

namespace SchemaExample

open PKB

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a Wikidata property. -/
def P (s : String) : Pid := .wd s

/-- The items: two people, a date, a country and the class `human`. -/
def base : KB where
  name := "wd-schema"
  items := [Q "Q42", Q "Q7", Q "V1952", Q "V1961", Q "Q145", Q "Q5"]
  levels := [(Q "Q42", 0), (Q "Q7", 0), (Q "V1952", 0), (Q "V1961", 0), (Q "Q145", 0),
             (Q "Q5", 1)]
  inst := [(Q "Q42", Q "Q5"), (Q "Q7", Q "Q5")]

set_option maxRecDepth 40000 in
theorem base_valid : base.valid = true := by decide

/-- Douglas Adams has one date of birth and one citizenship; the second item has
two conflicting dates of birth and no citizenship. -/
def layer : PKB where
  base := base
  props := [P "P569", P "P27"]
  stmts := [(P "P569", Q "Q42", Q "V1952"), (P "P27", Q "Q42", Q "Q145"),
            (P "P569", Q "Q7", Q "V1952"), (P "P569", Q "Q7", Q "V1961")]

/-- The schema: exactly one date of birth, at least one citizenship, closed. -/
def humanShape : Shape where
  sid := "E10"
  specs := [{ prop := P "P569", minCard := 1, maxCard := some 1 },
            { prop := P "P27", minCard := 1 }]
  closed := true

set_option maxRecDepth 40000 in
theorem adams_conforms : layer.conformsB humanShape (Q "Q42") = true := by decide

set_option maxRecDepth 40000 in
/-- The second item violates both the maximum on `date of birth` and the minimum on
`country of citizenship`. -/
theorem other_fails : layer.conformsB humanShape (Q "Q7") = false := by decide

/-- The open, lower-bound-only part of the schema. -/
def humanShapeOpen : Shape where
  sid := "E10-open"
  specs := [{ prop := P "P569", minCard := 1 }, { prop := P "P27", minCard := 1 }]

set_option maxRecDepth 40000 in
theorem adams_conforms_open : layer.conformsB humanShapeOpen (Q "Q42") = true := by decide

/-- Monotonicity in action: further statements keep the open schema satisfied. -/
theorem adams_still_conforms_open :
    (layer.addStmts [(P "P27", Q "Q42", Q "Q30")]).conformsB humanShapeOpen (Q "Q42") = true :=
  PKB.conformsB_addStmts rfl (by decide) _ adams_conforms_open

set_option maxRecDepth 40000 in
/-- The *closed* schema, by contrast, is broken by a statement it does not mention,
and the bounded one by a second date of birth. -/
theorem adams_breaks_closed :
    (layer.addStmts [(P "P19", Q "Q42", Q "Q350")]).conformsB humanShape (Q "Q42") = false := by
  decide

set_option maxRecDepth 40000 in
theorem adams_breaks_max :
    (layer.addStmts [(P "P569", Q "Q42", Q "V1961")]).conformsB humanShape (Q "Q42")
      = false := by decide

end SchemaExample

end Wikidata
