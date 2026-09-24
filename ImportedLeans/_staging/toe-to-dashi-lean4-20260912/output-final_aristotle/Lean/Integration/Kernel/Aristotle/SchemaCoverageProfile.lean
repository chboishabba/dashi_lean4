import Integration.Kernel.PartialIdentification
import RequestProject.Schemas

/-!
# Aristotle instantiation: named coverage schemas and per-query closure

The archive module `RequestProject.Schemas` carries an executable entity-schema
layer: `Shape` (a list of cardinality constraints, possibly closed) and
`conformsB`.  This file uses it to replace ad-hoc "required property id" lists
by a **named finite coverage schema**, and connects the result to the compatible
fibre of `Integration.Kernel.PartialIdentification`.

The shape of the result is deliberately *per query*:

  `Conforms(item, C) ∧ CoversQuery(C, q) → QueryCoverageSatisfied(item, q)`

and emphatically **not** global item completeness.

## What is proved

* `CoversQuery` — a coverage schema covers a query when it demands at least one
  statement for the queried property.
* **`conformance_gives_query_coverage`** — the positive law, general in the
  knowledge base, the schema, the item and the query: conformance plus coverage
  of the query gives a non-empty statement family for that query.  Proved
  through the archive's `conformsB_iff` and `specOkB_iff`.
* **`schema_complete_for_one_query_is_not_complete_for_every_query`** — the
  boundary: an item conforming to a coverage schema, with a query the schema
  does not cover and for which the item has no statements at all.
* **`coverage_closes_a_consumer_on_a_nonsingleton_fibre`** — the crossing with
  partial identification: two different knowledge bases conform to the same
  coverage schema and agree on the covered query's answer while differing
  elsewhere, so the schema closes that consumer without identifying the item.

**Claim boundary.**  `layerA`, `layerB` and `birthShape` are finite fixtures
defined here; `Shape`, `conformsB`, `countOf` and the two characterisation
lemmas are the archive's.  A coverage schema is a syntactic object: conformance
is a statement about the knowledge base, not about the world.
-/

namespace Integration.Kernel.Aristotle.SchemaCoverageProfile

open Integration.Kernel

/-! ## §1 Coverage of a query by a schema -/

/-- A schema **covers** a query — here, a property whose statement family the
consumer reads — when it demands at least one statement for it. -/
def CoversQuery (sh : Wikidata.Shape) (q : Wikidata.Pid) : Prop :=
  ∃ c ∈ sh.specs, c.prop = q ∧ 1 ≤ c.minCard

/-- **Conformance to a covering schema satisfies the query's coverage
obligation.**  General in the knowledge base, the schema, the item and the
query. -/
theorem conformance_gives_query_coverage {pkb : Wikidata.PKB} {sh : Wikidata.Shape}
    {s : Wikidata.Qid} {q : Wikidata.Pid} (hconf : pkb.conformsB sh s = true)
    (hcov : CoversQuery sh q) : 0 < pkb.countOf q s := by
  obtain ⟨c, hc, hprop, hmin⟩ := hcov
  have hspec := (Wikidata.PKB.conformsB_iff.1 hconf).1 c hc
  have hle := (Wikidata.PKB.specOkB_iff.1 hspec).1
  have : 1 ≤ pkb.countOf c.prop s := le_trans hmin hle
  rw [hprop] at this
  exact this

/-! ## §2 The fixtures -/

/-- Abbreviation for an item label. -/
def Q (s : String) : Wikidata.Qid := .wd s
/-- Abbreviation for a property label. -/
def P (s : String) : Wikidata.Pid := .wd s

/-- The ontology under the two layers. -/
def base : Wikidata.KB where
  name := "coverage base"
  items := [Q "Q42", Q "V1952", Q "Q145", Q "Q30", Q "Q350", Q "Q5"]
  levels := [(Q "Q42", 0), (Q "V1952", 0), (Q "Q145", 0), (Q "Q30", 0), (Q "Q350", 0),
             (Q "Q5", 1)]
  inst := [(Q "Q42", Q "Q5")]

/-- A layer recording a date of birth and one citizenship. -/
def layerA : Wikidata.PKB where
  base := base
  props := [P "P569", P "P27", P "P19"]
  stmts := [(P "P569", Q "Q42", Q "V1952"), (P "P27", Q "Q42", Q "Q145")]

/-- A second layer with the same date of birth and citizenship and an extra
statement in a different property family. -/
def layerB : Wikidata.PKB where
  base := base
  props := [P "P569", P "P27", P "P19"]
  stmts := [(P "P569", Q "Q42", Q "V1952"), (P "P27", Q "Q42", Q "Q145"),
            (P "P19", Q "Q42", Q "Q350")]

/-- The named coverage schema for the date-of-birth consumer: at least one and
at most one `P569`, open. -/
def birthShape : Wikidata.Shape where
  sid := "coverage-P569"
  specs := [{ prop := P "P569", minCard := 1, maxCard := some 1 }]
  closed := false

theorem birthShape_covers_P569 : CoversQuery birthShape (P "P569") :=
  ⟨{ prop := P "P569", minCard := 1, maxCard := some 1 }, by simp [birthShape], rfl, le_refl 1⟩

set_option maxRecDepth 40000 in
theorem layerA_conforms : layerA.conformsB birthShape (Q "Q42") = true := by decide

set_option maxRecDepth 40000 in
theorem layerB_conforms : layerB.conformsB birthShape (Q "Q42") = true := by decide

/-! ## §3 One query closed, not every query -/

/-- The consumer's answer: the statements of the covered family. -/
def answer (pkb : Wikidata.PKB) (q : Wikidata.Pid) (s : Wikidata.Qid) :
    List (Wikidata.Pid × Wikidata.Qid × Wikidata.Qid) :=
  pkb.stmtsOf q s

/-- **A schema complete for one query is not complete for every query.**  The
item conforms, the covered query has a non-empty family, and an uncovered query
has an empty one — with no way to tell from the schema whether that emptiness is
a fact or a gap. -/
theorem schema_complete_for_one_query_is_not_complete_for_every_query :
    0 < layerA.countOf (P "P569") (Q "Q42") ∧
    layerA.countOf (P "P19") (Q "Q42") = 0 ∧
    ¬ CoversQuery birthShape (P "P19") := by
  refine ⟨conformance_gives_query_coverage layerA_conforms birthShape_covers_P569, by decide, ?_⟩
  rintro ⟨c, hc, hprop, -⟩
  simp only [birthShape, List.mem_singleton] at hc
  subst hc
  exact absurd hprop (by decide)

/-! ## §4 Crossing with the compatible fibre -/

/-- The observation a schema-driven consumer makes: the covered family. -/
def coveredObs (q : Wikidata.Pid) (s : Wikidata.Qid) (pkb : Wikidata.PKB) :
    List (Wikidata.Pid × Wikidata.Qid × Wikidata.Qid) :=
  pkb.stmtsOf q s

set_option maxRecDepth 40000 in
theorem layers_agree_on_covered_query :
    coveredObs (P "P569") (Q "Q42") layerA = coveredObs (P "P569") (Q "Q42") layerB := by decide

theorem layers_differ : layerA ≠ layerB := by
  intro h
  have : layerA.stmts = layerB.stmts := congrArg Wikidata.PKB.stmts h
  exact absurd this (by decide)

/-- **A named coverage schema closes one consumer on a non-singleton fibre.**
Both layers conform to the schema and give the covered consumer the same answer,
while the underlying knowledge base is not identified by that observation. -/
theorem coverage_closes_a_consumer_on_a_nonsingleton_fibre :
    layerA.conformsB birthShape (Q "Q42") = true ∧
    layerB.conformsB birthShape (Q "Q42") = true ∧
    coveredObs (P "P569") (Q "Q42") layerA = coveredObs (P "P569") (Q "Q42") layerB ∧
    ¬ PartialIdentification.PointIdentified (coveredObs (P "P569") (Q "Q42"))
        (coveredObs (P "P569") (Q "Q42") layerA) :=
  ⟨layerA_conforms, layerB_conforms, layers_agree_on_covered_query,
   PartialIdentification.not_pointIdentified_of_collision
     layers_agree_on_covered_query layers_differ⟩

end Integration.Kernel.Aristotle.SchemaCoverageProfile
