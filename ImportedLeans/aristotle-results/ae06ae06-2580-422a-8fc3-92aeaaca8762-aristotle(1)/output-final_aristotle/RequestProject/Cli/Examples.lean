import RequestProject.Cli.Tool

/-!
# A worked example of the command line tool

The checks the `wikidata` tool performs, run here at compile time on a small
fragment: Douglas Adams (Q42) is a human (Q5), humans are persons (Q215627), and
persons are omnivores (Q164509) and natural persons (Q154954).

Everything below is either decided by the kernel (`by decide`) or an instance of
the general theorems proved in `RequestProject.Cli.*`.
-/

namespace Wikidata
namespace Cli
namespace Demo

open Lean (Json)

/-- A Wikidata entity, by its QID. -/
def Q (s : String) : Qid := .wd s

/-- The fragment, as the `import` command would build it from JSON. -/
def demoEntities : List Entity :=
  [ { id := "Q42", label := "Douglas Adams", claims := [("P31", "Q5")] },
    { id := "Q5", label := "human", claims := [("P279", "Q215627")] },
    { id := "Q215627", label := "person",
      claims := [("P279", "Q164509"), ("P279", "Q154954")] } ]

/-- The knowledge base built from those entities. -/
def demoKB : KB := kbOfEntities "demo" demoEntities

/-- Levels are inferred as `0` for Douglas Adams and `1` for the classes above him. -/
example : demoKB.levelOf (Q "Q42") = 0 := by decide
example : demoKB.levelOf (Q "Q5") = 1 := by decide
example : demoKB.levelOf (Q "Q215627") = 1 := by decide

/-- The imported base is well-formed — an instance of the general theorem. -/
example : demoKB.wellFormed = true := kbOfEntities_wellFormed _ _

/-- Here the inferred levels are right, so the base is valid outright. -/
example : demoKB.valid = true := by decide

/-- Inheritance is computed, not stated: Douglas Adams is a person. -/
example : demoKB.isInstanceOf (Q "Q42") (Q "Q215627") = true := by decide

/-- `derive` finds exactly the facts that follow but are not stated. -/
example : demoKB.newSubL = [(Q "Q5", Q "Q164509"), (Q "Q5", Q "Q154954")] := by decide

example : demoKB.newInstL =
    [(Q "Q42", Q "Q215627"), (Q "Q42", Q "Q164509"), (Q "Q42", Q "Q154954")] := by decide

/-- Saturating the base keeps it valid … -/
example : demoKB.saturate.valid = true := by decide

/-- … and a second pass finds nothing new. -/
example : demoKB.saturate.newSubL = [] :=
  KB.newSubL_saturate (kbOfEntities_wellFormed _ _)

example : demoKB.saturate.newInstL = [] :=
  KB.newInstL_saturate (kbOfEntities_wellFormed _ _)

/-- `check` reports nothing on this base. -/
example : demoKB.errors = [] := by decide

/-- `why Q5 Q154954` prints this chain, and it really is a derivation. -/
example : demoKB.explainSubclass (Q "Q5") (Q "Q154954") = some [Q "Q215627", Q "Q154954"] := by
  decide

example : Relation.ReflTransGen demoKB.Sub (Q "Q5") (Q "Q154954") :=
  KB.explainSubclass_derives (cs := [Q "Q215627", Q "Q154954"]) (by decide)

/-- Saving and re-reading the base returns it unchanged — an instance of
`Cli.parseKB?_renderKB`. -/
example : parseKB? (renderKB demoKB) = some demoKB := parseKB?_renderKB _ (by decide)

/-! ### Queries from the shell

`wikidata query FILE.wdkb 'inst ?x Q5'` reads its atoms with `parseAtom?` and answers
them with `Query.answersT`. -/

/-- The textual atom `inst ?x Q5` is read as the pattern it looks like. -/
example : parseAtom? "inst ?x Q5" = some (.inst (.var "x") (.item (Q "Q5"))) := by decide

/-- A whole query, as the tool receives it on the command line. -/
example : parseQuery? ["sub ?x Q154954", "ne ?x Q154954"] =
    some [.sub (.var "x") (.item (Q "Q154954")), .ne (.var "x") (.item (Q "Q154954"))] := by
  decide

/-- Printing the query and reading it back returns it — an instance of
`Cli.parseQuery?_showQuery`. -/
example : parseQuery? (showQuery [.inst (.var "x") (.item (Q "Q5"))]) =
    some [.inst (.var "x") (.item (Q "Q5"))] :=
  parseQuery?_showQuery (by decide)

/-- The answers to `inst ?x Q5`: Douglas Adams, and nobody else. -/
example : Query.answersT demoKB [.inst (.var "x") (.item (Q "Q5"))] ["x"] = [[Q "Q42"]] := by
  decide

/-- The classes strictly below `Q154954`, with the answers of the table-based evaluator
equal to those of the evaluator the theorems are about (`Query.answersT_eq_answers`). -/
example :
    Query.answersT demoKB
      [.sub (.var "x") (.item (Q "Q154954")), .ne (.var "x") (.item (Q "Q154954"))] ["x"] =
    [[Q "Q5"], [Q "Q215627"]] := by decide

/-! ### The same fragment as Wikidata JSON

`fetch` and `import` read documents of this shape. -/

/-- A miniature `Special:EntityData` document. -/
def demoJson : String :=
  "{\"entities\":{\"Q42\":{\"id\":\"Q42\"," ++
  "\"labels\":{\"en\":{\"language\":\"en\",\"value\":\"Douglas Adams\"}}," ++
  "\"claims\":{\"P31\":[{\"mainsnak\":{\"snaktype\":\"value\",\"property\":\"P31\"," ++
  "\"datavalue\":{\"value\":{\"entity-type\":\"item\",\"id\":\"Q5\"}," ++
  "\"type\":\"wikibase-entityid\"}},\"rank\":\"normal\"}]}}}}"

-- Parsing the JSON yields the expected entity.
#eval (Json.parse demoJson).toOption.map entitiesOfJson

-- … and the expected knowledge base.
#eval (kbOfJsonString "demo" demoJson).toOption.map fun kb => (kb.items.length, kb.inst)

-- The text the `--out` option writes.
#eval IO.println (renderKB demoKB)

/-! ### A base with a series layer

`wikidata scheck FILE.skb` and `wikidata series FILE.skb Q` work on files carrying the
three series record kinds as well.  The worked series of `RequestProject.SeriesExamples`
is the content of [`examples/trilogy.skb`](../../examples/trilogy.skb). -/

/-- `scheck` is silent on it: base and series layer are both valid. -/
example : SKB.trilogySKB.base.errors = [] ∧ SKB.trilogySKB.sErrors = [] := by decide

/-- `series … v2` walks the series from its first element; this is what it prints. -/
example : SKB.trilogySKB.chainFrom (Qid.wd "v1") = [Qid.wd "v1", Qid.wd "v2", Qid.wd "v3"] := by
  decide

/-- `v1` is the element the walk starts from: the unique origin of the series. -/
example : SKB.trilogySKB.originsOfL (Qid.wd "v2") = [Qid.wd "v1"] := by decide

/-- Saving and re-reading the series layer returns it unchanged — an instance of
`Cli.parseSKB?_renderSKB`. -/
example : parseSKB? (renderSKB SKB.trilogySKB) = some SKB.trilogySKB :=
  parseSKB?_renderSKB _ (by decide)

-- The text `wikidata scheck` reads, and `--out` writes.
#eval IO.println (renderSKB SKB.trilogySKB)

end Demo
end Cli
end Wikidata
