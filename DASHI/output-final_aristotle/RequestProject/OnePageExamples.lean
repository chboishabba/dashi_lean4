/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.OnePage
import RequestProject.Generated.DouglasAdams

/-!
# The single page report on the worked fragment

`RequestProject.OnePage` says what the self-contained HTML page guarantees in the
abstract.  This file runs those guarantees on the downloaded fragment about Douglas
Adams — the same data the rest of the development uses — so that what the page does
is exhibited on real rows rather than only in general:

* the fragment is *web safe*: every field of every published row can be inlined
  verbatim, so nothing has to be altered to embed it;
* the text a browser reads back out of the fragment's data block is the fragment's
  JSON Lines, character for character, and parsing it returns the fragment itself;
* the same holds for a two-ontology corpus;
* no `<` survives in a data block, whatever the data — so a block can neither close
  its element nor open a tag;
* the chart of the fragment has one bar per kind of row, and its bars account for
  every published row but the header and the levels;
* a one-variable query answers with exactly the items that satisfy it, here: the
  four classes Douglas Adams is an instance of, derived through `subclass of`.
-/

namespace Wikidata
namespace OnePageExamples

open Wikidata.Cli Wikidata.Publish Wikidata.OnePage

/-- The worked fragment: what `wikidata fetch Q42 --depth 3` downloaded. -/
abbrev douglas : KB := Generated.DouglasAdams.kb

/-! ### The fragment can be embedded verbatim -/

/-- Every field of every published row is safe to inline in the page. -/
theorem douglas_webSafe : webSafeKB douglas = true := by native_decide

/-- **What the browser reads out of the page is the fragment.** -/
theorem douglas_block_roundTrip :
    parseJsonl? (blockPayload douglas.name (dataBlock douglas.name (jsonlOfKB douglas)))
      = some douglas :=
  parseJsonl?_blockPayload_dataBlock douglas_webSafe douglas.name

/-- The data block carries the published rows unchanged: sanitising them is the
identity. -/
theorem douglas_block_payload :
    blockPayload douglas.name (dataBlock douglas.name (jsonlOfKB douglas))
      = jsonlOfKB douglas := by
  rw [blockPayload_dataBlock, sanitize_eq_self (scriptSafeB_jsonlOfKB douglas_webSafe)]

/-- A block cannot close its element nor open a tag: no `<` survives. -/
theorem douglas_block_inert : lt ∉ (sanitize (jsonlOfKB douglas)).toList :=
  lt_notMem_sanitize _

/-! ### A two-ontology corpus -/

/-- A second, tiny ontology, to make a corpus of two. -/
def tiny : KB :=
  { name := "tiny"
    items := [.wd "Q5", .wd "Q215627"]
    levels := [(.wd "Q5", 1), (.wd "Q215627", 1)]
    sub := [(.wd "Q5", .wd "Q215627")] }

theorem tiny_webSafe : webSafeKB tiny = true := by native_decide

/-- **The whole corpus round-trips**: reading the two embedded documents back
returns the two ontologies, in order. -/
theorem corpus_roundTrip :
    parseDocs? ((docs [douglas, tiny]).map sanitize) = some [douglas, tiny] := by
  refine parseDocs?_sanitize_docs ?_
  intro kb hkb
  rcases List.mem_cons.1 hkb with rfl | hkb
  · exact douglas_webSafe
  · rcases List.mem_cons.1 hkb with rfl | hkb
    · exact tiny_webSafe
    · simp at hkb

/-- One embedded document per ontology. -/
example : (docs [douglas, tiny]).length = 2 := length_docs _

/-! ### The charts -/

/-- The chart of the fragment: 21 items, 12 `subclass of`, 9 `instance of`, no
disjointness. -/
theorem douglas_bars :
    (kbBars douglas).map Report.Bar.count = [21, 12, 9, 0] := by native_decide

/-- **The bars account for every published row** but the header and the declared
levels, as `kbBars_count_sum` says in general: 21 + 12 + 9 + 0, plus the header and
the 21 levels, is the 64 rows the fragment publishes. -/
example :
    ((kbBars douglas).map Report.Bar.count).sum + 1 + douglas.levels.length
      = (kbRecs douglas).length := kbBars_count_sum douglas

theorem douglas_rows_from_bars : (kbRecs douglas).length = 64 := by native_decide

/-- The corpus chart has one bar per ontology… -/
example : (corpusBars [douglas, tiny]).length = 2 := corpusBars_length _

/-- …and its bars add up to the whole corpus. -/
example :
    ((corpusBars [douglas, tiny]).map Report.Bar.count).sum
      = ([douglas, tiny].map fun kb => kb.items.length).sum :=
  corpusBars_count_sum _

/-- The drawing has one line per bar (`Report.svgBarLines_length`). -/
example : (Report.svgBarLines (corpusBars [douglas, tiny])).length = 2 :=
  corpusChart_lines _

/-! ### A query the page ships an answer for -/

/-- Douglas Adams (Q42) is an instance of twelve classes of the fragment: `human`
(Q5) and, through `subclass of`, everything above it. -/
theorem douglas_classes :
    probeAnswers douglas [.inst (.item (.wd "Q42")) (.var "c")] ["c"] =
      [[.wd "Q5"], [.wd "Q2250224"], [.wd "Q215627"], [.wd "Q795052"], [.wd "Q164509"],
       [.wd "Q72638"], [.wd "Q729"], [.wd "Q154954"], [.wd "Q3778211"],
       [.wd "Q106559804"], [.wd "Q5891007"], [.wd "Q15978631"]] := by native_decide

/-- The items the query `inst ?x Q5` returns in the fragment: Douglas Adams alone. -/
theorem douglas_humans :
    probeAnswers douglas [.inst (.var "x") (.item (.wd "Q5"))] ["x"] = [[.wd "Q42"]] := by
  native_decide

/-- **And that answer means what it says**: an item of the fragment is returned by
`inst ?x Q5` exactly when it is an instance of `human` in the abstract ontology
(`mem_probe_iff`, on a base the validator accepts). -/
example (hv : douglas.valid = true) (x : Qid) (hx : x ∈ douglas.items) :
    (∃ e ∈ Query.eval douglas [.inst (.var "x") (.item (.wd "Q5"))], e.lookup "x" = some x) ↔
      Query.Sat douglas hv (fun _ => x) [.inst (.var "x") (.item (.wd "Q5"))] :=
  mem_probe_iff douglas hv _ "x" rfl x hx

end OnePageExamples
end Wikidata
