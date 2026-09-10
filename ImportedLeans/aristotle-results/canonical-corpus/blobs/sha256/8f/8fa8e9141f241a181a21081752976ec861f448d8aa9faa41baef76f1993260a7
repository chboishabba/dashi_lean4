import RequestProject.RepairReview
import RequestProject.SeriesRepair
import RequestProject.Cli.ReportCmd

/-!
# `wikidata repairs` — the patch review of a stored base

`wikidata report` says what is wrong with a base and `wikidata fix` performs the
two repairs the library had proved safe.  This command does the third thing a
clean-up project needs: for **every** flagged issue it writes down a concrete
change, the reason for it, and the verdict of the check — and then applies
nothing.

```
wikidata repairs data/douglas.wdkb --out docs/repairs
  → docs/repairs/douglas.csv    one row per candidate repair
  → docs/repairs/douglas.html   the same, as a page, with the summary
  → docs/repairs/douglas.txt    the same, as a plain text patch review
  → docs/repairs/douglas-repaired.wdkb   (with --out-base) the candidate base
```

Everything the files say is backed by `RequestProject.RepairWorkflow`: every
flagged issue has a candidate (`Wikidata.KB.plan_covers`), a line marked `proven`
really removes its issue and introduces no error or warning
(`Wikidata.KB.proven_no_regression`) and really lowers the repair debt
(`Wikidata.KB.proven_scoreAfter_lt`), and whatever subset of the recommendations
is eventually applied, the result carries no error the base did not already carry
(`Wikidata.KB.applyProposals_errors_subset`).  The command computes the review
through the closure tables (`Wikidata.KB.reviewItemsFast_eq`), which is the same
review.
-/

namespace Wikidata
namespace Cli

/-- The three files of a patch review. -/
def writeRepairReview (prefixPath : String) (title : String) (source : String)
    (kb : KB) (items : List ReviewItem) (debtNow debtAfter : ℕ) : IO Unit := do
  let intro :=
    s!"{items.length} candidate repair(s) for {kb.name} ({source}); " ++
    s!"{countVerdict items .proven} recommended, {countVerdict items .rejected} left for review. " ++
    "Nothing has been applied: this is a proposal to read and act on by hand."
  IO.FS.writeFile (prefixPath ++ ".csv") (reviewCsvOf items ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".html") (reviewHtmlOf title intro items debtNow debtAfter ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".txt")
    (reviewTextOf kb.name items debtNow debtAfter ++ "\n")

/-- The three files of a patch review covering **both** layers of a stored base:
the ontology candidates of `Wikidata.KB.reviewItems` and the series candidates of
`Wikidata.SKB.sReviewItems`, in the same columns.  The series half is backed by
the same guarantees (`Wikidata.SKB.sProven_no_regression`,
`sProven_scoreAfter_lt`), and repairing the series layer is proved never to break
the ontology underneath (`Wikidata.SKB.sApplyProposals_base_errors_subset`). -/
def writeRepairReviewSKB (prefixPath : String) (title : String) (source : String)
    (s : SKB) (debtNow debtAfter : Nat) : IO Unit := do
  let total := s.reviewCount
  let proven := s.reviewVerdictCount .proven
  let rejected := s.reviewVerdictCount .rejected
  let intro :=
    s!"{total} candidate repair(s) for {s.base.name} ({source}); " ++
    s!"{proven} recommended, {rejected} left for review. " ++
    "Nothing has been applied: this is a proposal to read and act on by hand."
  IO.FS.writeFile (prefixPath ++ ".csv")
    (Report.csvText reviewHeader s.reviewFieldRows ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".html")
    (Report.htmlText title intro reviewHeader
      ((reviewSummaryRows total proven rejected debtNow debtAfter).map fun fs => ("", fs))
      ["measure", "value"] s.reviewHtmlRows ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".txt")
    (joinChar '\n'
      (["Proposed repairs for " ++ s.base.name,
        "candidates: " ++ Report.num total ++
          ", recommended: " ++ Report.num proven ++
          ", left for review: " ++ Report.num rejected,
        "repair debt: " ++ Report.num debtNow ++
          " → " ++ Report.num debtAfter ++ " if the recommended changes are made",
        "Nothing below has been applied."] ++ s.reviewLines) ++ "\n")

end Cli
end Wikidata
