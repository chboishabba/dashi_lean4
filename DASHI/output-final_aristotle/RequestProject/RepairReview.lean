/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.RepairWorkflow

/-!
# The patch review: what the workflow would change, and why

`RequestProject.RepairWorkflow` proposes a repair for every flagged issue and
checks it.  This file writes the result down in the form a human reviewer needs:
one row per candidate, saying which issue it addresses, exactly which statements
it would add or delete, why that is the right change, the verdict of the check,
and what it does to the repair debt of the base.

Nothing here edits anything.  The output is a *patch review*: a table to read,
argue with, and — outside the tool — apply or not.

* `Wikidata.ReviewItem` is one line of it, `Wikidata.KB.reviewItems` the review of
  a whole base;
* `Wikidata.KB.reviewItems_length` — one line per candidate, no more and no less;
* `Wikidata.KB.reviewItems_covers` — every flagged issue is on the table;
* `Wikidata.KB.reviewItems_honest` — the numbers printed in a line really are the
  repair debt before and after the change it describes, and
  `Wikidata.KB.proven_scoreAfter_lt` — a line marked `proven` really does lower
  it;
* `Wikidata.KB.reviewItem_proven_iff` — a line is marked `proven` exactly when the
  check passed, so the mark cannot be given out by the renderer;
* `Wikidata.KB.provenCount_add_rejectedCount` — the summary counts add up to the
  number of candidates;
* `Wikidata.KB.parseCsvText_reviewCsv` — the exported CSV file reads back exactly
  as written.
-/

namespace Wikidata

open Cli (qidText)
open Report (num)

/-- One line of a patch review: a candidate repair, the verdict on it, and the
repair debt before and after it. -/
structure ReviewItem where
  /-- The candidate this line is about. -/
  proposal : KB.Proposal
  /-- What the check said about it. -/
  verdict : KB.Verdict
  /-- The repair debt of the base as it stands. -/
  scoreBefore : ℕ
  /-- The repair debt the base would have after the change. -/
  scoreAfter : ℕ
deriving DecidableEq, Repr, Inhabited

namespace KB

/-- The review of a base: one line for every candidate of the plan. -/
def reviewItems (kb : KB) : List ReviewItem :=
  kb.plan.map fun p =>
    { proposal := p, verdict := kb.verdictOf p, scoreBefore := kb.score,
      scoreAfter := (kb.patch p.edits).score }

/-- **One line per candidate.** -/
@[simp] theorem reviewItems_length (kb : KB) : kb.reviewItems.length = kb.plan.length := by
  simp [reviewItems]

theorem mem_reviewItems_iff {kb : KB} {r : ReviewItem} :
    r ∈ kb.reviewItems ↔ ∃ p ∈ kb.plan, r =
      { proposal := p, verdict := kb.verdictOf p, scoreBefore := kb.score,
        scoreAfter := (kb.patch p.edits).score } := by
  simp [reviewItems, eq_comm]

/-- **Every flagged issue is on the review table.** -/
theorem reviewItems_covers {kb : KB} {i : Issue} (h : i ∈ kb.flagged) :
    ∃ r ∈ kb.reviewItems, r.proposal.issue = i := by
  obtain ⟨p, hp, hpi⟩ := plan_covers h
  exact ⟨_, mem_reviewItems_iff.2 ⟨p, hp, rfl⟩, hpi⟩

/-- **The review invents no candidate**: every line addresses an issue the base
really flags. -/
theorem reviewItems_issue_flagged {kb : KB} {r : ReviewItem} (h : r ∈ kb.reviewItems) :
    r.proposal.issue ∈ kb.flagged := by
  obtain ⟨p, hp, rfl⟩ := mem_reviewItems_iff.1 h
  exact mem_plan_issue hp

/-- **The numbers on a line are the real ones**: the debt of the base, and the
debt of the base as the line's change would leave it. -/
theorem reviewItems_honest {kb : KB} {r : ReviewItem} (h : r ∈ kb.reviewItems) :
    r.scoreBefore = kb.score ∧ r.scoreAfter = (kb.patch r.proposal.edits).score := by
  obtain ⟨p, -, rfl⟩ := mem_reviewItems_iff.1 h
  exact ⟨rfl, rfl⟩

/-- **The `proven` mark is the verdict of the check**, not a decision of the
renderer. -/
theorem reviewItem_proven_iff {kb : KB} {r : ReviewItem} (h : r ∈ kb.reviewItems) :
    r.verdict = .proven ↔ kb.resolvesB r.proposal = true := by
  obtain ⟨p, -, rfl⟩ := mem_reviewItems_iff.1 h
  exact verdictOf_eq_proven_iff

/-- **A line marked `proven` really lowers the repair debt.** -/
theorem proven_scoreAfter_lt {kb : KB} {r : ReviewItem} (h : r ∈ kb.reviewItems)
    (hp : r.verdict = .proven) : r.scoreAfter < r.scoreBefore := by
  obtain ⟨hb, ha⟩ := reviewItems_honest h
  rw [ha, hb]
  exact score_lt_of_resolves ((reviewItem_proven_iff h).1 hp)

/-- **A line marked `proven` describes a change that breaks nothing**: no error
and no warning appears that the base did not already carry. -/
theorem proven_no_regression {kb : KB} {r : ReviewItem} (h : r ∈ kb.reviewItems)
    (hp : r.verdict = .proven) :
    (∀ e ∈ (kb.patch r.proposal.edits).errors, e ∈ kb.errors) ∧
      (∀ w ∈ (kb.patch r.proposal.edits).warnings, w ∈ kb.warnings) ∧
      r.proposal.issue ∉ (kb.patch r.proposal.edits).flagged := by
  have hr := (reviewItem_proven_iff h).1 hp
  exact ⟨errors_subset_of_resolves hr, warnings_subset_of_resolves hr,
    issue_not_flagged_of_resolves hr⟩

/-! ## Counting -/

/-- How many candidates the check recommends. -/
def provenCount (kb : KB) : ℕ := kb.reviewItems.countP (fun r => r.verdict == .proven)

/-- How many candidates are left for a human to decide. -/
def rejectedCount (kb : KB) : ℕ := kb.reviewItems.countP (fun r => r.verdict == .rejected)

/-- **The summary counts account for every candidate.** -/
theorem provenCount_add_rejectedCount (kb : KB) :
    kb.provenCount + kb.rejectedCount = kb.reviewItems.length := by
  have h2 : (kb.reviewItems.countP fun r => r.verdict == Verdict.rejected) =
      kb.reviewItems.countP fun r => decide ¬(r.verdict == Verdict.proven) = true :=
    List.countP_congr fun r _ => by cases r.verdict <;> simp
  rw [provenCount, rejectedCount, h2,
    ← List.length_eq_countP_add_countP (p := fun r : ReviewItem => r.verdict == Verdict.proven)]

/-- The candidates the check recommends, as they appear on the review table. -/
theorem provenCount_eq_accepted_length (kb : KB) : kb.provenCount = kb.accepted.length := by
  rw [provenCount, reviewItems, List.countP_map, accepted, ← List.countP_eq_length_filter]
  refine List.countP_congr fun p _ => ?_
  by_cases h : kb.resolvesB p = true <;> simp [verdictOf, h]

end KB

/-! ## The review as a table -/

/-- The column headings of an exported patch review. -/
def reviewHeader : List String :=
  ["code", "severity", "subject", "object", "extra", "issue", "change", "rationale", "verdict",
    "score before", "score after"]

/-- A review line as a list of fields, in the order of `Wikidata.reviewHeader`. -/
def ReviewItem.fields (r : ReviewItem) : List String :=
  let row := Report.rowOfIssue r.proposal.issue
  [row.code, row.severity.text, row.subject, row.object, row.extra, row.message,
    editsText r.proposal.edits, r.proposal.rationale, r.verdict.text,
    num r.scoreBefore, num r.scoreAfter]

theorem ReviewItem.fields_length (r : ReviewItem) : r.fields.length = reviewHeader.length := by
  simp [ReviewItem.fields, reviewHeader]

theorem ReviewItem.fields_ne_nil (r : ReviewItem) : r.fields ≠ [] := by
  simp [ReviewItem.fields]

/-- One line of the review, as a sentence for a wiki talk page. -/
def ReviewItem.line (r : ReviewItem) : String :=
  let row := Report.rowOfIssue r.proposal.issue
  "* " ++ row.code ++ " at " ++ row.subject ++
    (if row.object = "" then "" else " / " ++ row.object) ++
    " — proposed change: " ++ editsText r.proposal.edits ++
    " — why: " ++ r.proposal.rationale ++
    " — verdict: " ++ r.verdict.text ++
    " (repair debt " ++ num r.scoreBefore ++ " → " ++ num r.scoreAfter ++ ")"

/-! ### Rendering a review

The renderers take the lines and the two numbers, so that the tool can render a
review it computed through the closure tables and get the same file. -/

/-- The number of lines with each verdict. -/
def countVerdict (items : List ReviewItem) (v : KB.Verdict) : ℕ :=
  items.countP (fun r => r.verdict == v)

/-- A patch review as a CSV file. -/
def reviewCsvOf (items : List ReviewItem) : String :=
  Report.csvText reviewHeader (items.map ReviewItem.fields)

/-- **An exported review reads back exactly as written**, provided no field
carries a newline. -/
theorem parseCsvText_reviewCsvOf {items : List ReviewItem}
    (h : ∀ r ∈ items, ∀ f ∈ r.fields, '\n' ∉ f.toList) :
    Report.parseCsvText (reviewCsvOf items) =
      some (reviewHeader :: items.map ReviewItem.fields) := by
  refine Report.parseCsvText_csvText (by simp [reviewHeader]) (by decide) ?_
  intro fs hfs
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hfs
  exact ⟨ReviewItem.fields_ne_nil r, h r hr⟩

/-- The summary lines of a patch review: how many candidates there are, how many
the check recommends, and what the base would score if all of them were
accepted. -/
def reviewSummaryRows (total proven rejected debtNow debtAfter : ℕ) : List (List String) :=
  [["candidates", num total],
   ["recommended", num proven],
   ["left for review", num rejected],
   ["repair debt now", num debtNow],
   ["repair debt if all recommended changes are made", num debtAfter]]

/-- The summary lines of a patch review of one layer. -/
def reviewSummaryOf (items : List ReviewItem) (debtNow debtAfter : ℕ) : List (List String) :=
  reviewSummaryRows items.length (countVerdict items .proven) (countVerdict items .rejected)
    debtNow debtAfter

/-- A patch review as an HTML page. -/
def reviewHtmlOf (title : String) (intro : String) (items : List ReviewItem)
    (debtNow debtAfter : ℕ) : String :=
  Report.htmlText title intro reviewHeader
    ((reviewSummaryOf items debtNow debtAfter).map fun fs => ("", fs)) ["measure", "value"]
    (items.map fun r =>
      ((match r.verdict with | .proven => "warning" | .rejected => "error"), r.fields))

/-- A patch review as a plain text page: a header, the summary, and one line per
candidate. -/
def reviewTextOf (name : String) (items : List ReviewItem) (debtNow debtAfter : ℕ) : String :=
  Cli.joinChar '\n'
    (["Proposed repairs for " ++ name,
      "candidates: " ++ num items.length ++
        ", recommended: " ++ num (countVerdict items .proven) ++
        ", left for review: " ++ num (countVerdict items .rejected),
      "repair debt: " ++ num debtNow ++
        " → " ++ num debtAfter ++ " if the recommended changes are made",
      "Nothing below has been applied."] ++
     items.map ReviewItem.line)

namespace KB

/-- The patch review of a base, as a CSV file. -/
def reviewCsv (kb : KB) : String := reviewCsvOf kb.reviewItems

/-- **The exported review of a base reads back exactly as written**, provided no
field carries a newline. -/
theorem parseCsvText_reviewCsv {kb : KB}
    (h : ∀ r ∈ kb.reviewItems, ∀ f ∈ r.fields, '\n' ∉ f.toList) :
    Report.parseCsvText kb.reviewCsv =
      some (reviewHeader :: kb.reviewItems.map ReviewItem.fields) :=
  parseCsvText_reviewCsvOf h

/-- **The exported table has exactly one line per candidate**, in order. -/
theorem reviewCsv_rows (kb : KB) :
    (kb.reviewItems.map ReviewItem.fields).length = kb.plan.length := by
  simp

/-- The counts printed at the head of a review are the counts of the table. -/
@[simp] theorem countVerdict_proven (kb : KB) :
    countVerdict kb.reviewItems .proven = kb.provenCount := rfl

@[simp] theorem countVerdict_rejected (kb : KB) :
    countVerdict kb.reviewItems .rejected = kb.rejectedCount := rfl

/-- The patch review of a base, as an HTML page. -/
def reviewHtml (kb : KB) (title : String) (intro : String) : String :=
  reviewHtmlOf title intro kb.reviewItems kb.score kb.autofix.score

/-- The patch review of a base, as a plain text page. -/
def reviewText (kb : KB) : String :=
  reviewTextOf kb.name kb.reviewItems kb.score kb.autofix.score

/-- **The summary is honest about the outcome**: the debt it quotes for the
repaired base is one the base can really reach, and it is no worse than the
current one. -/
theorem reviewSummary_autofix_le (kb : KB) : kb.autofix.score ≤ kb.score :=
  autofix_score_le kb

/-! ### The review, computed through the closure tables -/

/-- `reviewItems`, computed through the closure tables: what the tool runs. -/
def reviewItemsFast (kb : KB) : List ReviewItem :=
  kb.planFast.map fun p =>
    { proposal := p, verdict := if kb.resolvesFastB p then .proven else .rejected,
      scoreBefore := kb.scoreFast, scoreAfter := (kb.patch p.edits).scoreFast }

/-- **The tool renders exactly the review the theorems are about.** -/
@[simp] theorem reviewItemsFast_eq (kb : KB) : kb.reviewItemsFast = kb.reviewItems := by
  rw [reviewItemsFast, reviewItems, planFast_eq]
  refine List.map_congr_left fun p _ => ?_
  simp [verdictOf]

end KB
end Wikidata
