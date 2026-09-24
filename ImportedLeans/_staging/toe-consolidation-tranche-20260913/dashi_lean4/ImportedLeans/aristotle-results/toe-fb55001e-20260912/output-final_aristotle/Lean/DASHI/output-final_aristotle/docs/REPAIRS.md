# The repair workflow: a checked patch review for every flagged issue

`wikidata check` and `wikidata report` say what is wrong.  They do not say what
to do about it, and they never say it with a guarantee.  The repair workflow
does both, and it does it **without touching the data**: for every flagged
issue it proposes the changes that would fix it, gives the reason for each one,
and marks the ones a machine check certifies as improvements.  A human reads the
review and decides.

```
wikidata repairs examples/defects.skb --out docs/repairs --out-base
  → docs/repairs/defects.csv             one line per candidate repair
  → docs/repairs/defects.html            the same, with the summary on top
  → docs/repairs/defects.txt             a plain text review for a talk page
  → docs/repairs/defects-repaired.skb    the base the recommended changes give
```

The input file is never modified.  `-repaired.wdkb` is written only with
`--out-base`, and only as something to diff against.
`scripts/make-repairs.sh` regenerates the reviews in
[`repairs/`](repairs/).

Both layers of a stored base are reviewed at once: the ontology (`subclass of`,
`instance of`, disjointness, metaclass levels) and the series layer (`part of the
series`, `follows`, `series ordinal`).  The steps below describe the ontology
half; [the series layer](#the-series-layer) works exactly the same way.

## The five steps

1. **Flag.** `Wikidata.KB.flagged` is the errors and the warnings of a base, in
   one list — the full agenda.
2. **Cost.** `Wikidata.KB.score` is the *repair debt*: `4·errors + 2·warnings +
   statements`.  Errors weigh most, warnings less, and the size term is what
   stops the engine from "repairing" a base by adding to it.
3. **Propose.** `Wikidata.KB.plan` gives one to four candidate repairs for every
   flagged issue, each a list of edits and a sentence of rationale.  Every issue
   the base flags has at least one candidate: `Wikidata.KB.plan_covers` and
   `repairsOfIssue_ne_nil`.
4. **Check.** `Wikidata.KB.resolvesB` decides, for one candidate, whether it is
   an improvement — see the guarantees below.  The verdict is
   `Wikidata.KB.verdictOf`: `proven` or `rejected`.
5. **Review.** `Wikidata.KB.reviewItems` is the whole thing as a table, one line
   per candidate, and that is what the command writes out.  Nothing is applied.

## The edits it may propose

`Wikidata.Edit` is deliberately small, so that every proposal is something a
human editor could carry out on the wiki by hand:

| edit | what it does on the wiki |
|---|---|
| `dropSub a b` | remove the `subclass of` (P279) statement `a → b` |
| `dropInst a c` | remove the `instance of` (P31) statement `a → c` |
| `dropDisj c d` | remove the disjointness declaration between `c` and `d` |
| `declareItem q` | add the missing item `q` to the base |
| `setLevel q n` | correct the metaclass level recorded for `q` |
| `instToSub a c` | rewrite `a instance of c` as `a subclass of c` |

## What the candidates look like

Per issue type, the plan is the list of readings of the defect that an editor
would actually consider:

| issue | candidates |
|---|---|
| `dangling-sub`, `dangling-inst`, `dangling-disj` | declare the missing endpoints; or delete the statement |
| `level-inst` | lift the class; lower the instance; reread it as `subclass of`; or delete the statement |
| `level-sub` | put both classes on one class level; lift the superclass only; or delete the statement |
| `subclass-cycle` | cut the statement; cut the other one; or cut both |
| `disjoint-violation` | withdraw the disjointness; or drop either of the two memberships |
| `redundant-sub` | delete the statement — it is already implied |

The rationale column carries the reading in words, e.g. *"the two items sit at
the same level, so this is `subclass of` written as `instance of`"*.  Two
candidates for one issue are usually incompatible; the review is there so a
person picks.

## What `proven` means

A candidate is marked `proven` exactly when all four hold
(`Wikidata.KB.verdictOf_eq_proven_iff` unfolds this):

| condition | theorem |
|---|---|
| the issue it is raised for really is flagged now | `Wikidata.KB.issue_flagged_of_resolves` |
| after the change that issue is no longer flagged | `Wikidata.KB.issue_not_flagged_of_resolves` |
| no *new* error and no *new* warning appears — every one afterwards was there before | `Wikidata.KB.errors_subset_of_resolves`, `warnings_subset_of_resolves` |
| the repair debt strictly falls | `Wikidata.KB.score_lt_of_resolves` |

Two consequences worth stating on their own:

* **A valid base stays valid.**  `Wikidata.KB.valid_of_resolves`: applying a
  `proven` repair to a base with no errors leaves a base with no errors.
* **The debt is a termination measure.**  Because it strictly falls, a
  `proven` repair can never be the first step of a loop.

`rejected` is not a claim that the change is wrong — only that this check does
not certify it.  Cutting a cycle the other way round, or deleting the membership
rather than the disjointness, are real choices that need an editor.

## The review table

| column | what it holds |
|---|---|
| `code`, `severity` | the issue this candidate is for, as in the report |
| `subject`, `object`, `extra` | the identifiers it is about |
| `issue` | the problem, in a sentence |
| `change` | the edits the candidate would make |
| `rationale` | why they would be the right ones |
| `verdict` | `proven` (recommended) or `rejected` (for review) |
| `score before`, `score after` | the repair debt now, and if this change were made |

What is verified about the table itself:

| claim | theorem |
|---|---|
| there is a line for every candidate, and a candidate for every flagged issue — nothing is quietly dropped | `Wikidata.KB.reviewItems_covers`, `reviewItems_length` |
| every line is about an issue the base really flags — no invented work | `Wikidata.KB.reviewItems_issue_flagged` |
| the numbers in a line are the ones the check used: the verdict, the scores and the base after the change all agree | `Wikidata.KB.reviewItems_honest` |
| a line marked `proven` removes its issue and adds no error and no warning | `Wikidata.KB.proven_no_regression` |
| a line marked `proven` strictly lowers the debt | `Wikidata.KB.proven_scoreAfter_lt` |
| the recommended and the rejected lines together are all of them | `Wikidata.KB.provenCount_add_rejectedCount` |
| the recommended lines are exactly the ones the engine would apply | `Wikidata.KB.provenCount_eq_accepted_length` |
| the CSV file reads back exactly as written | `Wikidata.parseCsvText_reviewCsvOf`, `Wikidata.KB.parseCsvText_reviewCsv` |

## Applying a selection — and applying all of them

An editor who accepts some subset of the review can apply it with
`Wikidata.KB.applyProposals`, and **any** subset is safe, because each proposal
is re-checked at the moment it is applied (`Wikidata.KB.applyProposal`) and
skipped if the base has moved under it:

| claim | theorem |
|---|---|
| the debt never rises | `Wikidata.KB.applyProposals_score_le` |
| no new error, no new warning | `Wikidata.KB.applyProposals_errors_subset`, `applyProposals_warnings_subset` |
| a valid base stays valid | `Wikidata.KB.applyProposals_valid` |
| a rejected proposal is a no-op | `Wikidata.KB.applyProposal_of_rejected` |

`Wikidata.KB.autofix` is the special case "accept everything recommended", and
`Wikidata.KB.rounds n` is `autofix` iterated — the whole workflow run to
convergence:

| claim | theorem |
|---|---|
| more rounds never cost more | `Wikidata.KB.rounds_score_antitone` |
| more rounds never add an error | `Wikidata.KB.rounds_errors_subset` |
| once a round changes nothing, no later round does either — the workflow terminates | `Wikidata.KB.rounds_stabilises` |
| a clean base is a fixpoint: nothing is proposed and nothing is touched | `Wikidata.KB.flagged_eq_nil_iff_clean`, `plan_eq_nil_of_clean`, `autofix_eq_self_of_clean` |

The last line is the one that matters for a wiki that is being edited anyway:
the workflow does nothing at all to a base it has no complaint about, so it can
be re-run on every snapshot.

## The series layer

Everything above is the *ontology* layer.  The series layer — `part of the
series` (P179), `follows` (P155), `series ordinal` (P1545) — has its own
diagnostics, and it has the same workflow, in the same shape and with the same
guarantees: `Wikidata.SKB.sFlagged`, `sScore`, `sPlan`, `sResolvesB`,
`sApplyProposals`, `sAutofix`, `sReviewItems`.  Its lines appear in the same
review, in the same columns, and the `code` column says which layer they came
from.

Its edit vocabulary is the one an editor would use on a series:

| edit | what it does on the wiki |
|---|---|
| `dropSeries a t` | remove the `part of the series` statement |
| `dropFollows a b` | remove the `follows` statement |
| `dropOrdinal a` | remove the `series ordinal` value |
| `declareItem q` | add the missing item to the base |
| `setOrdinal a n` | correct the `series ordinal` value |
| `setSeries a t` | put the item in another series |

| issue | candidates |
|---|---|
| `dangling-series`, `dangling-follows`, `dangling-ordinal` | declare the missing endpoint; or delete the statement |
| `self-follows` | delete the statement — nothing comes after itself |
| `series-cycle` | cut either statement, or both |
| `forked-series` | keep the first predecessor, or the second |
| `series-mismatch` | move either item into the other's series; or deny that they are neighbours |
| `taxonomic-follows` | delete the `follows` statement — the taxonomy already says it |
| `ordinal-conflict` | renumber the item after its predecessor; or delete either ordinal |

The check is the ontology one plus one more condition: a series repair must not
break the taxonomy underneath it either.  That is
`Wikidata.SKB.base_errors_subset_of_sResolves`, and it carries through any
selection a reviewer accepts
(`Wikidata.SKB.sApplyProposals_base_errors_subset`).  A valid layer stays valid
(`Wikidata.SKB.sValid_of_sResolves`), the debt is again a strict measure
(`Wikidata.SKB.sScore_lt_of_sResolves`, `sRounds_stabilises`), and a layer with
nothing flagged is again a fixpoint
(`Wikidata.SKB.sAutofix_eq_self_of_sFlagged_nil`).

The worked examples are in
[`RequestProject/SeriesRepairExamples.lean`](../RequestProject/SeriesRepairExamples.lean):
one small layer per series issue type, each flagged, each with a recommended
repair, each coming out with nothing flagged; and a layer with four defects at
once that one round takes from a repair debt of 36 to 4 and to nothing flagged
(`brokenSKB_round_clean`), after which it is a fixpoint.

## The redundant statement, end to end

The one case where the repair is *provably lossless* rather than merely an
improvement is the redundant `subclass of` statement.  Deleting it keeps the base
valid and changes no derived `subclass of` or `instance of` fact
(`Wikidata.KB.warning_prunable`, `dropSub_isSubclassOf`), it cannot create a new
redundancy warning (`Wikidata.KB.dropSub_warnings_subset`), and so its candidate
is always recommended: `Wikidata.KB.redundant_proposal_resolves`.

## Worked examples

[`RequestProject/RepairExamples.lean`](../RequestProject/RepairExamples.lean)
runs the workflow, in Lean, on one small base per issue type: each defect is
flagged, gets a recommended repair, and the base comes out clean — all `by
decide`, so they are checked whenever the project is built.  It also shows the
other side: a candidate that is *not* recommended
(`levelInst_instToSub_deferred`), and repairs that keep what the base could
answer (`disjoint_keeps_memberships`, `redundant_keeps_answers`,
`cycle_keeps_one_statement`).

Finally `brokenKB` carries all eight defects at once: ten flagged issues,
twenty-seven candidate repairs (`brokenKB_sizes`), every issue covered
(`brokenKB_plan_covers`), and one round of the workflow takes it from a repair
debt of 51 to 9 and to clean (`brokenKB_round_clean`), after which it is a
fixpoint (`brokenKB_fixpoint`).

## Where this fits

* `wikidata check` — is there anything wrong?
* `wikidata report` — what exactly, one line per defect ([REPORTS.md](REPORTS.md))
* `wikidata worklist` — grouped into things somebody could adopt
* **`wikidata repairs`** — what to *do* about each one, with the recommendations
  marked and nothing applied
* `wikidata fix` — the older, narrower engine: applies the mechanical fixes it
  can justify and prints what it declined
