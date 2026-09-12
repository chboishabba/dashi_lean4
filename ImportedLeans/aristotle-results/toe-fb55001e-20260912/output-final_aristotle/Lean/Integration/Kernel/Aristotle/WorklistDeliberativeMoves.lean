import Integration.Kernel.Welds.DeliberativeMoves
import RequestProject.Worklist

/-!
# Aristotle instantiation: report status ↔ deliberative move

The weld `Integration.Kernel.Welds.DeliberativeMoves` extends the action loop by
`ask`, `listen` and `reformulate`, and proves that reformulation can close a
question with the live fibre untouched.  The archive's reporting layer
(`RequestProject.Reports`, `RequestProject.Worklist`) already carries the
distinction that makes the weld applicable, and carries it in its own terms:

* `Severity` — `error` (validity broken) or `warning` (style);
* `Status` — `provenFix` (a fix **proved** to change no derived fact),
  `suggestedFix` (mechanical, but it changes the data), `needsReview`
  (destructive or ambiguous: a human must choose).

So *reportable*, *repairable* and *reviewable* are three different coordinates
in the archive, not a gloss added here.

## What is proved

* `statusMove` — the mapping into the weld's extended move type, justified by
  the archive's own definitions: a **proven fix changes no derived fact**, hence
  is a `reformulate`; a suggested fix is a search/test move; a needs-review row
  is an `ask`.
* `provenFix_is_reformulation`, `suggestedFix_is_a_search_move`,
  `needsReview_is_ask` and `statusMove_injective` — the three are not
  interchangeable, using the weld's own separations.
* **`severity_does_not_determine_move`** and
  **`move_does_not_determine_severity`** — the two coordinates come apart in
  both directions: how bad an issue is does not say what to do about it, and
  vice versa.
* **`worklist_membership_is_not_information_gain`** — a task all of whose rows
  are proven fixes maps entirely to reformulations, and reformulation leaves the
  live fibre exactly as it was (the weld's theorem).  Being on the worklist is
  therefore not evidence and not narrowing; the authority to act has to come
  from somewhere else.
* `task_counts_separate` — on one worklist task the error count and the
  proven-fix count are different numbers, computed by the archive's own
  `Task.errors` / `Task.provenFixes`.

**Claim boundary.**  `sampleRows` and the task built from them are finite
fixtures defined here; `Severity`, `Status`, `Row`, `tasks`, `Task.errors` and
`Task.provenFixes` are the archive's.  The mapping `statusMove` is a modelling
choice, argued from the archive's docstrings and not derived from them; no
claim is made that any real repair workflow behaves this way.
-/

namespace Integration.Kernel.Aristotle.WorklistDeliberativeMoves

open Integration.Kernel

/-! ## §1 Status as a deliberative move -/

/-- The move a report row calls for.  A *proven* fix changes no derived fact:
applying it re-presents the question without touching what is live, which is
exactly the weld's `reformulate`.  A suggested fix changes the data and must be
tested, a search move.  A needs-review row puts the question to someone else. -/
def statusMove : Wikidata.Report.Status → Welds.DeliberativeMoves.EpistemicMove
  | .provenFix => .reformulate
  | .suggestedFix => .search .refineMove
  | .needsReview => .ask

theorem provenFix_is_reformulation :
    statusMove .provenFix = Welds.DeliberativeMoves.EpistemicMove.reformulate := rfl

theorem suggestedFix_is_a_search_move :
    statusMove .suggestedFix = Welds.DeliberativeMoves.EpistemicMove.search .refineMove := rfl

theorem needsReview_is_ask :
    statusMove .needsReview = Welds.DeliberativeMoves.EpistemicMove.ask := rfl

/-- A needs-review row is not a search move: the weld's separation, instantiated. -/
theorem needsReview_is_not_a_search_move (m : Kernel.Loop.Move) :
    statusMove .needsReview ≠ Welds.DeliberativeMoves.EpistemicMove.search m :=
  fun h => Welds.DeliberativeMoves.ask_is_not_a_search_move m h.symm

/-- A proven fix is not a search move either. -/
theorem provenFix_is_not_a_search_move (m : Kernel.Loop.Move) :
    statusMove .provenFix ≠ Welds.DeliberativeMoves.EpistemicMove.search m :=
  fun h => Welds.DeliberativeMoves.reformulate_is_not_a_search_move m h.symm

/-- The three statuses call for three different moves. -/
theorem statusMove_injective : Function.Injective statusMove := by
  intro a b h
  cases a <;> cases b <;> simp_all [statusMove]

/-! ## §2 Severity and move are independent coordinates -/

/-- A validity-breaking issue that only needs review. -/
def errorNeedsReview : Wikidata.Report.Row where
  layer := "class graph"
  code := "cycle"
  severity := .error
  status := .needsReview
  subject := "Q1"
  object := ""
  extra := ""
  message := "the class graph has a cycle"
  fix := ""

/-- A validity-breaking issue with a proven fix. -/
def errorProvenFix : Wikidata.Report.Row where
  layer := "class graph"
  code := "redundant-edge"
  severity := .error
  status := .provenFix
  subject := "Q2"
  object := "Q1"
  extra := ""
  message := "the edge is derivable from the others"
  fix := "drop the edge"

/-- A stylistic issue that also has a proven fix. -/
def warningProvenFix : Wikidata.Report.Row where
  layer := "labels"
  code := "duplicate-alias"
  severity := .warning
  status := .provenFix
  subject := "Q3"
  object := ""
  extra := ""
  message := "the alias repeats the label"
  fix := "drop the alias"

/-- **How bad an issue is does not say what to do about it.**  Two rows of the
same severity call for different moves. -/
theorem severity_does_not_determine_move :
    errorNeedsReview.severity = errorProvenFix.severity ∧
    statusMove errorNeedsReview.status ≠ statusMove errorProvenFix.status := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Welds.DeliberativeMoves.reformulate_is_not_a_search_move .refineMove
    (absurd (statusMove_injective h) (by decide))

/-- **And what to do about it does not say how bad it is.**  Two rows calling
for the same move have different severities. -/
theorem move_does_not_determine_severity :
    statusMove errorProvenFix.status = statusMove warningProvenFix.status ∧
    errorProvenFix.severity ≠ warningProvenFix.severity := by
  refine ⟨rfl, by decide⟩

/-! ## §3 Being on the worklist is not information gain -/

/-- The rows of the fixture. -/
def sampleRows : List Wikidata.Report.Row :=
  [errorNeedsReview, errorProvenFix, warningProvenFix]

/-- The worklist tasks keyed by layer, as the archive builds them. -/
def sampleTasks : List Wikidata.Report.Task :=
  Wikidata.Report.tasks (fun r => r.layer) sampleRows

/-- **The counts separate.**  On the class-graph task the archive counts two
errors and one proven fix: the queue's size, its severity profile and its
repairability profile are three different readings. -/
theorem task_counts_separate :
    (sampleTasks.map (fun t => (t.rows.length, t.errors, t.provenFixes)))
      = [(2, 2, 1), (1, 0, 1)] := by decide

/-- A task all of whose rows are proven fixes. -/
def provenOnlyTask : List Wikidata.Report.Row := [errorProvenFix, warningProvenFix]

/-- Every row of that task maps to a reformulation. -/
theorem provenOnlyTask_is_all_reformulation :
    ∀ r ∈ provenOnlyTask,
      statusMove r.status = Welds.DeliberativeMoves.EpistemicMove.reformulate := by
  decide

/-- **Being on the worklist is not information gain.**  A queue of proven fixes
consists entirely of reformulations, and reformulation leaves the live fibre
exactly as it was — the weld's theorem, quoted here.  So the queue supplies no
narrowing, and the authority to act on it is not manufactured by membership. -/
theorem worklist_membership_is_not_information_gain :
    (∀ r ∈ provenOnlyTask,
      statusMove r.status = Welds.DeliberativeMoves.EpistemicMove.reformulate) ∧
    (Welds.DeliberativeMoves.act Welds.DeliberativeMoves.blindPolicy true ∅ {true}
        (fun _ => true) .reformulate Welds.DeliberativeMoves.openInquiry).fibre
      = Welds.DeliberativeMoves.openInquiry.fibre :=
  ⟨provenOnlyTask_is_all_reformulation,
   Welds.DeliberativeMoves.reformulation_can_close_without_narrowing.1⟩

end Integration.Kernel.Aristotle.WorklistDeliberativeMoves
