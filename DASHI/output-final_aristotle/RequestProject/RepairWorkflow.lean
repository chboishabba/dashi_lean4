/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Fixes

/-!
# A reviewable repair workflow for every flagged issue

`RequestProject.Diagnostics` flags issues, `RequestProject.Reports` prints them and
`RequestProject.Fixes` repairs the two kinds that can be repaired mechanically.
Everything else the report classifies `needs-review` and the engine leaves alone,
so a large part of the report has no candidate repair attached to it at all.

This file closes that gap.  The workflow it defines is deliberately *advisory*:
it proposes, it never edits.  For **every** issue the diagnostics can flag it
produces at least one concrete candidate repair, says in words why the change is
the right one, checks the candidate against the data, and hands the result to a
human.

* `Wikidata.Edit` is an elementary change to a base — delete a statement, declare
  an item, re-level an item, or turn an `instance of` statement into a `subclass
  of` statement — and `Wikidata.KB.patch` applies a list of them.
* `Wikidata.Proposal` is a candidate repair: the issue it addresses, the edits it
  makes, and the rationale.
* `Wikidata.KB.repairsOfIssue` generates the candidates for one issue and
  `Wikidata.KB.plan` for the whole report.  *Every* issue gets candidates:
  `Wikidata.KB.plan_covers`.
* `Wikidata.KB.score` measures how much is wrong with a base — errors weigh most,
  then style warnings, then sheer size — and `Wikidata.KB.resolvesB` is the check
  a candidate has to pass: the issue it was raised for is gone, no error and no
  warning appears that the base did not already carry, and the score has gone
  down.  `Wikidata.KB.verdictOf` turns that into the verdict shown to the
  reviewer.

What is proved about a candidate that passes the check
(`Wikidata.KB.issue_not_flagged_of_resolves`, `errors_subset_of_resolves`,
`warnings_subset_of_resolves`, `score_lt_of_resolves`, `valid_of_resolves`): the
issue really is gone, nothing new is broken, the base measurably improves, and a
valid base stays valid.

What is proved about the workflow as a whole:

* `Wikidata.KB.applyProposals_nil` — accepting nothing changes nothing: the
  proposals are only ever a suggestion;
* `Wikidata.KB.applyProposal_of_rejected` — a candidate that fails the check is
  never performed, whatever the reviewer says;
* `Wikidata.KB.applyProposals_score_le`, `applyProposals_errors_subset`,
  `applyProposals_valid` — *any* selection of the proposals, accepted in any
  order, leaves a base that is no worse: no new error, no new warning, no higher
  score;
* `Wikidata.KB.rounds_score_antitone` — running the workflow again and again can
  only improve the base, so the quality of a base is monotone along the repair
  history;
* `Wikidata.KB.redundant_proposal_resolves` — the one repair the library had
  already proved lossless is accepted by the new check as well, so the workflow
  extends the old engine rather than replacing it.
-/

namespace Wikidata

open Cli (qidText)

/-! ## Elementary edits -/

/-- An elementary change to a knowledge base: the vocabulary in which a repair is
proposed. -/
inductive Edit where
  /-- Delete a `subclass of` statement. -/
  | dropSub (a b : Qid)
  /-- Delete an `instance of` statement. -/
  | dropInst (a c : Qid)
  /-- Delete a disjointness declaration. -/
  | dropDisj (c d : Qid)
  /-- Declare an item that statements refer to but the base does not list. -/
  | declareItem (q : Qid)
  /-- Record a different metaclass level for an item. -/
  | setLevel (q : Qid) (n : ℕ)
  /-- Replace the `instance of` statement `a → c` by the `subclass of` statement
  `a → c`: the classic Wikidata class/instance confusion. -/
  | instToSub (a c : Qid)
deriving DecidableEq, Repr, Inhabited

/-- The edit, in one line, as the review table prints it. -/
def Edit.text : Edit → String
  | .dropSub a b => s!"delete `subclass of` {qidText a} → {qidText b}"
  | .dropInst a c => s!"delete `instance of` {qidText a} → {qidText c}"
  | .dropDisj c d => s!"delete the disjointness of {qidText c} and {qidText d}"
  | .declareItem q => s!"declare the item {qidText q}"
  | .setLevel q n => s!"set the metaclass level of {qidText q} to {n}"
  | .instToSub a c => s!"replace `instance of` {qidText a} → {qidText c} by `subclass of`"

/-- A list of edits, in one line. -/
def editsText : List Edit → String
  | [] => "(no change)"
  | [e] => e.text
  | e :: es => e.text ++ "; " ++ editsText es

namespace KB

/-! ## Applying edits -/

/-- The base with the metaclass level of `q` set to `n`. -/
def relevel (kb : KB) (q : Qid) (n : ℕ) : KB :=
  { kb with levels := (q, n) :: kb.levels.filter (fun p => p.1 != q) }

@[simp] theorem relevel_items (kb : KB) (q : Qid) (n : ℕ) : (kb.relevel q n).items = kb.items := rfl

@[simp] theorem relevel_sub (kb : KB) (q : Qid) (n : ℕ) : (kb.relevel q n).sub = kb.sub := rfl

@[simp] theorem relevel_inst (kb : KB) (q : Qid) (n : ℕ) : (kb.relevel q n).inst = kb.inst := rfl

@[simp] theorem relevel_disj (kb : KB) (q : Qid) (n : ℕ) : (kb.relevel q n).disj = kb.disj := rfl

/-- The base after one edit. -/
def edit (kb : KB) : Edit → KB
  | .dropSub a b => kb.dropSub (a, b)
  | .dropInst a c => { kb with inst := kb.inst.filter (fun r => r != (a, c)) }
  | .dropDisj c d => { kb with disj := kb.disj.filter (fun r => r != (c, d)) }
  | .declareItem q => if kb.items.contains q then kb else { kb with items := kb.items ++ [q] }
  | .setLevel q n => kb.relevel q n
  | .instToSub a c =>
      { kb with inst := kb.inst.filter (fun r => r != (a, c)),
                sub := if kb.sub.contains (a, c) then kb.sub else kb.sub ++ [(a, c)] }

/-- The base after a list of edits, performed in order. -/
def patch (kb : KB) (es : List Edit) : KB := es.foldl edit kb

@[simp] theorem patch_nil (kb : KB) : kb.patch [] = kb := rfl

theorem patch_cons (kb : KB) (e : Edit) (es : List Edit) :
    kb.patch (e :: es) = (kb.edit e).patch es := rfl

/-! ## How much is wrong with a base -/

/-- Everything the diagnostics flag: the errors and the style warnings. -/
def flagged (kb : KB) : List Issue := kb.errors ++ kb.warnings

theorem mem_flagged_of_mem_errors {kb : KB} {i : Issue} (h : i ∈ kb.errors) : i ∈ kb.flagged :=
  List.mem_append_left _ h

theorem mem_flagged_of_mem_warnings {kb : KB} {i : Issue} (h : i ∈ kb.warnings) :
    i ∈ kb.flagged := List.mem_append_right _ h

/-- **The repair debt of a base.**  An error costs most, a style warning half as
much, and every statement costs one: of two bases with the same defects, the
smaller — the one that says the same thing with fewer statements — is the better
one. -/
def score (kb : KB) : ℕ := 4 * kb.errors.length + 2 * kb.warnings.length + kb.statementCount

/-- The check for *regression*: the candidate carries no error and no warning that
the base did not already carry. -/
def noRegressionB (kb kb' : KB) : Bool :=
  kb'.errors.all (fun e => decide (e ∈ kb.errors)) &&
    kb'.warnings.all (fun w => decide (w ∈ kb.warnings))

theorem errors_subset_of_noRegression {kb kb' : KB} (h : noRegressionB kb kb' = true) :
    ∀ e ∈ kb'.errors, e ∈ kb.errors := by
  rw [noRegressionB, Bool.and_eq_true, List.all_eq_true] at h
  intro e he
  simpa using h.1 e he

theorem warnings_subset_of_noRegression {kb kb' : KB} (h : noRegressionB kb kb' = true) :
    ∀ w ∈ kb'.warnings, w ∈ kb.warnings := by
  rw [noRegressionB, Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.2
  intro w hw
  simpa using h2 w hw

theorem valid_of_noRegression {kb kb' : KB} (h : noRegressionB kb kb' = true)
    (hv : kb.valid = true) : kb'.valid = true := by
  rw [← errors_eq_nil_iff_valid] at hv ⊢
  refine List.eq_nil_iff_forall_not_mem.2 fun e he => ?_
  have := errors_subset_of_noRegression h e he
  rw [hv] at this
  exact absurd this (List.not_mem_nil)

/-! ## Candidate repairs -/

/-- A candidate repair: the issue it is raised for, the edits it makes, and why
they are the right ones. -/
structure Proposal where
  /-- The flagged issue this candidate addresses. -/
  issue : Issue
  /-- The change it proposes. -/
  edits : List Edit
  /-- Why this change is the right one. -/
  rationale : String
deriving DecidableEq, Repr, Inhabited

/-- The declaration an endpoint calls for, if the base does not list it. -/
def declareMissingE (kb : KB) (q : Qid) : List Edit :=
  if kb.items.contains q then [] else [Edit.declareItem q]

/-- The candidate repairs for one issue, as a change and a rationale.  There is
always at least one candidate: no flagged issue is left without a suggestion. -/
def repairPlansOf (kb : KB) : Issue → List (List Edit × String)
  | .danglingSub a b =>
      [ (kb.declareMissingE a ++ kb.declareMissingE b,
          "the statement looks intended and only its endpoints are undeclared: declare them"),
        ([.dropSub a b],
          "if the undeclared endpoint is not a real item, the statement is the mistake") ]
  | .danglingInst a c =>
      [ (kb.declareMissingE a ++ kb.declareMissingE c,
          "the statement looks intended and only its endpoints are undeclared: declare them"),
        ([.dropInst a c],
          "if the undeclared endpoint is not a real item, the statement is the mistake") ]
  | .danglingDisj c d =>
      [ (kb.declareMissingE c ++ kb.declareMissingE d,
          "the declaration looks intended and only its endpoints are undeclared: declare them"),
        ([.dropDisj c d],
          "if the undeclared endpoint is not a real item, the declaration is the mistake") ]
  | .levelMismatchInst a c =>
      [ ([.setLevel c (kb.levelOf a + 1)],
          "the statement is believed and the level table is wrong: a class sits one level above its instances"),
        ([.setLevel a (kb.levelOf c - 1)],
          "the class is believed and the instance is mis-levelled: an instance sits one level below its class"),
        ([.instToSub a c],
          "the two items sit at the same level, so this is `subclass of` written as `instance of`"),
        ([.dropInst a c],
          "if neither level is in doubt the statement itself is wrong") ]
  | .levelMismatchSub a b =>
      [ ([.setLevel a (max 1 (max (kb.levelOf a) (kb.levelOf b))),
          .setLevel b (max 1 (max (kb.levelOf a) (kb.levelOf b)))],
          "the statement is believed: a class and its superclasses share one level, and it is a class level"),
        ([.setLevel b (max 1 (kb.levelOf a))],
          "the subclass is correctly levelled and the superclass is not: lift the superclass to its level"),
        ([.dropSub a b],
          "if both levels are right the statement crosses metaclass levels and is wrong") ]
  | .subclassCycle a b =>
      [ ([.dropSub a b],
          "a cycle makes the two classes interchangeable: delete the upward statement"),
        ([.dropSub b a],
          "a cycle makes the two classes interchangeable: delete the other statement instead"),
        ([.dropSub a b, .dropSub b a],
          "if neither class is really above the other, delete both statements") ]
  | .disjointViolation c d a =>
      [ ([.dropDisj c d],
          "the two classes demonstrably share an instance, so they are not disjoint"),
        ([.dropInst a c],
          "the disjointness is believed and the first membership is the wrong one"),
        ([.dropInst a d],
          "the disjointness is believed and the second membership is the wrong one") ]
  | .redundantSubclass a b =>
      [ ([.dropSub a b],
          "the statement is already implied by the others: deleting it changes no derived fact") ]

/-- The candidate repairs for one issue. -/
def repairsOfIssue (kb : KB) (i : Issue) : List Proposal :=
  (kb.repairPlansOf i).map fun p => { issue := i, edits := p.1, rationale := p.2 }

/-- Every candidate is a candidate for the issue it was generated from. -/
theorem repairsOfIssue_issue {kb : KB} {i : Issue} {p : Proposal}
    (h : p ∈ kb.repairsOfIssue i) : p.issue = i := by
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- **No flagged issue is left without a suggestion.** -/
theorem repairsOfIssue_ne_nil (kb : KB) (i : Issue) : kb.repairsOfIssue i ≠ [] := by
  cases i <;> simp [repairsOfIssue, repairPlansOf]

theorem exists_repairOfIssue (kb : KB) (i : Issue) :
    ∃ p ∈ kb.repairsOfIssue i, p.issue = i := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (repairsOfIssue_ne_nil kb i)
  exact ⟨p, hp, repairsOfIssue_issue hp⟩

/-- The whole repair plan of a base: the candidates for every issue it flags, in
the order of the report. -/
def plan (kb : KB) : List Proposal := kb.flagged.flatMap kb.repairsOfIssue

/-- **Every flagged issue has a candidate repair in the plan.** -/
theorem plan_covers {kb : KB} {i : Issue} (h : i ∈ kb.flagged) :
    ∃ p ∈ kb.plan, p.issue = i := by
  obtain ⟨p, hp, hpi⟩ := exists_repairOfIssue kb i
  exact ⟨p, List.mem_flatMap.2 ⟨i, h, hp⟩, hpi⟩

/-- **The plan invents nothing**: every candidate addresses an issue the base
really flags. -/
theorem mem_plan_issue {kb : KB} {p : Proposal} (h : p ∈ kb.plan) : p.issue ∈ kb.flagged := by
  obtain ⟨i, hi, hp⟩ := List.mem_flatMap.1 h
  rw [repairsOfIssue_issue hp]
  exact hi

/-! ## The verdict on a candidate -/

/-- The check a candidate has to pass to be recommended: the issue it was raised
for is really flagged and is gone after the change, the change introduces no
error and no warning the base did not carry, and the repair debt has gone down.

The first conjunct is what keeps the workflow from destroying data: a change is
only ever performed to remove an issue that is on the table at the moment it is
performed, so a candidate whose issue an earlier repair has already settled is
refused rather than applied for the sake of a smaller base. -/
def resolvesB (kb : KB) (p : Proposal) : Bool :=
  decide (p.issue ∈ kb.flagged) &&
    !decide (p.issue ∈ (kb.patch p.edits).flagged) &&
    noRegressionB kb (kb.patch p.edits) &&
    decide ((kb.patch p.edits).score < kb.score)

/-- What the workflow recommends about a candidate. -/
inductive Verdict where
  /-- The candidate passed the check: applying it is proved to remove the issue
  and to break nothing. -/
  | proven
  /-- The candidate did not pass: it is recorded for the reviewer, and never
  performed. -/
  | rejected
deriving DecidableEq, Repr, Inhabited

/-- The verdict, as the review table prints it. -/
def Verdict.text : Verdict → String
  | .proven => "proven"
  | .rejected => "rejected"

/-- The verdict on a candidate. -/
def verdictOf (kb : KB) (p : Proposal) : Verdict :=
  if kb.resolvesB p then .proven else .rejected

@[simp] theorem verdictOf_eq_proven_iff {kb : KB} {p : Proposal} :
    kb.verdictOf p = .proven ↔ kb.resolvesB p = true := by
  by_cases h : kb.resolvesB p <;> simp [verdictOf, h]

/-- **A recommended repair addresses an issue the base really flags.** -/
theorem issue_flagged_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    p.issue ∈ kb.flagged := by
  rw [resolvesB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.1.1.1

/-- **The issue a recommended repair was raised for is gone.** -/
theorem issue_not_flagged_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    p.issue ∉ (kb.patch p.edits).flagged := by
  rw [resolvesB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h.1.1.2

theorem noRegression_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    noRegressionB kb (kb.patch p.edits) = true := by
  rw [resolvesB, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- **A recommended repair introduces no new error.** -/
theorem errors_subset_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    ∀ e ∈ (kb.patch p.edits).errors, e ∈ kb.errors :=
  errors_subset_of_noRegression (noRegression_of_resolves h)

/-- **A recommended repair introduces no new warning.** -/
theorem warnings_subset_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    ∀ w ∈ (kb.patch p.edits).warnings, w ∈ kb.warnings :=
  warnings_subset_of_noRegression (noRegression_of_resolves h)

/-- **A recommended repair improves the base**: its repair debt goes down. -/
theorem score_lt_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true) :
    (kb.patch p.edits).score < kb.score := by
  rw [resolvesB, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.2

/-- **A recommended repair keeps a valid base valid.** -/
theorem valid_of_resolves {kb : KB} {p : Proposal} (h : kb.resolvesB p = true)
    (hv : kb.valid = true) : (kb.patch p.edits).valid = true :=
  valid_of_noRegression (noRegression_of_resolves h) hv

/-! ## Applying what a reviewer accepts -/

/-- The base after a reviewer accepts one candidate.  The check is run again at
the moment of application, so a candidate that does not pass it is not performed
even if it was accepted. -/
def applyProposal (kb : KB) (p : Proposal) : KB :=
  if kb.resolvesB p then kb.patch p.edits else kb

/-- **A candidate that fails the check is never performed.** -/
theorem applyProposal_of_rejected {kb : KB} {p : Proposal} (h : kb.resolvesB p = false) :
    kb.applyProposal p = kb := by simp [applyProposal, h]

theorem applyProposal_score_le (kb : KB) (p : Proposal) : (kb.applyProposal p).score ≤ kb.score := by
  by_cases h : kb.resolvesB p = true
  · simp only [applyProposal, h, if_true]
    exact (score_lt_of_resolves h).le
  · simp [applyProposal, h]

theorem applyProposal_errors_subset (kb : KB) (p : Proposal) :
    ∀ e ∈ (kb.applyProposal p).errors, e ∈ kb.errors := by
  by_cases h : kb.resolvesB p = true
  · simp only [applyProposal, h, if_true]
    exact errors_subset_of_resolves h
  · simp only [Bool.not_eq_true] at h
    simp [applyProposal, h]

theorem applyProposal_warnings_subset (kb : KB) (p : Proposal) :
    ∀ w ∈ (kb.applyProposal p).warnings, w ∈ kb.warnings := by
  by_cases h : kb.resolvesB p = true
  · simp only [applyProposal, h, if_true]
    exact warnings_subset_of_resolves h
  · simp only [Bool.not_eq_true] at h
    simp [applyProposal, h]

theorem applyProposal_valid {kb : KB} (hv : kb.valid = true) (p : Proposal) :
    (kb.applyProposal p).valid = true := by
  by_cases h : kb.resolvesB p = true
  · simp only [applyProposal, h, if_true]
    exact valid_of_resolves h hv
  · simp only [Bool.not_eq_true] at h
    simpa [applyProposal, h] using hv

/-- The base after a reviewer accepts a selection of candidates, in the order of
the selection. -/
def applyProposals (kb : KB) (ps : List Proposal) : KB := ps.foldl applyProposal kb

/-- **Accepting nothing changes nothing**: the workflow only ever suggests. -/
@[simp] theorem applyProposals_nil (kb : KB) : kb.applyProposals [] = kb := rfl

theorem applyProposals_cons (kb : KB) (p : Proposal) (ps : List Proposal) :
    kb.applyProposals (p :: ps) = (kb.applyProposal p).applyProposals ps := rfl

/-- **Any selection of candidates leaves a base that is no worse.** -/
theorem applyProposals_score_le : ∀ (ps : List Proposal) (kb : KB),
    (kb.applyProposals ps).score ≤ kb.score
  | [], _ => Nat.le_refl _
  | p :: ps, kb => by
      rw [applyProposals_cons]
      exact (applyProposals_score_le ps _).trans (applyProposal_score_le kb p)

/-- **Any selection of candidates introduces no new error.** -/
theorem applyProposals_errors_subset : ∀ (ps : List Proposal) (kb : KB),
    ∀ e ∈ (kb.applyProposals ps).errors, e ∈ kb.errors
  | [], _, _, he => he
  | p :: ps, kb, e, he => by
      rw [applyProposals_cons] at he
      exact applyProposal_errors_subset kb p e (applyProposals_errors_subset ps _ e he)

/-- **Any selection of candidates introduces no new warning.** -/
theorem applyProposals_warnings_subset : ∀ (ps : List Proposal) (kb : KB),
    ∀ w ∈ (kb.applyProposals ps).warnings, w ∈ kb.warnings
  | [], _, _, hw => hw
  | p :: ps, kb, w, hw => by
      rw [applyProposals_cons] at hw
      exact applyProposal_warnings_subset kb p w (applyProposals_warnings_subset ps _ w hw)

/-- **Any selection of candidates keeps a valid base valid.** -/
theorem applyProposals_valid : ∀ (ps : List Proposal) {kb : KB}, kb.valid = true →
    (kb.applyProposals ps).valid = true
  | [], _, hv => hv
  | p :: ps, kb, hv => by
      rw [applyProposals_cons]
      exact applyProposals_valid ps (applyProposal_valid hv p)

/-! ## The workflow -/

/-- The candidates of the plan that pass the check: what the workflow
recommends. -/
def accepted (kb : KB) : List Proposal := kb.plan.filter (fun p => kb.resolvesB p)

/-- The candidates of the plan that do not pass the check: what is left for a
human to decide. -/
def deferred (kb : KB) : List Proposal := kb.plan.filter (fun p => !kb.resolvesB p)

/-- **The plan splits into what is recommended and what is deferred**, with
nothing dropped and nothing counted twice. -/
theorem accepted_append_deferred_perm (kb : KB) :
    (kb.accepted ++ kb.deferred).Perm kb.plan :=
  List.filter_append_perm _ _

theorem accepted_length_add_deferred_length (kb : KB) :
    kb.accepted.length + kb.deferred.length = kb.plan.length := by
  have := (accepted_append_deferred_perm kb).length_eq
  simpa using this

theorem mem_accepted_resolves {kb : KB} {p : Proposal} (h : p ∈ kb.accepted) :
    kb.resolvesB p = true := by
  simpa using (List.mem_filter.1 h).2

theorem mem_deferred_not_resolves {kb : KB} {p : Proposal} (h : p ∈ kb.deferred) :
    kb.resolvesB p = false := by
  simpa using (List.mem_filter.1 h).2

/-- **Every flagged issue is dealt with**: it has a recommended repair, or a
candidate held back for review — never neither. -/
theorem coverage {kb : KB} {i : Issue} (h : i ∈ kb.flagged) :
    (∃ p ∈ kb.accepted, p.issue = i) ∨ (∃ p ∈ kb.deferred, p.issue = i) := by
  obtain ⟨p, hp, hpi⟩ := plan_covers h
  by_cases hr : kb.resolvesB p = true
  · exact Or.inl ⟨p, List.mem_filter.2 ⟨hp, by simpa using hr⟩, hpi⟩
  · simp only [Bool.not_eq_true] at hr
    exact Or.inr ⟨p, List.mem_filter.2 ⟨hp, by simp [hr]⟩, hpi⟩

/-- The base a reviewer would get by accepting everything the workflow
recommends.  It is a *candidate*: the workflow itself never writes it back. -/
def autofix (kb : KB) : KB := kb.applyProposals kb.accepted

theorem autofix_score_le (kb : KB) : kb.autofix.score ≤ kb.score :=
  applyProposals_score_le _ kb

theorem autofix_errors_subset (kb : KB) : ∀ e ∈ kb.autofix.errors, e ∈ kb.errors :=
  applyProposals_errors_subset _ kb

theorem autofix_warnings_subset (kb : KB) : ∀ w ∈ kb.autofix.warnings, w ∈ kb.warnings :=
  applyProposals_warnings_subset _ kb

theorem autofix_valid {kb : KB} (hv : kb.valid = true) : kb.autofix.valid = true :=
  applyProposals_valid _ hv

/-- With nothing to recommend, the workflow is the identity. -/
theorem autofix_eq_self_of_accepted_nil {kb : KB} (h : kb.accepted = []) : kb.autofix = kb := by
  rw [autofix, h, applyProposals_nil]

theorem flagged_eq_nil_iff_clean {kb : KB} : kb.flagged = [] ↔ kb.clean = true := by
  rw [flagged, clean, List.append_eq_nil_iff]
  simp [List.isEmpty_iff]

theorem plan_eq_nil_of_clean {kb : KB} (h : kb.clean = true) : kb.plan = [] := by
  rw [plan, flagged_eq_nil_iff_clean.2 h]
  rfl

theorem accepted_eq_nil_of_clean {kb : KB} (h : kb.clean = true) : kb.accepted = [] := by
  rw [accepted, plan_eq_nil_of_clean h]
  rfl

/-- **A clean base is a fixed point**: there is nothing left to propose. -/
theorem autofix_eq_self_of_clean {kb : KB} (h : kb.clean = true) : kb.autofix = kb :=
  autofix_eq_self_of_accepted_nil (accepted_eq_nil_of_clean h)

/-- The base after `n` rounds of the workflow: each round re-reads the data,
re-plans, and applies what it can prove. -/
def rounds (kb : KB) : ℕ → KB
  | 0 => kb
  | n + 1 => (kb.rounds n).autofix

@[simp] theorem rounds_zero (kb : KB) : kb.rounds 0 = kb := rfl

theorem rounds_succ (kb : KB) (n : ℕ) : kb.rounds (n + 1) = (kb.rounds n).autofix := rfl

/-- **The repair history only improves the base**: the debt is antitone in the
number of rounds. -/
theorem rounds_score_antitone (kb : KB) {m n : ℕ} (h : m ≤ n) :
    (kb.rounds n).score ≤ (kb.rounds m).score := by
  induction n, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih => exact (autofix_score_le (kb.rounds n)).trans ih

/-- **No round ever introduces an error.** -/
theorem rounds_errors_subset (kb : KB) {m n : ℕ} (h : m ≤ n) :
    ∀ e ∈ (kb.rounds n).errors, e ∈ (kb.rounds m).errors := by
  induction n, h using Nat.le_induction with
  | base => exact fun _ he => he
  | succ n _ ih => exact fun e he => ih e (autofix_errors_subset (kb.rounds n) e he)

/-- **The workflow terminates**: once a round has left a clean base, no later
round changes anything. -/
theorem rounds_stabilises {kb : KB} {m : ℕ} (h : (kb.rounds m).clean = true) :
    ∀ {n : ℕ}, m ≤ n → kb.rounds n = kb.rounds m := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => rw [rounds_succ, ih, autofix_eq_self_of_clean h]

/-- **A valid base stays valid however long the workflow runs.** -/
theorem rounds_valid {kb : KB} (hv : kb.valid = true) (n : ℕ) : (kb.rounds n).valid = true := by
  induction n with
  | zero => exact hv
  | succ n ih => exact autofix_valid ih

/-! ## The same workflow, computed through the closure tables

The definitions above recompute the transitive closure of the class hierarchy for
every pair of items, which is what makes them easy to reason about and slow to
run.  The tool runs the definitions below instead: each is proved equal to the
one the theorems are about, so nothing is taken on trust. -/

/-- `flagged`, computed through the closure table. -/
def flaggedFast (kb : KB) : List Issue := kb.errorsFast ++ kb.warningsFast

@[simp] theorem flaggedFast_eq (kb : KB) : kb.flaggedFast = kb.flagged := by
  rw [flaggedFast, flagged, errorsFast_eq, warningsFast_eq]

/-- `score`, computed through the closure table. -/
def scoreFast (kb : KB) : ℕ :=
  4 * kb.errorsFast.length + 2 * kb.warningsFast.length + kb.statementCount

@[simp] theorem scoreFast_eq (kb : KB) : kb.scoreFast = kb.score := by
  rw [scoreFast, score, errorsFast_eq, warningsFast_eq]

/-- `noRegressionB`, computed through the closure tables. -/
def noRegressionFastB (kb kb' : KB) : Bool :=
  kb'.errorsFast.all (fun e => decide (e ∈ kb.errorsFast)) &&
    kb'.warningsFast.all (fun w => decide (w ∈ kb.warningsFast))

@[simp] theorem noRegressionFastB_eq (kb kb' : KB) :
    noRegressionFastB kb kb' = noRegressionB kb kb' := by
  rw [noRegressionFastB, noRegressionB, errorsFast_eq, errorsFast_eq, warningsFast_eq,
    warningsFast_eq]

/-- `resolvesB`, computed through the closure tables. -/
def resolvesFastB (kb : KB) (p : Proposal) : Bool :=
  decide (p.issue ∈ kb.flaggedFast) &&
    !decide (p.issue ∈ (kb.patch p.edits).flaggedFast) &&
    noRegressionFastB kb (kb.patch p.edits) &&
    decide ((kb.patch p.edits).scoreFast < kb.scoreFast)

@[simp] theorem resolvesFastB_eq (kb : KB) (p : Proposal) :
    kb.resolvesFastB p = kb.resolvesB p := by
  rw [resolvesFastB, resolvesB, flaggedFast_eq, flaggedFast_eq, noRegressionFastB_eq,
    scoreFast_eq, scoreFast_eq]

/-- `plan`, computed through the closure table. -/
def planFast (kb : KB) : List Proposal := kb.flaggedFast.flatMap kb.repairsOfIssue

@[simp] theorem planFast_eq (kb : KB) : kb.planFast = kb.plan := by
  rw [planFast, plan, flaggedFast_eq]

/-- `applyProposal`, with the check computed through the closure tables. -/
def applyProposalFast (kb : KB) (p : Proposal) : KB :=
  if kb.resolvesFastB p then kb.patch p.edits else kb

@[simp] theorem applyProposalFast_eq (kb : KB) (p : Proposal) :
    kb.applyProposalFast p = kb.applyProposal p := by
  rw [applyProposalFast, applyProposal, resolvesFastB_eq]

/-- `applyProposals`, with the checks computed through the closure tables. -/
def applyProposalsFast (kb : KB) (ps : List Proposal) : KB := ps.foldl applyProposalFast kb

@[simp] theorem applyProposalsFast_eq : ∀ (ps : List Proposal) (kb : KB),
    kb.applyProposalsFast ps = kb.applyProposals ps
  | [], _ => rfl
  | p :: ps, kb => by
      rw [applyProposalsFast, List.foldl_cons, applyProposalFast_eq]
      exact applyProposalsFast_eq ps _

/-- `accepted`, computed through the closure tables. -/
def acceptedFast (kb : KB) : List Proposal := kb.planFast.filter (fun p => kb.resolvesFastB p)

@[simp] theorem acceptedFast_eq (kb : KB) : kb.acceptedFast = kb.accepted := by
  rw [acceptedFast, accepted, planFast_eq]
  exact List.filter_congr fun p _ => by rw [resolvesFastB_eq]

/-- `autofix`, computed through the closure tables. -/
def autofixFast (kb : KB) : KB := kb.applyProposalsFast kb.acceptedFast

@[simp] theorem autofixFast_eq (kb : KB) : kb.autofixFast = kb.autofix := by
  rw [autofixFast, autofix, acceptedFast_eq, applyProposalsFast_eq]

/-! ## The proved fix of the old engine is recommended by the new check -/

/-- Deleting a `subclass of` statement of a valid base whose deletion changes no
derived fact cannot make another statement redundant. -/
theorem dropSub_isRedundantSubB_le {kb : KB} {e : Qid × Qid} (hv : kb.valid = true)
    (hred : kb.isRedundantSubB e = true) (x : Qid × Qid)
    (h : (kb.dropSub e).isRedundantSubB x = true) : kb.isRedundantSubB x = true := by
  have hcls := dropSub_isSubclassOf (kb := kb) (e := e) hv hred
  rw [isRedundantSubB, Bool.and_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨hx, c, hc, hcond⟩ := h
  refine ⟨by simpa using dropSub_sub_subset (by simpa using hx), c, hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcond ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcond
  exact ⟨⟨⟨h1, h2⟩, dropSub_sub_subset h3⟩, by rwa [hcls] at h4⟩

theorem dropSub_warnings_subset {kb : KB} {e : Qid × Qid} (hv : kb.valid = true)
    (hred : kb.isRedundantSubB e = true) :
    ∀ w ∈ (kb.dropSub e).warnings, w ∈ kb.warnings := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
  rw [redundantSubL, List.mem_filter] at hx
  refine List.mem_map.2 ⟨x, ?_, rfl⟩
  rw [redundantSubL, List.mem_filter]
  exact ⟨dropSub_sub_subset hx.1, dropSub_isRedundantSubB_le hv hred x hx.2⟩

theorem dropSub_warnings_length_le {kb : KB} {e : Qid × Qid} (hv : kb.valid = true)
    (hred : kb.isRedundantSubB e = true) :
    (kb.dropSub e).warnings.length ≤ kb.warnings.length := by
  rw [warnings, warnings, List.length_map, List.length_map, redundantSubL, redundantSubL,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  show List.countP _ (List.filter (fun r => r != e) kb.sub) ≤ _
  rw [List.countP_filter]
  refine List.countP_mono_left ?_
  intro x hx hcond
  simp only [Bool.and_eq_true] at hcond
  exact dropSub_isRedundantSubB_le hv hred x hcond.1

/-- **The repair the library had already proved lossless passes the new check.**
The deletion of a redundant `subclass of` statement is recommended, not merely
tolerated. -/
theorem redundant_proposal_resolves {kb : KB} (hv : kb.valid = true) {a b : Qid}
    (hw : Issue.redundantSubclass a b ∈ kb.warnings) (why : String) :
    kb.resolvesB ⟨.redundantSubclass a b, [.dropSub a b], why⟩ = true := by
  have hmem : (a, b) ∈ kb.sub := (mem_warnings_iff.1 hw).1
  have hred : kb.isRedundantSubB (a, b) = true := (mem_warnings_iff.1 hw).2
  have hpatch : kb.patch [Edit.dropSub a b] = kb.dropSub (a, b) := rfl
  obtain ⟨hval, -, -⟩ := warning_prunable hv hw
  have herr : (kb.dropSub (a, b)).errors = [] := errors_eq_nil_iff_valid.2 hval
  have herr0 : kb.errors = [] := errors_eq_nil_iff_valid.2 hv
  have hnotmem : (a, b) ∉ (kb.dropSub (a, b)).sub := by
    simp [dropSub, List.mem_filter]
  have hgone : Issue.redundantSubclass a b ∉ (kb.dropSub (a, b)).flagged := by
    intro hcon
    rcases List.mem_append.1 hcon with h | h
    · rw [herr] at h; exact absurd h List.not_mem_nil
    · exact hnotmem (mem_warnings_iff.1 h).1
  have hnoreg : noRegressionB kb (kb.dropSub (a, b)) = true := by
    rw [noRegressionB, Bool.and_eq_true]
    constructor
    · rw [herr]; rfl
    · rw [List.all_eq_true]
      intro w hw'
      simpa using dropSub_warnings_subset hv hred w hw'
  have hcount : (kb.dropSub (a, b)).statementCount < kb.statementCount := by
    have := dropSub_length_lt (kb := kb) (e := (a, b)) hmem
    simp only [statementCount, dropSub_inst, dropSub_disj]
    omega
  have hwl : (kb.dropSub (a, b)).warnings.length ≤ kb.warnings.length :=
    dropSub_warnings_length_le hv hred
  have hscore : (kb.dropSub (a, b)).score < kb.score := by
    simp only [score, herr, herr0, List.length_nil]
    omega
  rw [resolvesB]
  simp only [hpatch, hnoreg, hscore]
  simp [hgone, mem_flagged_of_mem_warnings hw]

end KB

end Wikidata
