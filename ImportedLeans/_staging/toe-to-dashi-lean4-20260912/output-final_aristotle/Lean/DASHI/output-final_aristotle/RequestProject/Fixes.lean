import RequestProject.Defects
import RequestProject.Reports

/-!
# From witnessed issues to checked repairs

`RequestProject.Reports` turns every diagnostic of the library into a row that
names the items the problem is about and the action suggested for it.  This file
turns those suggestions into *data* — `Wikidata.FixAction` — and applies them.

The one thing a repair engine must not do is trade one defect for another, so
nothing here is applied on trust:

* `Wikidata.KB.applyFix` performs a single action;
* `Wikidata.KB.applyFixSafe` performs it **only if** the result answers every
  `subclass of` / `instance of` question about the items of the base exactly as
  before (`Wikidata.KB.answersAgreeB`), carries no more errors than the base, and
  makes progress — it removes an error, or it removes a statement
  (`Wikidata.KB.improvesB`);
* `Wikidata.KB.applyFixes` folds that over a list of actions, and
  `Wikidata.KB.repair` runs it on the actions suggested by the report itself.

What is proved about the result:

* `Wikidata.KB.applyFixes_valid` — repairing a valid base leaves a valid base;
* `Wikidata.KB.applyFixes_errors_le`, `Wikidata.KB.repair_errors_le` — a repair
  never introduces an error: no candidate the engine offers is worse than the
  base it came from;
* `Wikidata.KB.applyFixes_isSubclassOf`, `applyFixes_isInstanceOf` — no fact
  about a declared item is gained or lost by the repair;
* `Wikidata.KB.dropSub_mem_fixes_iff` — the only statement the engine ever
  deletes by itself is a redundant `subclass of`, i.e. exactly the rows the
  report marks `proven-fix`; every destructive repair is a `review` action,
  which by `Wikidata.KB.applyFix_review` changes nothing;
* `Wikidata.KB.redundant_fix_accepted` — and that deletion is always accepted:
  the check cannot reject a fix the library has proved lossless.
-/

namespace Wikidata

open Cli (qidText)

/-- A remediation action: what to do about a witnessed issue. -/
inductive FixAction where
  /-- Delete a `subclass of` statement. -/
  | dropSub (a b : Qid)
  /-- Delete an `instance of` statement. -/
  | dropInst (a c : Qid)
  /-- Delete a disjointness declaration. -/
  | dropDisj (c d : Qid)
  /-- Declare an item the statements refer to but the base does not list. -/
  | declareItem (q : Qid)
  /-- Nothing can be done automatically: the issue needs a human decision.  The
  fields are the error type and the item it is reported against. -/
  | review (code subject : String)
deriving DecidableEq, Repr, Inhabited

/-- The action, in one line, as the tool prints it. -/
def FixAction.text : FixAction → String
  | .dropSub a b => s!"delete `subclass of` {qidText a} → {qidText b}"
  | .dropInst a c => s!"delete `instance of` {qidText a} → {qidText c}"
  | .dropDisj c d => s!"delete the disjointness of {qidText c} and {qidText d}"
  | .declareItem q => s!"declare the missing item {qidText q}"
  | .review code subject => s!"review by hand: {code} at {subject}"

namespace KB

/-! ## Performing one action -/

/-- The base after one action.  A `review` action changes nothing. -/
def applyFix (kb : KB) : FixAction → KB
  | .dropSub a b => kb.dropSub (a, b)
  | .dropInst a c => { kb with inst := kb.inst.filter (fun r => r != (a, c)) }
  | .dropDisj c d => { kb with disj := kb.disj.filter (fun r => r != (c, d)) }
  | .declareItem q => if kb.items.contains q then kb else { kb with items := kb.items ++ [q] }
  | .review _ _ => kb

/-- **A `review` action is never performed automatically.** -/
@[simp] theorem applyFix_review (kb : KB) (code subject : String) :
    kb.applyFix (.review code subject) = kb := rfl

/-- No action ever undeclares an item. -/
theorem mem_applyFix_items {kb : KB} {f : FixAction} {q : Qid} (h : q ∈ kb.items) :
    q ∈ (kb.applyFix f).items := by
  cases f with
  | dropSub a b => exact h
  | dropInst a c => exact h
  | dropDisj c d => exact h
  | declareItem p =>
      by_cases hp : p ∈ kb.items
      · simpa [applyFix, hp] using h
      · simp only [applyFix, List.contains_eq_mem, decide_eq_true_eq, hp, if_false]
        exact List.mem_append_left _ h
  | review c s => exact h

/-! ## Performing an action only if it is safe -/

/-- The check the engine runs before accepting a repair: the candidate answers
every `subclass of` and `instance of` question about the declared items of the
base exactly as the base does. -/
def answersAgreeB (kb kb' : KB) : Bool :=
  kb.items.all fun a => kb.items.all fun b =>
    (kb'.isSubclassOf a b == kb.isSubclassOf a b) && (kb'.isInstanceOf a b == kb.isInstanceOf a b)

theorem answersAgree_of_agreeB {kb kb' : KB} (h : answersAgreeB kb kb' = true)
    {a b : Qid} (ha : a ∈ kb.items) (hb : b ∈ kb.items) :
    kb'.isSubclassOf a b = kb.isSubclassOf a b ∧ kb'.isInstanceOf a b = kb.isInstanceOf a b := by
  rw [answersAgreeB, List.all_eq_true] at h
  have h2 := h a (by simpa using ha)
  rw [List.all_eq_true] at h2
  have h3 := h2 b (by simpa using hb)
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  exact h3

/-- The size of a base: how many statements it carries. -/
def statementCount (kb : KB) : ℕ := kb.sub.length + kb.inst.length + kb.disj.length

/-- The check the engine runs before accepting a repair: the candidate must
answer every question the way the base did, must not carry more errors than the
base, and must make progress — it removes an error, or it removes a statement. -/
def improvesB (kb kb' : KB) : Bool :=
  answersAgreeB kb kb' && decide (kb'.errors.length ≤ kb.errors.length) &&
    (decide (kb'.errors.length < kb.errors.length) ||
      decide (kb'.statementCount < kb.statementCount))

/-- One repair, applied only if it passes that check. -/
def applyFixSafe (kb : KB) (f : FixAction) : KB :=
  let kb' := kb.applyFix f
  if improvesB kb kb' then kb' else kb

/-! ### The same checks, computed through the closure tables

The definitions above recompute the transitive closure for every pair of items.
The tool runs these instead: each is proved equal to the definition the theorems
are about, so nothing is taken on trust. -/

/-- `answersAgreeB`, evaluated against the closure tables of the two bases. -/
def answersAgreeFastB (kb kb' : KB) : Bool :=
  let T := kb.closureTable
  let T' := kb'.closureTable
  kb.items.all fun a => kb.items.all fun b =>
    (kb'.isSubclassOfT T' a b == kb.isSubclassOfT T a b) &&
      (kb'.isInstanceOfT T' a b == kb.isInstanceOfT T a b)

@[simp] theorem answersAgreeFastB_eq (kb kb' : KB) :
    answersAgreeFastB kb kb' = answersAgreeB kb kb' := by
  simp [answersAgreeFastB, answersAgreeB]

/-- `improvesB`, with both the answers and the error lists computed fast. -/
def improvesFastB (kb kb' : KB) : Bool :=
  answersAgreeFastB kb kb' && decide (kb'.errorsFast.length ≤ kb.errorsFast.length) &&
    (decide (kb'.errorsFast.length < kb.errorsFast.length) ||
      decide (kb'.statementCount < kb.statementCount))

@[simp] theorem improvesFastB_eq (kb kb' : KB) : improvesFastB kb kb' = improvesB kb kb' := by
  simp [improvesFastB, improvesB]

/-- A `review` action makes no progress, so the check refuses it: there is nothing
to compute. -/
theorem applyFixSafe_review (kb : KB) (code subject : String) :
    applyFixSafe kb (.review code subject) = kb := by
  have h : improvesB kb (kb.applyFix (.review code subject)) = false := by
    rw [applyFix_review, improvesB]
    simp
  rw [applyFixSafe]
  simp [h]

/-- `applyFixSafe`, as the tool computes it: the checks run through the closure
tables, and a request for review is refused without computing anything. -/
def applyFixSafeFast (kb : KB) (f : FixAction) : KB :=
  match f with
  | .review _ _ => kb
  | f =>
      let kb' := kb.applyFix f
      if improvesFastB kb kb' then kb' else kb

/-- **The tool performs exactly the repairs the theorems are about.** -/
@[simp] theorem applyFixSafeFast_eq (kb : KB) (f : FixAction) :
    applyFixSafeFast kb f = applyFixSafe kb f := by
  cases f with
  | review c s => rw [applyFixSafeFast, applyFixSafe_review]
  | _ => simp [applyFixSafeFast, applyFixSafe]

/-- Either the action was refused, or it was performed and the result is
certified: it answers exactly as before and carries no new error. -/
theorem applyFixSafe_spec (kb : KB) (f : FixAction) :
    applyFixSafe kb f = kb ∨
      (applyFixSafe kb f = kb.applyFix f ∧
        (kb.applyFix f).errors.length ≤ kb.errors.length ∧
        answersAgreeB kb (kb.applyFix f) = true) := by
  by_cases h : improvesB kb (kb.applyFix f) = true
  · have h' := h
    rw [improvesB, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h'
    exact Or.inr ⟨by simp [applyFixSafe, h], h'.1.2, h'.1.1⟩
  · exact Or.inl (by simp [applyFixSafe, h])

/-- **A repair never introduces an error.** -/
theorem applyFixSafe_errors_le (kb : KB) (f : FixAction) :
    (applyFixSafe kb f).errors.length ≤ kb.errors.length := by
  rcases applyFixSafe_spec kb f with h | ⟨h, hle, -⟩
  · rw [h]
  · rw [h]; exact hle

theorem applyFixSafe_valid {kb : KB} (hv : kb.valid = true) (f : FixAction) :
    (applyFixSafe kb f).valid = true := by
  rw [← errors_eq_nil_iff_valid, ← List.length_eq_zero_iff] at hv ⊢
  exact Nat.le_zero.1 (hv ▸ applyFixSafe_errors_le kb f)

theorem mem_applyFixSafe_items {kb : KB} {f : FixAction} {q : Qid} (h : q ∈ kb.items) :
    q ∈ (applyFixSafe kb f).items := by
  rcases applyFixSafe_spec kb f with hs | ⟨hs, -, -⟩
  · rw [hs]; exact h
  · rw [hs]; exact mem_applyFix_items h

theorem applyFixSafe_answers {kb : KB} {f : FixAction} {a b : Qid}
    (ha : a ∈ kb.items) (hb : b ∈ kb.items) :
    (applyFixSafe kb f).isSubclassOf a b = kb.isSubclassOf a b ∧
      (applyFixSafe kb f).isInstanceOf a b = kb.isInstanceOf a b := by
  rcases applyFixSafe_spec kb f with hs | ⟨hs, -, hag⟩
  · rw [hs]; exact ⟨rfl, rfl⟩
  · rw [hs]; exact answersAgree_of_agreeB hag ha hb

/-! ## Performing a list of actions -/

/-- The candidate base: every action tried in turn, each accepted only if it is
safe. -/
def applyFixes (kb : KB) (fs : List FixAction) : KB := fs.foldl applyFixSafe kb

@[simp] theorem applyFixes_nil (kb : KB) : applyFixes kb [] = kb := rfl

theorem applyFixes_cons (kb : KB) (f : FixAction) (fs : List FixAction) :
    applyFixes kb (f :: fs) = applyFixes (applyFixSafe kb f) fs := rfl

/-- **A repair never introduces an error**: the candidate has no more errors than
the base it repairs. -/
theorem applyFixes_errors_le : ∀ (fs : List FixAction) (kb : KB),
    (applyFixes kb fs).errors.length ≤ kb.errors.length
  | [], _ => Nat.le_refl _
  | f :: fs, kb => by
      rw [applyFixes_cons]
      exact (applyFixes_errors_le fs _).trans (applyFixSafe_errors_le kb f)

/-- **Repairing a valid base leaves a valid base.** -/
theorem applyFixes_valid : ∀ (fs : List FixAction) {kb : KB}, kb.valid = true →
    (applyFixes kb fs).valid = true
  | [], _, hv => hv
  | f :: fs, kb, hv => by
      rw [applyFixes_cons]
      exact applyFixes_valid fs (applyFixSafe_valid hv f)

theorem mem_applyFixes_items : ∀ (fs : List FixAction) {kb : KB} {q : Qid}, q ∈ kb.items →
    q ∈ (applyFixes kb fs).items
  | [], _, _, h => h
  | f :: fs, kb, q, h => by
      rw [applyFixes_cons]
      exact mem_applyFixes_items fs (mem_applyFixSafe_items h)

/-- **No knowledge is lost or gained**: the candidate answers every `subclass of`
question about the declared items exactly as the base does. -/
theorem applyFixes_answers : ∀ (fs : List FixAction) {kb : KB} {a b : Qid},
    a ∈ kb.items → b ∈ kb.items →
      (applyFixes kb fs).isSubclassOf a b = kb.isSubclassOf a b ∧
        (applyFixes kb fs).isInstanceOf a b = kb.isInstanceOf a b
  | [], _, _, _, _, _ => ⟨rfl, rfl⟩
  | f :: fs, kb, a, b, ha, hb => by
      rw [applyFixes_cons]
      obtain ⟨h1, h2⟩ :=
        applyFixes_answers fs (mem_applyFixSafe_items (f := f) ha)
          (mem_applyFixSafe_items (f := f) hb)
      obtain ⟨h3, h4⟩ := applyFixSafe_answers (f := f) ha hb
      exact ⟨h1.trans h3, h2.trans h4⟩

theorem applyFixes_isSubclassOf (fs : List FixAction) {kb : KB} {a b : Qid}
    (ha : a ∈ kb.items) (hb : b ∈ kb.items) :
    (applyFixes kb fs).isSubclassOf a b = kb.isSubclassOf a b :=
  (applyFixes_answers fs ha hb).1

theorem applyFixes_isInstanceOf (fs : List FixAction) {kb : KB} {a c : Qid}
    (ha : a ∈ kb.items) (hc : c ∈ kb.items) :
    (applyFixes kb fs).isInstanceOf a c = kb.isInstanceOf a c :=
  (applyFixes_answers fs ha hc).2


/-! ## The actions the report suggests -/

/-- The action for an issue that no rule can repair by itself. -/
def reviewFix (i : Issue) : FixAction :=
  .review (Report.rowOfIssue i).code (Report.rowOfIssue i).subject

/-- The declaration an undeclared endpoint calls for, if it is undeclared. -/
def declareMissing (kb : KB) (q : Qid) : List FixAction :=
  if kb.items.contains q then [] else [.declareItem q]

/-- The actions suggested for one issue: declare what a dangling statement points
at, delete a redundant `subclass of` statement, and otherwise ask for a human. -/
def fixesOfIssue (kb : KB) : Issue → List FixAction
  | .danglingSub a b => kb.declareMissing a ++ kb.declareMissing b
  | .danglingInst a c => kb.declareMissing a ++ kb.declareMissing c
  | .danglingDisj c d => kb.declareMissing c ++ kb.declareMissing d
  | .redundantSubclass a b => [.dropSub a b]
  | i => [reviewFix i]

/-- Every action the report of a base suggests, in the order of the report. -/
def suggestedFixes (kb : KB) : List FixAction :=
  (kb.errors ++ kb.warnings).flatMap kb.fixesOfIssue

/-- The style warnings of a base, through the closure table. -/
def warningsFast (kb : KB) : List Issue :=
  kb.redundantSubLFast.map (fun r => Issue.redundantSubclass r.1 r.2)

@[simp] theorem warningsFast_eq (kb : KB) : kb.warningsFast = kb.warnings := by
  rw [warningsFast, warnings, redundantSubLFast_eq]

/-- `suggestedFixes`, as the tool computes it.  The scan for redundant statements
is quadratic, so the tool can leave the style warnings out; with `warn := true`
this is `suggestedFixes`. -/
def suggestedFixesFast (kb : KB) (warn : Bool) : List FixAction :=
  (kb.errorsFast ++ (if warn then kb.warningsFast else [])).flatMap kb.fixesOfIssue

@[simp] theorem suggestedFixesFast_eq (kb : KB) :
    kb.suggestedFixesFast true = kb.suggestedFixes := by
  rw [suggestedFixesFast, suggestedFixes, errorsFast_eq, if_pos rfl, warningsFast_eq]

/-- The candidate base: the report of `kb`, turned into actions and applied to it,
each action accepted only if it is safe. -/
def repair (kb : KB) : KB := kb.applyFixes kb.suggestedFixes

/-- **The candidate is never worse than the base**: it carries no error the base
did not already carry — the count cannot go up. -/
theorem repair_errors_le (kb : KB) : kb.repair.errors.length ≤ kb.errors.length :=
  applyFixes_errors_le _ kb

theorem repair_valid {kb : KB} (hv : kb.valid = true) : kb.repair.valid = true :=
  applyFixes_valid _ hv

theorem repair_isSubclassOf {kb : KB} {a b : Qid} (ha : a ∈ kb.items) (hb : b ∈ kb.items) :
    kb.repair.isSubclassOf a b = kb.isSubclassOf a b :=
  applyFixes_isSubclassOf _ ha hb

theorem repair_isInstanceOf {kb : KB} {a c : Qid} (ha : a ∈ kb.items) (hc : c ∈ kb.items) :
    kb.repair.isInstanceOf a c = kb.isInstanceOf a c :=
  applyFixes_isInstanceOf _ ha hc

/-! ## Only the proved fix deletes anything -/

theorem mem_declareMissing {kb : KB} {q : Qid} {f : FixAction} (h : f ∈ kb.declareMissing q) :
    f = .declareItem q := by
  by_cases hq : q ∈ kb.items
  · simp [declareMissing, hq] at h
  · simp [declareMissing, hq] at h
    simp [h]

/-- **The engine deletes a statement only where the report says the deletion is
proved lossless.**  Every other repair it proposes is a declaration or a request
for review. -/
theorem dropSub_mem_fixes_iff {kb : KB} {i : Issue} {a b : Qid} :
    FixAction.dropSub a b ∈ kb.fixesOfIssue i ↔ i = .redundantSubclass a b := by
  constructor
  · intro h
    cases i with
    | danglingSub x y =>
        rcases List.mem_append.1 h with h | h <;>
          exact absurd (mem_declareMissing h) (by simp)
    | danglingInst x y =>
        rcases List.mem_append.1 h with h | h <;>
          exact absurd (mem_declareMissing h) (by simp)
    | danglingDisj x y =>
        rcases List.mem_append.1 h with h | h <;>
          exact absurd (mem_declareMissing h) (by simp)
    | redundantSubclass x y => simpa [fixesOfIssue, eq_comm] using h
    | _ => simp [fixesOfIssue, reviewFix, Report.rowOfIssue] at h
  · rintro rfl
    simp [fixesOfIssue]

/-- The issues whose repair the engine performs are exactly the rows the report
marks `proven-fix`. -/
theorem status_of_dropSub_mem_fixes {kb : KB} {i : Issue} {a b : Qid}
    (h : FixAction.dropSub a b ∈ kb.fixesOfIssue i) :
    (Report.rowOfIssue i).status = .provenFix := by
  rw [dropSub_mem_fixes_iff.1 h]
  rfl

/-- **A proved fix is never refused**: deleting a redundant `subclass of`
statement of a valid base passes the safety check, so the engine really does
perform it. -/
theorem redundant_fix_accepted {kb : KB} (hv : kb.valid = true) {a b : Qid}
    (hw : Issue.redundantSubclass a b ∈ kb.warnings) :
    applyFixSafe kb (.dropSub a b) = kb.dropSub (a, b) := by
  obtain ⟨hval, hsub, hinst⟩ := warning_prunable hv hw
  have hag : answersAgreeB kb (kb.dropSub (a, b)) = true := by
    rw [answersAgreeB, List.all_eq_true]
    intro x _
    rw [List.all_eq_true]
    intro y _
    simp [hsub x y, hinst x y]
  have hsize : (kb.dropSub (a, b)).statementCount < kb.statementCount := by
    have hmem : (a, b) ∈ kb.sub := (mem_warnings_iff.1 hw).1
    have := dropSub_length_lt (kb := kb) (e := (a, b)) hmem
    simp only [statementCount, dropSub_inst, dropSub_disj]
    omega
  have herr : (kb.dropSub (a, b)).errors.length ≤ kb.errors.length := by
    have h0 : (kb.dropSub (a, b)).errors.length = 0 :=
      List.length_eq_zero_iff.2 (errors_eq_nil_iff_valid.2 hval)
    omega
  have hcond : improvesB kb (kb.applyFix (.dropSub a b)) = true := by
    show improvesB kb (kb.dropSub (a, b)) = true
    rw [improvesB, hag]
    simp [herr, hsize]
  rw [applyFixSafe]
  simp only [hcond, if_true]
  rfl

end KB

end Wikidata
