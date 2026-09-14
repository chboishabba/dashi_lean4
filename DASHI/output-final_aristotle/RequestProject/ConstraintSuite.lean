import RequestProject.Qualifiers
import RequestProject.FormatConstraints
import RequestProject.ContemporaryConstraint
import RequestProject.CardinalityConstraints

/-!
# The statement-level constraint suite

The property constraints of Wikidata are checked together, not one at a time: a
constraint report for a base lists, for each kind of constraint, whether the base
violates it.  This file collects the statement-level checks of the development
into a single profile and a single run.

* `Wikidata.ConstraintProfile` gathers the qualifier profiles (allowed and
  mandatory qualifiers), the property scopes, the range constraints, the format
  constraints and the contemporary constraints of a base, and
  `ConstraintProfile.checkAll` runs them all.  `checkAll_iff` characterises the
  combined run as the conjunction of the individual ones, and `checkAll_empty`
  says the empty profile accepts everything.
* `Wikidata.Violation` names the six kinds of defect and
  `ConstraintProfile.report` lists the kinds a base violates.  The report is
  honest: `mem_report_iff` says a kind is listed exactly when the corresponding
  check fails, and `report_eq_nil_iff` says the report is empty exactly when the
  combined run succeeds.
* Four of the six checks are **downward closed** along sublists of the claim set,
  hence hold of the truthy fragment of a conforming base
  (`checkClosed_sublist`, `checkClosed_truthy`).  The contemporary check is
  **not**: `contemporary_not_truthy_closed` exhibits a base that satisfies it
  while its truthy fragment does not, because ranks decide which date is read as
  the start of an existence.  So a constraint report has to be run on the same
  fragment it is reported for.

A worked fragment runs the whole suite on a small base of population statements
and identifiers, once as it stands -- where the report lists exactly the range and
the format defect -- and once repaired, where the report is empty; two competing
capitals are reported as a cardinality defect.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

/-- The statement-level constraints of a base, gathered in one place. -/
structure ConstraintProfile where
  /-- Allowed and mandatory qualifiers, per property. -/
  quals : List QualSpec := []
  /-- Property scopes: in which slot a property may be used. -/
  scopes : List ScopeSpec := []
  /-- Range constraints. -/
  ranges : List RangeSpec := []
  /-- Format constraints. -/
  formats : List FormatSpec := []
  /-- Cardinality constraints. -/
  cards : List CardSpec := []
  /-- Contemporary constraints. -/
  contemporaries : List ContemporarySpec := []

/-- The kinds of constraint a base can violate. -/
inductive Violation where
  /-- An allowed- or mandatory-qualifiers constraint. -/
  | qualifiers
  /-- A property-scope constraint. -/
  | scope
  /-- A range constraint. -/
  | range
  /-- A format constraint. -/
  | format
  /-- A cardinality constraint. -/
  | cardinality
  /-- A contemporary constraint. -/
  | contemporary
deriving DecidableEq, Repr, Inhabited

namespace ConstraintProfile

variable (P : ConstraintProfile) (cs : Claim.Set)

/-- The cardinality part of the run. -/
def cardOk : Bool := P.cards.all fun s => s.setOk cs

/-- The contemporary part of the run. -/
def contemporaryOk : Bool := P.contemporaries.all fun s => s.setOk cs

/-- The four checks that only look at the claims individually, and are therefore
preserved by removing claims. -/
def checkClosed : Bool :=
  qualSetOk P.quals cs && scopeOk P.scopes cs && rangeOk P.ranges cs && formatOk P.formats cs

/-- The whole suite. -/
def checkAll : Bool := P.checkClosed cs && P.cardOk cs && P.contemporaryOk cs

theorem checkClosed_iff :
    P.checkClosed cs = true ↔
      qualSetOk P.quals cs = true ∧ scopeOk P.scopes cs = true ∧
        rangeOk P.ranges cs = true ∧ formatOk P.formats cs = true := by
  simp [checkClosed, and_assoc]

theorem checkAll_iff :
    P.checkAll cs = true ↔
      qualSetOk P.quals cs = true ∧ scopeOk P.scopes cs = true ∧
        rangeOk P.ranges cs = true ∧ formatOk P.formats cs = true ∧
        (∀ s ∈ P.cards, s.setOk cs = true) ∧
        ∀ s ∈ P.contemporaries, s.setOk cs = true := by
  simp [checkAll, checkClosed, cardOk, contemporaryOk, and_assoc, List.all_eq_true]

/-- The empty profile accepts every base. -/
@[simp] theorem checkAll_empty (cs : Claim.Set) : checkAll {} cs = true := by
  simp [checkAll, checkClosed, cardOk, contemporaryOk, qualSetOk, scopeOk, rangeOk, formatOk,
    specOf, scopeOf, mainAllowed, qualifierAllowed]

/-- The kinds of constraint the base violates. -/
def report : List Violation :=
  (if qualSetOk P.quals cs then [] else [Violation.qualifiers]) ++
  (if scopeOk P.scopes cs then [] else [Violation.scope]) ++
  (if rangeOk P.ranges cs then [] else [Violation.range]) ++
  (if formatOk P.formats cs then [] else [Violation.format]) ++
  (if P.cardOk cs then [] else [Violation.cardinality]) ++
  (if P.contemporaryOk cs then [] else [Violation.contemporary])

/-- The report is honest: a kind is listed exactly when its check fails. -/
theorem mem_report_iff (v : Violation) :
    v ∈ P.report cs ↔
      (v = .qualifiers ∧ qualSetOk P.quals cs = false) ∨
      (v = .scope ∧ scopeOk P.scopes cs = false) ∨
      (v = .range ∧ rangeOk P.ranges cs = false) ∨
      (v = .format ∧ formatOk P.formats cs = false) ∨
      (v = .cardinality ∧ P.cardOk cs = false) ∨
      (v = .contemporary ∧ P.contemporaryOk cs = false) := by
  unfold report
  cases hq : qualSetOk P.quals cs <;> cases hs : scopeOk P.scopes cs <;>
    cases hr : rangeOk P.ranges cs <;> cases hf : formatOk P.formats cs <;>
      cases hn : P.cardOk cs <;> cases hc : P.contemporaryOk cs <;> cases v <;> simp

/-- The report is empty exactly when the whole suite succeeds. -/
theorem report_eq_nil_iff : P.report cs = [] ↔ P.checkAll cs = true := by
  unfold report checkAll checkClosed
  cases hq : qualSetOk P.quals cs <;> cases hs : scopeOk P.scopes cs <;>
    cases hr : rangeOk P.ranges cs <;> cases hf : formatOk P.formats cs <;>
      cases hn : P.cardOk cs <;> cases hc : P.contemporaryOk cs <;> simp

/-- The four claim-local checks are downward closed along sublists. -/
theorem checkClosed_sublist {cs ds : Claim.Set} (hsub : ds.Sublist cs)
    (h : P.checkClosed cs = true) : P.checkClosed ds = true := by
  rw [checkClosed_iff] at h ⊢
  exact ⟨qualSetOk_sublist hsub h.1, scopeOk_sublist hsub h.2.1,
    rangeOk_sublist hsub h.2.2.1, formatOk_sublist hsub h.2.2.2⟩

/-- In particular they hold of the truthy fragment of a conforming base. -/
theorem checkClosed_truthy {cs : Claim.Set} (h : P.checkClosed cs = true) :
    P.checkClosed (Claim.truthy cs) = true :=
  P.checkClosed_sublist List.filter_sublist h

end ConstraintProfile

/-! ### The contemporary check is not preserved by rank filtering -/

namespace SuiteExample

open RankExample (Q P)

/-- `spouse` (P26) constrained to be contemporary, with the usual date properties. -/
def spouseSpec : ContemporarySpec :=
  { pid := P "P26", starts := [P "P569", P "P571"], ends := [P "P570", P "P576"] }

/-- A base in which `Q1` has two `date of birth` statements, an ordinary one in 1900
and a preferred one in 1990, and is married to `Q2`, who lived 1900-1950. -/
def rankedDates : Claim.Set :=
  [ { subject := Q "Q1", pid := P "P569", value := .time 1900 },
    { subject := Q "Q1", pid := P "P569", value := .time 1990, rank := .preferred },
    { subject := Q "Q2", pid := P "P569", value := .time 1900 },
    { subject := Q "Q2", pid := P "P570", value := .time 1950 },
    { subject := Q "Q1", pid := P "P26", value := .item (Q "Q2") } ]

/-- The base passes the contemporary constraint, but its truthy fragment does not:
unlike the claim-local checks, the contemporary check is **not** preserved by
filtering out the non-truthy statements, because ranks decide which date is read
as the start of an existence. -/
theorem contemporary_not_truthy_closed :
    spouseSpec.setOk rankedDates = true ∧
      spouseSpec.setOk (Claim.truthy rankedDates) = false := by decide

/-! ### Running the whole suite -/

/-- Population must be non-negative; `VIAF ID` must be a nonzero digit followed by
up to five digits; a population statement must carry a `point in time` (P585)
qualifier and nothing else. -/
def profile : ConstraintProfile :=
  { quals := [{ pid := P "P1082", allowed := [P "P585"], mandatory := [P "P585"] }]
    scopes := []
    ranges := [{ pid := P "P1082", lower := .finite 0 }]
    formats := [{ pid := P "P214", pat := FormatExample.viafPat }]
    cards := [{ pid := P "P36", upper := some 1 }]
    contemporaries := [] }

/-- A base with two defects: a negative population and a malformed identifier. -/
def defective : Claim.Set :=
  [ { subject := Q "Q64", pid := P "P1082", value := .quantity (-5),
      quals := [(P "P585", .time 2018)] },
    { subject := Q "Q42", pid := P "P214", value := .str "0bad" } ]

/-- The suite rejects it, and the report names exactly the two constraints it
violates. -/
theorem defective_report :
    profile.report defective = [Violation.range, Violation.format] := by decide

theorem defective_rejected : profile.checkAll defective = false := by decide

/-- The repaired base passes, and its report is empty. -/
def repaired : Claim.Set :=
  [ { subject := Q "Q64", pid := P "P1082", value := .quantity 3644826,
      quals := [(P "P585", .time 2018)] },
    { subject := Q "Q42", pid := P "P214", value := .str "113230" } ]

theorem repaired_accepted : profile.checkAll repaired = true := by decide

theorem repaired_report : profile.report repaired = [] := by decide

/-- Two competing capitals add the cardinality defect to the report. -/
theorem two_capitals_report :
    profile.report
      [ { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") },
        { subject := Q "Q183", pid := P "P36", value := .item (Q "Q365") } ] =
      [Violation.cardinality] := by decide

/-- Dropping the mandatory qualifier adds the qualifier defect to the report. -/
theorem missing_qualifier_report :
    profile.report [{ subject := Q "Q64", pid := P "P1082", value := .quantity 3644826 }] =
      [Violation.qualifiers] := by decide

end SuiteExample

end Wikidata
