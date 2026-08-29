import RequestProject.Temporal

/-!
# The time datatype: dates with a precision

`RequestProject.Temporal` treats a point in time as an integer and studies the
*validity intervals* built from the `start time` (P580) and `end time` (P582)
qualifiers.  This file formalises the other half of Wikidata's treatment of
time: the **time value** itself, which is not a point but a date recorded *to a
stated precision* — `1990`, `May 1990`, `1 May 1990`, `the 19th century` — in a
stated calendar model.

A time value therefore denotes a *set* of instants, namely all the dates that
agree with it as far as its precision reaches, and the two operations one needs
are

* **coarsening**: reading a date at a coarser precision, and
* **compatibility**: whether two time values can refer to the same instant.

Main results:

* reading a date at precision `p` is a function of reading it at any finer
  precision (`Wikidata.Prec.key_refine`), so agreement at a precision is an
  equivalence relation and agreements grow coarser-wards;
* a more precise value denotes fewer instants (`Wikidata.TimeValue.denote_mono`);
* **two time values are compatible exactly when their denotations meet**, and
  that happens exactly when they agree at the coarser of the two precisions
  (`Wikidata.TimeValue.compatible_iff_exists_mem`);
* compatibility is reflexive and symmetric but **not transitive**: `May 1990`
  and `July 1990` are both compatible with `1990` and incompatible with each
  other (`Wikidata.TimeExample.compatible_not_transitive`).

The calendar model (`Julian` vs `Gregorian`) is carried along, and time values
recorded in different calendars are never declared compatible, since the same
label denotes different instants in the two calendars.
-/

namespace Wikidata

/-- A date: a year (negative for BCE), a month and a day.  Fields below the
recorded precision are ignored, so they may be left at `0`. -/
structure Date where
  /-- The year. -/
  year : ℤ
  /-- The month, `1`–`12`, or `0` when unspecified. -/
  month : ℕ := 0
  /-- The day, `1`–`31`, or `0` when unspecified. -/
  day : ℕ := 0
deriving DecidableEq, Repr, Inhabited

/-- The precision of a time value; Wikidata's ladder, restricted to the range
that is actually used for dates. -/
inductive Prec where
  /-- Precision 6: millennium. -/
  | millennium
  /-- Precision 7: century. -/
  | century
  /-- Precision 8: decade. -/
  | decade
  /-- Precision 9: year. -/
  | year
  /-- Precision 10: month. -/
  | month
  /-- Precision 11: day. -/
  | day
deriving DecidableEq, Repr, Inhabited

/-- The calendar model: `proleptic Gregorian calendar` (Q1985727) or `proleptic
Julian calendar` (Q1985786). -/
inductive Calendar where
  /-- The proleptic Gregorian calendar. -/
  | gregorian
  /-- The proleptic Julian calendar. -/
  | julian
deriving DecidableEq, Repr, Inhabited

namespace Prec

/-- How fine a precision is: larger is finer. -/
def rank : Prec → ℕ
  | .millennium => 0
  | .century => 1
  | .decade => 2
  | .year => 3
  | .month => 4
  | .day => 5

/-- Reading a date at a given precision: the data that the precision retains.
Coarser than a year, the year is divided down (floor division, so it works for
BCE years too). -/
def key : Prec → Date → ℤ × ℕ × ℕ
  | .day, t => (t.year, t.month, t.day)
  | .month, t => (t.year, t.month, 0)
  | .year, t => (t.year, 0, 0)
  | .decade, t => (t.year / 10, 0, 0)
  | .century, t => (t.year / 10 / 10, 0, 0)
  | .millennium, t => (t.year / 10 / 10 / 10, 0, 0)

/-- The coarser of two precisions. -/
def coarser (p q : Prec) : Prec := if p.rank ≤ q.rank then p else q

theorem coarser_rank_le_left (p q : Prec) : (coarser p q).rank ≤ p.rank := by
  unfold coarser; split <;> omega

theorem coarser_rank_le_right (p q : Prec) : (coarser p q).rank ≤ q.rank := by
  unfold coarser; split <;> omega

theorem rank_inj {p q : Prec} (h : p.rank = q.rank) : p = q := by
  cases p <;> cases q <;> simp_all [rank]

theorem coarser_comm (p q : Prec) : coarser p q = coarser q p := by
  unfold coarser
  rcases lt_trichotomy p.rank q.rank with h | h | h
  · simp [h.le, Nat.not_le.2 h]
  · cases p <;> cases q <;> simp_all [rank]
  · simp [h.le, Nat.not_le.2 h]

/-- **Coarsening**: what a date looks like at precision `p` is determined by what
it looks like at any finer precision `q`.  Hence two dates agreeing at a
precision agree at every coarser one. -/
theorem key_refine {p q : Prec} (hpq : p.rank ≤ q.rank) {d e : Date}
    (h : q.key d = q.key e) : p.key d = p.key e := by
  cases p <;> cases q <;>
    simp only [key, rank, Prod.mk.injEq, and_true] at hpq h ⊢ <;> omega

end Prec

/-- Agreement of two dates as far as a precision reaches. -/
def Date.AgreeAt (p : Prec) (d e : Date) : Prop := p.key d = p.key e

namespace Date

@[refl] theorem agreeAt_refl (p : Prec) (d : Date) : d.AgreeAt p d := rfl

theorem agreeAt_symm {p : Prec} {d e : Date} (h : d.AgreeAt p e) : e.AgreeAt p d := h.symm

theorem agreeAt_trans {p : Prec} {d e f : Date} (h : d.AgreeAt p e) (h' : e.AgreeAt p f) :
    d.AgreeAt p f := h.trans h'

/-- Agreement at a precision is an equivalence relation. -/
theorem agreeAt_equivalence (p : Prec) : Equivalence (Date.AgreeAt p) :=
  ⟨agreeAt_refl p, agreeAt_symm, agreeAt_trans⟩

/-- Agreement is inherited by coarser precisions. -/
theorem agreeAt_of_rank_le {p q : Prec} (hpq : p.rank ≤ q.rank) {d e : Date}
    (h : d.AgreeAt q e) : d.AgreeAt p e := Prec.key_refine hpq h

/-- Agreement at a precision is decidable. -/
instance (p : Prec) (d e : Date) : Decidable (d.AgreeAt p e) := by
  unfold AgreeAt; infer_instance

end Date

/-- A Wikidata time value: a date, the precision it was recorded to, and the
calendar model. -/
structure TimeValue where
  /-- The date. -/
  date : Date
  /-- The precision it is recorded to. -/
  prec : Prec := .day
  /-- The calendar model. -/
  cal : Calendar := .gregorian
deriving DecidableEq, Repr, Inhabited

namespace TimeValue

variable (v w : TimeValue)

/-- The instants a time value denotes: every date agreeing with it as far as its
precision reaches. -/
def denote : Set Date := {d | d.AgreeAt v.prec v.date}

/-- The executable membership test. -/
def memB (d : Date) : Bool := decide (d.AgreeAt v.prec v.date)

@[simp] theorem memB_iff {d : Date} : v.memB d = true ↔ d ∈ v.denote := by
  simp [memB, denote, Set.mem_setOf_eq]

/-- A time value denotes its own date. -/
theorem mem_denote_self : v.date ∈ v.denote := Date.agreeAt_refl _ _

/-- The denotation is never empty. -/
theorem denote_nonempty : v.denote.Nonempty := ⟨v.date, v.mem_denote_self⟩

variable {v w}

/-- **A more precise value denotes fewer instants.** -/
theorem denote_mono {d : Date} {p q : Prec} {c : Calendar} (hpq : p.rank ≤ q.rank) :
    ({ date := d, prec := q, cal := c } : TimeValue).denote ⊆
      ({ date := d, prec := p, cal := c } : TimeValue).denote := by
  intro e he
  exact Date.agreeAt_of_rank_le hpq he

/-- Two time values are **compatible** when they are recorded in the same
calendar and agree as far as the coarser of the two precisions reaches: they can
refer to the same instant. -/
def Compatible (v w : TimeValue) : Prop :=
  v.cal = w.cal ∧ v.date.AgreeAt (Prec.coarser v.prec w.prec) w.date

instance (v w : TimeValue) : Decidable (Compatible v w) := by
  unfold Compatible; infer_instance

/-- The executable compatibility check. -/
def compatibleB (v w : TimeValue) : Bool :=
  (v.cal == w.cal) && decide (v.date.AgreeAt (Prec.coarser v.prec w.prec) w.date)

@[simp] theorem compatibleB_iff : compatibleB v w = true ↔ Compatible v w := by
  simp [compatibleB, Compatible]

/-- **Compatibility is exactly overlap of the denotations**: two time values in
the same calendar can refer to a common instant precisely when they agree at the
coarser of their precisions. -/
theorem compatible_iff_exists_mem (hcal : v.cal = w.cal) :
    Compatible v w ↔ ∃ d, d ∈ v.denote ∧ d ∈ w.denote := by
  constructor
  · rintro ⟨-, hag⟩
    rcases le_total v.prec.rank w.prec.rank with h | h
    · -- `v` is the coarser value; the date of `w` lies in both denotations
      refine ⟨w.date, ?_, w.mem_denote_self⟩
      have hc : Prec.coarser v.prec w.prec = v.prec := by simp [Prec.coarser, h]
      rw [hc] at hag
      exact Date.agreeAt_symm hag
    · refine ⟨v.date, v.mem_denote_self, ?_⟩
      have hc : Prec.coarser v.prec w.prec = w.prec := by
        unfold Prec.coarser
        by_cases hle : v.prec.rank ≤ w.prec.rank
        · rw [if_pos hle]
          exact Prec.rank_inj (le_antisymm hle h)
        · rw [if_neg hle]
      rw [hc] at hag
      exact hag
  · rintro ⟨d, hv, hw⟩
    refine ⟨hcal, ?_⟩
    have h1 : v.date.AgreeAt (Prec.coarser v.prec w.prec) d :=
      Date.agreeAt_symm (Date.agreeAt_of_rank_le (Prec.coarser_rank_le_left _ _) hv)
    have h2 : d.AgreeAt (Prec.coarser v.prec w.prec) w.date :=
      Date.agreeAt_of_rank_le (Prec.coarser_rank_le_right _ _) hw
    exact Date.agreeAt_trans h1 h2

@[refl] theorem compatible_refl (v : TimeValue) : Compatible v v :=
  ⟨rfl, Date.agreeAt_refl _ _⟩

theorem compatible_symm (h : Compatible v w) : Compatible w v := by
  obtain ⟨hc, hag⟩ := h
  refine ⟨hc.symm, ?_⟩
  rw [Prec.coarser_comm]
  exact Date.agreeAt_symm hag

/-- Time values in different calendars are never compatible. -/
theorem not_compatible_of_cal_ne (h : v.cal ≠ w.cal) : ¬ Compatible v w := fun hc => h hc.1

/-- Coarsening a time value: the same date read to a coarser precision. -/
def coarsen (v : TimeValue) (p : Prec) : TimeValue :=
  { date := v.date, prec := Prec.coarser p v.prec, cal := v.cal }

/-- Coarsening only ever adds instants. -/
theorem denote_subset_coarsen (v : TimeValue) (p : Prec) : v.denote ⊆ (v.coarsen p).denote := by
  intro d hd
  exact Date.agreeAt_of_rank_le (Prec.coarser_rank_le_right p v.prec) hd

/-- A value is always compatible with any coarsening of itself. -/
theorem compatible_coarsen (v : TimeValue) (p : Prec) : Compatible v (v.coarsen p) := by
  refine ⟨rfl, ?_⟩
  exact Date.agreeAt_refl _ _

end TimeValue

/-! ## Worked examples -/

namespace TimeExample

open Wikidata

/-- 1 May 1990, to the day. -/
def may1990 : TimeValue := { date := ⟨1990, 5, 1⟩, prec := .day }

/-- 1 July 1990, to the day. -/
def jul1990 : TimeValue := { date := ⟨1990, 7, 1⟩, prec := .day }

/-- The year 1990. -/
def y1990 : TimeValue := { date := { year := 1990 }, prec := .year }

/-- The 20th century, i.e. the years 1900–1999 as Wikidata records them. -/
def c20 : TimeValue := { date := { year := 1990 }, prec := .century }

/-- The same year, but recorded in the Julian calendar. -/
def y1990julian : TimeValue := { date := { year := 1990 }, prec := .year, cal := .julian }

theorem may_compat_year : TimeValue.Compatible may1990 y1990 := by decide

theorem jul_compat_year : TimeValue.Compatible jul1990 y1990 := by decide

theorem may_not_compat_jul : ¬ TimeValue.Compatible may1990 jul1990 := by decide

/-- **Compatibility is not transitive**: `1 May 1990` and `1 July 1990` are both
compatible with `1990`, but not with each other. -/
theorem compatible_not_transitive :
    ¬ ∀ u v w : TimeValue, TimeValue.Compatible u v → TimeValue.Compatible v w →
      TimeValue.Compatible u w := by
  intro h
  exact may_not_compat_jul
    (h may1990 y1990 jul1990 may_compat_year (TimeValue.compatible_symm jul_compat_year))

/-- A date of 1990 is an instant of the 20th century. -/
theorem may_mem_c20 : c20.memB ⟨1990, 5, 1⟩ = true := by decide

/-- A date of 2005 is not. -/
theorem y2005_not_mem_c20 : c20.memB ⟨2005, 1, 1⟩ = false := by decide

/-- Years before the common era are handled by floor division: the year −5 lies
in the same decade as the year −1, ... -/
theorem bce_same_decade :
    (Date.AgreeAt .decade { year := -5 } { year := -1 }) := by decide

/-- ... but not in the same decade as the year −11. -/
theorem bce_other_decade :
    ¬ (Date.AgreeAt .decade { year := -5 } { year := -11 }) := by decide

/-- The same year in two different calendar models is not compatible. -/
theorem calendars_incompatible : ¬ TimeValue.Compatible y1990 y1990julian :=
  TimeValue.not_compatible_of_cal_ne (by decide)

/-- The denotation of a year is contained in the denotation of its century. -/
theorem year_denote_subset_century :
    ({ date := { year := 1990 }, prec := .year } : TimeValue).denote ⊆
      ({ date := { year := 1990 }, prec := .century } : TimeValue).denote :=
  TimeValue.denote_mono (by decide)

end TimeExample

end Wikidata
