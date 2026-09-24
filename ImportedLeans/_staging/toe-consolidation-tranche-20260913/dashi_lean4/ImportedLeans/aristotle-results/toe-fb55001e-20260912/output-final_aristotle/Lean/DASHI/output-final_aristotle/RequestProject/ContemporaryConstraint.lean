import RequestProject.RangeConstraints

/-!
# The contemporary constraint

Wikidata's **contemporary constraint** (Q25796498) says that a statement of the
property may only relate two items whose existences overlap in time: a person can
only be the `spouse` (P26) of somebody alive at the same time, an organisation can
only be a `member of` something that existed while it did.  The existence of an
item is read off its start and end dates -- `date of birth` (P569) or `inception`
(P571) on one side, `date of death` (P570) or `dissolved, abolished or demolished`
(P576) on the other -- and a missing date leaves that side of the interval
unbounded.

This file formalises the constraint on top of the claim model of
`RequestProject.Ranks`, reusing the endpoints `Wikidata.Bound` of
`RequestProject.RangeConstraints`.

* `Wikidata.Interval` is an interval of years with possibly unbounded ends, with
  membership `Interval.Mem`, intersection `Interval.inter` (characterised by
  `Interval.mem_inter`), inclusion `Interval.Subset`, and the executable
  nonemptiness test `Interval.okB`, proved correct by `Interval.okB_iff`.
* `Wikidata.Overlaps` is the relation "these two existences meet", with the
  executable test `Wikidata.overlapsB` (`overlapsB_iff`).  Proved: overlapping is
  symmetric (`overlaps_symm`) and reflexive on nonempty intervals
  (`overlaps_refl`); it is monotone under widening (`overlaps_mono`), so an item
  with unknown dates overlaps every nonempty existence
  (`overlaps_of_unbounded`); disjoint intervals do not overlap
  (`not_overlaps_of_lt`); and it is **not transitive** — `not_overlaps_trans`
  exhibits three existences with the first meeting the second and the second the
  third, but not the first the third, so contemporariness cannot be propagated
  along chains.
* `Wikidata.ContemporarySpec` is the constraint of one property, with the start and
  end properties it reads dates from; `ContemporarySpec.existence` computes the
  existence interval of an item and `ContemporarySpec.setOk` checks a claim set,
  characterised exactly by `setOk_iff`.  Only item-valued statements of the
  constrained property are checked (`setOk_of_pid_ne`), and from conformance one
  gets, for two items with fully known dates, that neither died before the other
  was born (`no_gap_of_setOk`).

The worked fragment has three stylised people -- one 1900-1970, one 1930-2010 and
one 1990- -- with `spouse` (P26) statements.  The overlapping marriage is
accepted, the one spanning the gap is rejected, a person with no recorded dates
may be married to anybody, and the three existences witness the failure of
transitivity.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

/-! ### Intervals of years -/

/-- An interval of years, either end of which may be unbounded. -/
structure Interval where
  /-- The start of the interval. -/
  lower : Bound := .unbounded
  /-- The end of the interval. -/
  upper : Bound := .unbounded
deriving DecidableEq, Repr, Inhabited

namespace Interval

variable (I J : Interval)

/-- The years inside the interval. -/
def Mem (x : Int) : Prop := I.lower.LowerOk x ∧ I.upper.UpperOk x

instance (x : Int) : Decidable (I.Mem x) := by unfold Mem; infer_instance

/-- The whole line: the existence of an item with no recorded dates. -/
def univ : Interval := {}

@[simp] theorem mem_univ (x : Int) : univ.Mem x := ⟨trivial, trivial⟩

/-- The intersection of two intervals. -/
def inter : Interval := ⟨I.lower.maxLower J.lower, I.upper.minUpper J.upper⟩

theorem mem_inter (x : Int) : (I.inter J).Mem x ↔ I.Mem x ∧ J.Mem x := by
  simp only [Mem, inter, Bound.maxLower_ok, Bound.minUpper_ok]
  tauto

/-- One interval is contained in another. -/
def Subset : Prop := ∀ x, I.Mem x → J.Mem x

/-- The executable nonemptiness test. -/
def okB : Bool :=
  match I.lower, I.upper with
  | .finite a, .finite b => decide (a ≤ b)
  | _, _ => true

/-- The nonemptiness test is correct. -/
theorem okB_iff : I.okB = true ↔ ∃ x, I.Mem x := by
  constructor
  · intro h
    cases hl : I.lower with
    | unbounded =>
        cases hu : I.upper with
        | unbounded => exact ⟨0, by simp [Mem, hl, hu, Bound.LowerOk, Bound.UpperOk]⟩
        | finite b => exact ⟨b, by simp [Mem, hl, hu, Bound.LowerOk, Bound.UpperOk]⟩
    | finite a =>
        cases hu : I.upper with
        | unbounded => exact ⟨a, by simp [Mem, hl, hu, Bound.LowerOk, Bound.UpperOk]⟩
        | finite b =>
            have hab : a ≤ b := by
              simp only [okB, hl, hu, decide_eq_true_eq] at h
              exact h
            exact ⟨a, by simp [Mem, hl, hu, Bound.LowerOk, Bound.UpperOk, hab]⟩
  · rintro ⟨x, hx1, hx2⟩
    cases hl : I.lower with
    | unbounded => simp [okB, hl]
    | finite a =>
        cases hu : I.upper with
        | unbounded => simp [okB, hl, hu]
        | finite b =>
            rw [hl] at hx1
            rw [hu] at hx2
            simp only [Bound.lowerOk_finite] at hx1
            simp only [Bound.upperOk_finite] at hx2
            simp only [okB, hl, hu, decide_eq_true_eq]
            omega

end Interval

/-- Two existences are contemporary when they share a year. -/
def Overlaps (I J : Interval) : Prop := ∃ x, I.Mem x ∧ J.Mem x

/-- The executable contemporariness test. -/
def overlapsB (I J : Interval) : Bool := (I.inter J).okB

theorem overlapsB_iff (I J : Interval) : overlapsB I J = true ↔ Overlaps I J := by
  rw [overlapsB, Interval.okB_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Interval.mem_inter I J x).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (Interval.mem_inter I J x).2 hx⟩

instance (I J : Interval) : Decidable (Overlaps I J) :=
  decidable_of_iff _ (overlapsB_iff I J)

/-- Contemporariness is symmetric. -/
theorem overlaps_symm {I J : Interval} (h : Overlaps I J) : Overlaps J I := by
  obtain ⟨x, hI, hJ⟩ := h
  exact ⟨x, hJ, hI⟩

/-- A nonempty existence is contemporary with itself. -/
theorem overlaps_refl {I : Interval} (h : ∃ x, I.Mem x) : Overlaps I I := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, hx⟩

/-- Widening the existences preserves contemporariness. -/
theorem overlaps_mono {I J I' J' : Interval} (h : Overlaps I J)
    (hI : I.Subset I') (hJ : J.Subset J') : Overlaps I' J' := by
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hI x hx, hJ x hy⟩

/-- An item with no recorded dates is contemporary with every nonempty existence. -/
theorem overlaps_of_unbounded {J : Interval} (h : ∃ x, J.Mem x) : Overlaps Interval.univ J := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Interval.mem_univ x, hx⟩

/-- Existences separated in time are not contemporary. -/
theorem not_overlaps_of_lt {I J : Interval} {a b : Int} (hI : I.upper = .finite a)
    (hJ : J.lower = .finite b) (hab : a < b) : ¬ Overlaps I J := by
  rintro ⟨x, ⟨-, hx2⟩, ⟨hy1, -⟩⟩
  rw [hI] at hx2
  rw [hJ] at hy1
  simp only [Bound.upperOk_finite] at hx2
  simp only [Bound.lowerOk_finite] at hy1
  omega

/-- Contemporariness is **not** transitive: it cannot be propagated along chains of
statements. -/
theorem not_overlaps_trans :
    ∃ I J K : Interval, Overlaps I J ∧ Overlaps J K ∧ ¬ Overlaps I K := by
  refine ⟨⟨.finite 1900, .finite 1970⟩, ⟨.finite 1930, .finite 2010⟩,
    ⟨.finite 1990, .unbounded⟩, ?_, ?_, ?_⟩
  · exact ⟨1950, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨2000, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, trivial⟩⟩
  · exact not_overlaps_of_lt rfl rfl (by norm_num)

/-! ### The constraint -/

/-- A **contemporary constraint** (Q25796498) on one property, together with the
properties its existence dates are read from. -/
structure ContemporarySpec where
  /-- The constrained property, e.g. `spouse` (P26). -/
  pid : Pid
  /-- The properties giving the start of an existence, e.g. `date of birth` (P569)
  and `inception` (P571). -/
  starts : List Pid := []
  /-- The properties giving the end of an existence, e.g. `date of death` (P570)
  and `dissolved, abolished or demolished` (P576). -/
  ends : List Pid := []
deriving DecidableEq, Repr, Inhabited

namespace ContemporarySpec

variable (spec : ContemporarySpec)

/-- The first numeric value of one of the given properties recorded for an item. -/
def firstDate (cs : Claim.Set) (q : Qid) (ps : List Pid) : Option Int :=
  cs.findSome? fun c =>
    if c.subject = q ∧ c.pid ∈ ps then c.value.numeric? else none

/-- An optional date as an endpoint: a missing date leaves the side unbounded. -/
def boundOf : Option Int → Bound
  | none => .unbounded
  | some x => .finite x

/-- The existence interval of an item, read off its start and end dates. -/
def existence (cs : Claim.Set) (q : Qid) : Interval :=
  { lower := boundOf (firstDate cs q spec.starts)
    upper := boundOf (firstDate cs q spec.ends) }

/-- An item with none of the dates recorded has the whole line as its existence. -/
theorem existence_eq_univ {cs : Claim.Set} {q : Qid}
    (h1 : firstDate cs q spec.starts = none) (h2 : firstDate cs q spec.ends = none) :
    spec.existence cs q = Interval.univ := by
  simp [existence, h1, h2, boundOf, Interval.univ]

/-- The check of a single claim. -/
def claimOk (cs : Claim.Set) (c : Claim) : Bool :=
  if c.pid = spec.pid then
    match c.value with
    | .item o => overlapsB (spec.existence cs c.subject) (spec.existence cs o)
    | _ => true
  else true

/-- The check of a whole claim set. -/
def setOk (cs : Claim.Set) : Bool := cs.all fun c => spec.claimOk cs c

theorem setOk_iff (cs : Claim.Set) :
    spec.setOk cs = true ↔
      ∀ c ∈ cs, ∀ o : Qid, c.pid = spec.pid → c.value = .item o →
        Overlaps (spec.existence cs c.subject) (spec.existence cs o) := by
  simp only [setOk, List.all_eq_true]
  constructor
  · intro h c hc o hp hv
    have := h c hc
    rw [claimOk, if_pos hp, hv] at this
    exact (overlapsB_iff _ _).1 this
  · intro h c hc
    unfold claimOk
    by_cases hp : c.pid = spec.pid
    · rw [if_pos hp]
      cases hv : c.value with
      | item o => exact (overlapsB_iff _ _).2 (h c hc o hp hv)
      | _ => rfl
    · rw [if_neg hp]

/-- A claim about another property is unconstrained. -/
theorem claimOk_of_pid_ne {cs : Claim.Set} {c : Claim} (h : c.pid ≠ spec.pid) :
    spec.claimOk cs c = true := by
  simp [claimOk, h]

/-- In a conforming base, related items with fully known dates cannot be separated:
neither can have ended before the other began. -/
theorem no_gap_of_setOk {cs : Claim.Set} (h : spec.setOk cs = true) {c : Claim} (hc : c ∈ cs)
    {o : Qid} (hp : c.pid = spec.pid) (hv : c.value = .item o) {a b : Int}
    (ha : (spec.existence cs c.subject).upper = .finite a)
    (hb : (spec.existence cs o).lower = .finite b) : b ≤ a := by
  have hov := (spec.setOk_iff cs).1 h c hc o hp hv
  by_contra hlt
  exact not_overlaps_of_lt ha hb (by omega) hov

end ContemporarySpec

/-! ### A worked fragment -/

namespace ContemporaryExample

open RankExample (Q P)

/-- `spouse` (P26) is contemporary; existences run from `date of birth` (P569) or
`inception` (P571) to `date of death` (P570) or `dissolved` (P576). -/
def spouseSpec : ContemporarySpec :=
  { pid := P "P26", starts := [P "P569", P "P571"], ends := [P "P570", P "P576"] }

/-- Three stylised people: `Q1` lived 1900-1970, `Q2` 1930-2010, `Q3` was born in
1990, and `Q4` has no recorded dates. -/
def dates : Claim.Set :=
  [ { subject := Q "Q1", pid := P "P569", value := .time 1900 },
    { subject := Q "Q1", pid := P "P570", value := .time 1970 },
    { subject := Q "Q2", pid := P "P569", value := .time 1930 },
    { subject := Q "Q2", pid := P "P570", value := .time 2010 },
    { subject := Q "Q3", pid := P "P569", value := .time 1990 } ]

/-- A marriage between two people whose lives overlap is accepted. -/
theorem overlapping_marriage_ok :
    spouseSpec.setOk (dates ++ [{ subject := Q "Q1", pid := P "P26", value := .item (Q "Q2") }]) =
      true := by decide

/-- A marriage between people separated in time is rejected. -/
theorem separated_marriage_rejected :
    spouseSpec.setOk (dates ++ [{ subject := Q "Q1", pid := P "P26", value := .item (Q "Q3") }]) =
      false := by decide

/-- A person with no recorded dates may be married to anybody. -/
theorem unknown_dates_ok :
    spouseSpec.setOk (dates ++ [{ subject := Q "Q4", pid := P "P26", value := .item (Q "Q1") }]) =
      true := by decide

/-- The constraint only looks at the property it constrains. -/
theorem other_property_unconstrained :
    spouseSpec.setOk (dates ++ [{ subject := Q "Q1", pid := P "P1038", value := .item (Q "Q3") }]) =
      true := by decide

/-- The three existences of the fragment witness the failure of transitivity: `Q1`
is contemporary with `Q2` and `Q2` with `Q3`, but `Q1` is not with `Q3`. -/
theorem fragment_not_transitive :
    overlapsB (spouseSpec.existence dates (Q "Q1")) (spouseSpec.existence dates (Q "Q2")) = true ∧
    overlapsB (spouseSpec.existence dates (Q "Q2")) (spouseSpec.existence dates (Q "Q3")) = true ∧
    overlapsB (spouseSpec.existence dates (Q "Q1")) (spouseSpec.existence dates (Q "Q3")) =
      false := by decide

end ContemporaryExample

end Wikidata
