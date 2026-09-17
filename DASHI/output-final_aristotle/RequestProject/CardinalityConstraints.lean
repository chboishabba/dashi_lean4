/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Ranks

/-!
# Cardinality constraints on the truthy values of a property

How many values a property may have for one item is governed by a family of
Wikidata constraints:

* **single-value** (Q19474404) — at most one value per item, e.g. `capital` (P36);
* **multi-value** (Q21510857) — at least two values per item, e.g. `child` (P40)
  on an item claiming to have several;
* and the intermediate cases, a minimum and a maximum number of values.

The count that matters is the number of *distinct truthy values*: a deprecated
statement does not count, and neither does a value hidden behind a preferred one,
so a property can carry several statements and still be single-valued.  This file
formalises that reading on top of the claim model of `RequestProject.Ranks`.

* `Wikidata.CardSpec` is the cardinality constraint of one property — a minimum and
  an optional maximum — `Wikidata.distinctTruthyValues` is the count it applies to,
  and `CardSpec.setOk` the executable check on a claim set, characterised exactly
  by `setOk_iff` and by the per-subject `subjectOk_iff`.
* Proved: an unconstrained specification accepts everything
  (`setOk_of_trivial`); widening the bounds preserves conformance
  (`subjectOk_mono`); a subject with no statement of the property is unconstrained
  (`subjectOk_of_no_claim`).
* The constraints have the expected consequences.  Under a maximum of one, any two
  truthy statements of the property on the same item carry the same value
  (`eq_of_single_value`) — so the property really is a partial function.  Under a
  minimum of two, an item with a statement has two *different* truthy values
  (`two_values_of_multi_value`).  Consequently a property declared both
  single-valued and multi-valued has no statements at all
  (`no_claim_of_conflict`).
* Ranks interact with the count exactly as they should: several statements of a
  single-valued property are fine as long as ranks single one of them out, which
  the worked fragment exhibits, while two competing normal statements are
  rejected.

The worked fragment gives `capital` (P36) a maximum of one value and `child`
(P40) a minimum of two.  A country with one capital passes; a country with two
different capitals at the same rank is rejected but the same base with one of them
deprecated passes; an item with two children passes, one with a single child is
rejected.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

/-! ### Two small facts about lists -/

/-- A list with at most one element has all its members equal. -/
theorem eq_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h with
  | [], _ => exact absurd ha (by simp)
  | [x], _ =>
      simp only [List.mem_singleton] at ha hb
      exact ha.trans hb.symm

/-- A list whose deduplication has at least two elements has two different members. -/
theorem exists_ne_of_two_le_dedup_length {α : Type*} [DecidableEq α] {l : List α}
    (h : 2 ≤ l.dedup.length) : ∃ a ∈ l, ∃ b ∈ l, a ≠ b := by
  match hd : l.dedup with
  | [] => rw [hd] at h; simp at h
  | [_] => rw [hd] at h; simp at h
  | a :: b :: t =>
      have hnd : (a :: b :: t).Nodup := hd ▸ l.nodup_dedup
      have hab : a ≠ b := by
        intro hab
        exact (List.nodup_cons.1 hnd).1 (by simp [hab])
      have hal : a ∈ l := by
        have : a ∈ l.dedup := by rw [hd]; simp
        exact (List.mem_dedup).1 this
      have hbl : b ∈ l := by
        have : b ∈ l.dedup := by rw [hd]; simp
        exact (List.mem_dedup).1 this
      exact ⟨a, hal, b, hbl, hab⟩

/-! ### The constraint -/

/-- The distinct values a default query returns for an item and a property. -/
def distinctTruthyValues (cs : Claim.Set) (q : Qid) (p : Pid) : List Value :=
  (Claim.truthyValues cs q p).dedup

theorem mem_distinctTruthyValues_iff {cs : Claim.Set} {q : Qid} {p : Pid} {v : Value} :
    v ∈ distinctTruthyValues cs q p ↔ v ∈ Claim.truthyValues cs q p :=
  List.mem_dedup

/-- A **cardinality constraint** on one property: how many distinct truthy values an
item may have.  `upper = none` is the absence of a maximum. -/
structure CardSpec where
  /-- The constrained property. -/
  pid : Pid
  /-- The minimum number of distinct values (`2` is the multi-value constraint). -/
  lower : Nat := 0
  /-- The maximum number of distinct values (`some 1` is the single-value
  constraint). -/
  upper : Option Nat := none
deriving DecidableEq, Repr, Inhabited

namespace CardSpec

variable (spec : CardSpec) (cs : Claim.Set)

/-- The items carrying a statement of the constrained property. -/
def subjects : List Qid := (cs.filter fun c => c.pid = spec.pid).map (·.subject)

theorem mem_subjects_iff {q : Qid} :
    q ∈ spec.subjects cs ↔ ∃ c ∈ cs, c.pid = spec.pid ∧ c.subject = q := by
  simp only [subjects, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, ⟨hc, hp⟩, rfl⟩; exact ⟨c, hc, hp, rfl⟩
  · rintro ⟨c, hc, hp, rfl⟩; exact ⟨c, ⟨hc, hp⟩, rfl⟩

/-- The check for one item. -/
def subjectOk (q : Qid) : Bool :=
  let n := (distinctTruthyValues cs q spec.pid).length
  decide (spec.lower ≤ n) &&
    (match spec.upper with
     | none => true
     | some m => decide (n ≤ m))

theorem subjectOk_iff (q : Qid) :
    spec.subjectOk cs q = true ↔
      spec.lower ≤ (distinctTruthyValues cs q spec.pid).length ∧
        ∀ m, spec.upper = some m → (distinctTruthyValues cs q spec.pid).length ≤ m := by
  unfold subjectOk
  cases hu : spec.upper with
  | none => simp
  | some m => simp

/-- The check for a whole claim set: every item carrying the property is checked. -/
def setOk : Bool := (spec.subjects cs).all (spec.subjectOk cs)

theorem setOk_iff :
    spec.setOk cs = true ↔
      ∀ q, (∃ c ∈ cs, c.pid = spec.pid ∧ c.subject = q) → spec.subjectOk cs q = true := by
  simp only [setOk, List.all_eq_true]
  constructor
  · intro h q hq
    exact h q ((spec.mem_subjects_iff cs).2 hq)
  · intro h q hq
    exact h q ((spec.mem_subjects_iff cs).1 hq)

/-- An item with no statement of the property is unconstrained as soon as the
constraint asks for no values at all. -/
theorem subjectOk_of_no_claim {q : Qid} (hlow : spec.lower = 0)
    (h : distinctTruthyValues cs q spec.pid = []) : spec.subjectOk cs q = true := by
  rw [subjectOk_iff, h, hlow]
  refine ⟨Nat.zero_le _, ?_⟩
  intro m _
  simp

/-- A constraint with no minimum and no maximum accepts every base. -/
theorem setOk_of_trivial (hlow : spec.lower = 0) (hup : spec.upper = none) :
    spec.setOk cs = true := by
  rw [setOk_iff]
  intro q _
  rw [subjectOk_iff, hlow, hup]
  exact ⟨Nat.zero_le _, by simp⟩

/-- Widening the bounds preserves conformance. -/
theorem subjectOk_mono {spec' : CardSpec} (hp : spec'.pid = spec.pid)
    (hlow : spec'.lower ≤ spec.lower)
    (hup : ∀ m', spec'.upper = some m' → ∃ m, spec.upper = some m ∧ m ≤ m')
    {q : Qid} (h : spec.subjectOk cs q = true) : spec'.subjectOk cs q = true := by
  rw [subjectOk_iff] at h ⊢
  rw [hp]
  refine ⟨le_trans hlow h.1, ?_⟩
  intro m' hm'
  obtain ⟨m, hm, hmm⟩ := hup m' hm'
  exact le_trans (h.2 m hm) hmm

/-- **Single value**: under a maximum of one, two truthy statements of the property
on the same item carry the same value. -/
theorem eq_of_single_value (h : spec.setOk cs = true) (hup : spec.upper = some 1)
    {q : Qid} {c d : Claim} (hc : c ∈ cs) (hd : d ∈ cs)
    (hcp : c.pid = spec.pid) (hdp : d.pid = spec.pid) (hcq : c.subject = q) (hdq : d.subject = q)
    (hct : Claim.isTruthy cs c) (hdt : Claim.isTruthy cs d) : c.value = d.value := by
  have hok := (spec.setOk_iff cs).1 h q ⟨c, hc, hcp, hcq⟩
  have hlen := ((spec.subjectOk_iff cs q).1 hok).2 1 hup
  have hcv : c.value ∈ distinctTruthyValues cs q spec.pid :=
    mem_distinctTruthyValues_iff.2 (Claim.mem_truthyValues_iff.2 ⟨c, hc, hcq, hcp, hct, rfl⟩)
  have hdv : d.value ∈ distinctTruthyValues cs q spec.pid :=
    mem_distinctTruthyValues_iff.2 (Claim.mem_truthyValues_iff.2 ⟨d, hd, hdq, hdp, hdt, rfl⟩)
  exact eq_of_length_le_one hlen hcv hdv

/-- **Multi value**: under a minimum of two, an item carrying the property has two
different truthy values. -/
theorem two_values_of_multi_value (h : spec.setOk cs = true) (hlow : 2 ≤ spec.lower)
    {q : Qid} {c : Claim} (hc : c ∈ cs) (hcp : c.pid = spec.pid) (hcq : c.subject = q) :
    ∃ v ∈ Claim.truthyValues cs q spec.pid, ∃ w ∈ Claim.truthyValues cs q spec.pid, v ≠ w := by
  have hok := (spec.setOk_iff cs).1 h q ⟨c, hc, hcp, hcq⟩
  have hlen := ((spec.subjectOk_iff cs q).1 hok).1
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    exists_ne_of_two_le_dedup_length (l := Claim.truthyValues cs q spec.pid)
      (le_trans hlow hlen)
  exact ⟨v, hv, w, hw, hvw⟩

/-- A property declared both single-valued and multi-valued has no statements at
all: the two constraints are inconsistent. -/
theorem no_claim_of_conflict {single multi : CardSpec} (hpid : single.pid = multi.pid)
    (hs : single.setOk cs = true) (hm : multi.setOk cs = true)
    (hup : single.upper = some 1) (hlow : 2 ≤ multi.lower) :
    ∀ c ∈ cs, c.pid ≠ single.pid := by
  intro c hc hcp
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    two_values_of_multi_value multi cs hm hlow hc (by rw [hcp, hpid]) rfl
  obtain ⟨d, hd, hdq, hdp, hdt, rfl⟩ := Claim.mem_truthyValues_iff.1 hv
  obtain ⟨e, he, heq, hep, het, rfl⟩ := Claim.mem_truthyValues_iff.1 hw
  exact hvw (eq_of_single_value single cs hs hup hd he (by rw [hdp, ← hpid])
    (by rw [hep, ← hpid]) hdq heq hdt het)

end CardSpec

/-! ### A worked fragment -/

namespace CardExample

open RankExample (Q P)

/-- `capital` (P36) has at most one value. -/
def capitalSpec : CardSpec := { pid := P "P36", upper := some 1 }

/-- `child` (P40) is used here with a multi-value constraint: at least two values. -/
def childSpec : CardSpec := { pid := P "P40", lower := 2 }

/-- One country, one capital. -/
def oneCapital : Claim.Set :=
  [{ subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") }]

theorem oneCapital_ok : capitalSpec.setOk oneCapital = true := by decide

/-- Two competing capitals at the same rank are rejected. -/
def twoCapitals : Claim.Set :=
  [ { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") },
    { subject := Q "Q183", pid := P "P36", value := .item (Q "Q365") } ]

theorem twoCapitals_rejected : capitalSpec.setOk twoCapitals = false := by decide

/-- The same two statements, with the historical one deprecated, pass: ranks single
out one truthy value, so the property is single-valued after all. -/
def twoCapitalsRanked : Claim.Set :=
  [ { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") },
    { subject := Q "Q183", pid := P "P36", value := .item (Q "Q365"), rank := .deprecated } ]

theorem twoCapitalsRanked_ok : capitalSpec.setOk twoCapitalsRanked = true := by decide

/-- A preferred statement likewise hides the other value. -/
def twoCapitalsPreferred : Claim.Set :=
  [ { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64"), rank := .preferred },
    { subject := Q "Q183", pid := P "P36", value := .item (Q "Q365") } ]

theorem twoCapitalsPreferred_ok : capitalSpec.setOk twoCapitalsPreferred = true := by decide

/-- Repeating the *same* value twice is not two values. -/
theorem repeated_value_ok :
    capitalSpec.setOk
      [ { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") },
        { subject := Q "Q183", pid := P "P36", value := .item (Q "Q64") } ] = true := by decide

/-- Two children satisfy the multi-value constraint. -/
theorem twoChildren_ok :
    childSpec.setOk
      [ { subject := Q "Q42", pid := P "P40", value := .item (Q "Q1") },
        { subject := Q "Q42", pid := P "P40", value := .item (Q "Q2") } ] = true := by decide

/-- A single child does not. -/
theorem oneChild_rejected :
    childSpec.setOk [{ subject := Q "Q42", pid := P "P40", value := .item (Q "Q1") }] = false := by
  decide

/-- An item with no statement of the property is not checked. -/
theorem unrelated_item_ok :
    childSpec.setOk [{ subject := Q "Q42", pid := P "P26", value := .item (Q "Q1") }] = true := by
  decide

end CardExample

end Wikidata
