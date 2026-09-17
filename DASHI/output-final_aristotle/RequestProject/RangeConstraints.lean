/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Ranks

/-!
# Range constraints and the difference-within-range constraint

Two of Wikidata's property constraints bound the *numeric* content of a
statement rather than its ontological type:

* **range constraint** (Q21510860) — the value of the property must lie between a
  minimum (P2313) and a maximum (P2312) value; either endpoint may be absent, in
  which case that side is unbounded (the "no-bounds" situation);
* **difference within range constraint** (Q21510854) — the value of the property
  must differ from the value of another property of the same item by an amount
  lying in a given interval; the textbook instance is that `date of death` (P570)
  must be after `date of birth` (P569) and by at most a human lifespan.

Both are formalised here on top of the claim model of `RequestProject.Ranks`,
whose `Value` carries integer quantities and years, so that a single integer
reading `Value.numeric?` covers the quantity and the time case at once.  A value
that is not numeric (an item or a string) is outside the scope of a range
constraint and is left unconstrained.

* `Wikidata.Bound` is an endpoint, either `unbounded` or `finite n`, and
  `Wikidata.RangeSpec` is the range constraint of one property.  `RangeSpec.Admits`
  is its meaning on integers and `RangeSpec.admitsB`, `RangeSpec.valueOk`,
  `RangeSpec.claimOk`, `Wikidata.rangeOk` the executable checks, each characterised
  exactly (`admitsB_iff`, `valueOk_iff`, `claimOk_iff`, `rangeOk_iff`).
* The intervals form a meet-semilattice: `RangeSpec.inter` admits exactly the
  integers admitted by both (`inter_admits`), so a conjunction of range constraints
  is again one, and it is the greatest such (`inter_greatest`); widening the
  interval weakens the constraint (`admits_mono`), and the doubly unbounded
  constraint admits everything (`admits_unbounded`).
* A constraint whose maximum lies below its minimum forbids the property numeric
  values outright (`no_numeric_of_empty_range`); a property that appears in no
  constraint of the table is unconstrained (`claimOk_of_pid_ne`,
  `rangeOk_of_no_spec`).
* Conformance is downward closed along sublists (`rangeOk_sublist`), hence holds
  of the truthy fragment of a conforming base (`rangeOk_truthy`), splits over
  concatenation (`rangeOk_append`), and is monotone in the table of constraints
  (`rangeOk_sublist_specs`).  From conformance the bounds can be read back off any
  statement (`lower_le_of_rangeOk`, `le_upper_of_rangeOk`).
* `Wikidata.DiffSpec` is a difference-within-range constraint, with the executable
  check `DiffSpec.setOk` characterised by `setOk_iff`.  A constraint with a
  non-negative minimum orders the two properties (`base_le_of_setOk`); differences
  compose, so chaining two such constraints gives a third with the added bounds
  (`Bound.addLower`, `Bound.addUpper`, `DiffSpec.admits_trans`); reversing the two properties
  negates the interval (`DiffSpec.admits_swap`); and conformance is again downward
  closed (`DiffSpec.setOk_sublist`, `DiffSpec.setOk_truthy`).
* The two layers propagate into each other: a range on the property a difference
  constraint compares with bounds the constrained property too
  (`lower_le_of_diff`, `le_upper_of_diff`) -- a range for `date of birth` and a
  bound on the lifespan give a range for `date of death`.

The worked fragment gives `population` (P1082) a non-negative range, `date of
birth` (P569) a plausible range of years, and constrains `date of death` (P570)
to lie between 0 and 150 years after the birth.  Berlin's population statements
from `RequestProject.Ranks` pass; a negative population, a birth year in the far
future and a death preceding the birth are each rejected, and a base whose only
offence is on a deprecated statement is rejected while its truthy fragment passes.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

/-! ### Endpoints -/

/-- An endpoint of a range constraint: either absent (the corresponding side of the
range is unbounded) or a concrete integer. -/
inductive Bound where
  /-- No bound on this side. -/
  | unbounded
  /-- The bound is the integer `n`. -/
  | finite (n : Int)
deriving DecidableEq, Repr, Inhabited

namespace Bound

/-- `b` as a *lower* endpoint: the integers it allows. -/
def LowerOk : Bound → Int → Prop
  | unbounded, _ => True
  | finite n, x => n ≤ x

/-- `b` as an *upper* endpoint: the integers it allows. -/
def UpperOk : Bound → Int → Prop
  | unbounded, _ => True
  | finite n, x => x ≤ n

instance : ∀ (b : Bound) (x : Int), Decidable (b.LowerOk x)
  | unbounded, _ => isTrue trivial
  | finite n, x => inferInstanceAs (Decidable (n ≤ x))

instance : ∀ (b : Bound) (x : Int), Decidable (b.UpperOk x)
  | unbounded, _ => isTrue trivial
  | finite n, x => inferInstanceAs (Decidable (x ≤ n))

@[simp] theorem lowerOk_unbounded (x : Int) : LowerOk .unbounded x := trivial

@[simp] theorem upperOk_unbounded (x : Int) : UpperOk .unbounded x := trivial

@[simp] theorem lowerOk_finite (n x : Int) : LowerOk (.finite n) x ↔ n ≤ x := Iff.rfl

@[simp] theorem upperOk_finite (n x : Int) : UpperOk (.finite n) x ↔ x ≤ n := Iff.rfl

/-- The larger of two lower endpoints: the lower endpoint of the intersection. -/
def maxLower : Bound → Bound → Bound
  | unbounded, c => c
  | b, unbounded => b
  | finite m, finite n => finite (max m n)

/-- The smaller of two upper endpoints: the upper endpoint of the intersection. -/
def minUpper : Bound → Bound → Bound
  | unbounded, c => c
  | b, unbounded => b
  | finite m, finite n => finite (min m n)

theorem maxLower_ok (b c : Bound) (x : Int) :
    (b.maxLower c).LowerOk x ↔ b.LowerOk x ∧ c.LowerOk x := by
  cases b <;> cases c <;> simp [maxLower, LowerOk]

theorem minUpper_ok (b c : Bound) (x : Int) :
    (b.minUpper c).UpperOk x ↔ b.UpperOk x ∧ c.UpperOk x := by
  cases b <;> cases c <;> simp [minUpper, UpperOk]

/-- Adding two endpoints; `unbounded` absorbs, since a sum with an unknown side is
itself unknown. -/
def add : Bound → Bound → Bound
  | unbounded, _ => unbounded
  | _, unbounded => unbounded
  | finite m, finite n => finite (m + n)

theorem addLower (b c : Bound) {x y : Int} (hx : b.LowerOk x) (hy : c.LowerOk y) :
    (b.add c).LowerOk (x + y) := by
  cases b <;> cases c <;> simp_all [add, LowerOk]
  omega

theorem addUpper (b c : Bound) {x y : Int} (hx : b.UpperOk x) (hy : c.UpperOk y) :
    (b.add c).UpperOk (x + y) := by
  cases b <;> cases c <;> simp_all [add, UpperOk]
  omega

/-- Negating an endpoint turns a lower into an upper endpoint and back. -/
def neg : Bound → Bound
  | unbounded => unbounded
  | finite n => finite (-n)

theorem neg_lower_upper (b : Bound) (x : Int) : b.neg.UpperOk (-x) ↔ b.LowerOk x := by
  cases b <;> simp [neg, LowerOk, UpperOk]

theorem neg_upper_lower (b : Bound) (x : Int) : b.neg.LowerOk (-x) ↔ b.UpperOk x := by
  cases b <;> simp [neg, LowerOk, UpperOk]

end Bound

/-! ### The numeric content of a value -/

/-- The integer content of a value, if it has one: a quantity is its amount and a
time is its year, while item and string values have none. -/
def Value.numeric? : Value → Option Int
  | .quantity n => some n
  | .time y => some y
  | .item _ => none
  | .str _ => none

@[simp] theorem Value.numeric?_quantity (n : Int) : (Value.quantity n).numeric? = some n := rfl

@[simp] theorem Value.numeric?_time (y : Int) : (Value.time y).numeric? = some y := rfl

@[simp] theorem Value.numeric?_item (q : Qid) : (Value.item q).numeric? = none := rfl

@[simp] theorem Value.numeric?_str (s : String) : (Value.str s).numeric? = none := rfl

/-! ### Range constraints -/

/-- A **range constraint** (Q21510860) on one property: a minimum (P2313) and a
maximum (P2312), either of which may be absent. -/
structure RangeSpec where
  /-- The constrained property. -/
  pid : Pid
  /-- The minimum value (P2313). -/
  lower : Bound := .unbounded
  /-- The maximum value (P2312). -/
  upper : Bound := .unbounded
deriving DecidableEq, Repr, Inhabited

namespace RangeSpec

variable (s t : RangeSpec)

/-- The integers the constraint admits. -/
def Admits (x : Int) : Prop := s.lower.LowerOk x ∧ s.upper.UpperOk x

instance (x : Int) : Decidable (s.Admits x) := by unfold Admits; infer_instance

/-- The executable form of `Admits`. -/
def admitsB (x : Int) : Bool := decide (s.Admits x)

@[simp] theorem admitsB_iff (x : Int) : s.admitsB x = true ↔ s.Admits x := by
  simp [admitsB]

/-- A doubly unbounded range constraint — the "no bounds" case — admits everything. -/
theorem admits_unbounded (p : Pid) (x : Int) : Admits ⟨p, .unbounded, .unbounded⟩ x :=
  ⟨trivial, trivial⟩

/-- Widening the interval weakens the constraint. -/
theorem admits_mono {x : Int} (h : s.Admits x)
    (hl : ∀ y : Int, s.lower.LowerOk y → t.lower.LowerOk y)
    (hu : ∀ y : Int, s.upper.UpperOk y → t.upper.UpperOk y) : t.Admits x :=
  ⟨hl _ h.1, hu _ h.2⟩

/-- The conjunction of two range constraints on the same property. -/
def inter : RangeSpec :=
  { pid := s.pid, lower := s.lower.maxLower t.lower, upper := s.upper.minUpper t.upper }

/-- The intersection admits exactly what both constraints admit: a conjunction of
range constraints is again a range constraint. -/
theorem inter_admits (x : Int) : (s.inter t).Admits x ↔ s.Admits x ∧ t.Admits x := by
  simp only [Admits, inter, Bound.maxLower_ok, Bound.minUpper_ok]
  tauto

/-- The intersection is the greatest range constraint below both. -/
theorem inter_greatest (u : RangeSpec) (hs : ∀ x, u.Admits x → s.Admits x)
    (ht : ∀ x, u.Admits x → t.Admits x) : ∀ x, u.Admits x → (s.inter t).Admits x :=
  fun x hx => (inter_admits s t x).2 ⟨hs x hx, ht x hx⟩

/-- A value passes the constraint when its numeric content, if it has one, is
admitted; non-numeric values are outside the scope of a range constraint. -/
def valueOk (v : Value) : Bool :=
  match v.numeric? with
  | some x => s.admitsB x
  | none => true

theorem valueOk_iff (v : Value) :
    s.valueOk v = true ↔ ∀ x, v.numeric? = some x → s.Admits x := by
  cases v <;> simp [valueOk]

/-- A claim passes the constraint when it is not about the constrained property, or
its value is admitted. -/
def claimOk (c : Claim) : Bool :=
  if c.pid = s.pid then s.valueOk c.value else true

theorem claimOk_iff (c : Claim) :
    s.claimOk c = true ↔ ∀ x, c.pid = s.pid → c.value.numeric? = some x → s.Admits x := by
  unfold claimOk
  by_cases h : c.pid = s.pid
  · simp [h, valueOk_iff]
  · simp [h]

/-- A claim about another property is unconstrained. -/
theorem claimOk_of_pid_ne {c : Claim} (h : c.pid ≠ s.pid) : s.claimOk c = true := by
  simp [claimOk, h]

/-- A constraint whose maximum lies below its minimum admits nothing. -/
theorem not_admits_of_empty {a b x : Int} (hab : b < a) :
    ¬ Admits ⟨s.pid, .finite a, .finite b⟩ x := by
  rintro ⟨h1, h2⟩
  simp only [Bound.lowerOk_finite] at h1
  simp only [Bound.upperOk_finite] at h2
  omega

end RangeSpec

/-- A whole claim set passes a table of range constraints. -/
def rangeOk (specs : List RangeSpec) (cs : Claim.Set) : Bool :=
  cs.all fun c => specs.all fun s => s.claimOk c

theorem rangeOk_iff (specs : List RangeSpec) (cs : Claim.Set) :
    rangeOk specs cs = true ↔
      ∀ c ∈ cs, ∀ s ∈ specs, ∀ x, c.pid = s.pid → c.value.numeric? = some x → s.Admits x := by
  simp [rangeOk, List.all_eq_true, RangeSpec.claimOk_iff]

/-- From conformance, the minimum can be read back off any statement of the
constrained property. -/
theorem lower_le_of_rangeOk {specs : List RangeSpec} {cs : Claim.Set}
    (h : rangeOk specs cs = true) {s : RangeSpec} (hs : s ∈ specs) {c : Claim} (hc : c ∈ cs)
    (hp : c.pid = s.pid) {x a : Int} (hx : c.value.numeric? = some x)
    (ha : s.lower = .finite a) : a ≤ x := by
  have := (rangeOk_iff specs cs).1 h c hc s hs x hp hx
  have h1 := this.1
  rw [ha] at h1
  exact h1

/-- From conformance, the maximum can be read back off any statement of the
constrained property. -/
theorem le_upper_of_rangeOk {specs : List RangeSpec} {cs : Claim.Set}
    (h : rangeOk specs cs = true) {s : RangeSpec} (hs : s ∈ specs) {c : Claim} (hc : c ∈ cs)
    (hp : c.pid = s.pid) {x b : Int} (hx : c.value.numeric? = some x)
    (hb : s.upper = .finite b) : x ≤ b := by
  have := (rangeOk_iff specs cs).1 h c hc s hs x hp hx
  have h2 := this.2
  rw [hb] at h2
  exact h2

/-- In a conforming base, a property constrained to an empty range has no numeric
values at all. -/
theorem no_numeric_of_empty_range {specs : List RangeSpec} {cs : Claim.Set}
    (h : rangeOk specs cs = true) {s : RangeSpec} (hs : s ∈ specs) {a b : Int}
    (hl : s.lower = .finite a) (hu : s.upper = .finite b) (hab : b < a) :
    ∀ c ∈ cs, c.pid = s.pid → c.value.numeric? = none := by
  intro c hc hp
  cases hx : c.value.numeric? with
  | none => rfl
  | some x =>
      have h1 := lower_le_of_rangeOk h hs hc hp hx hl
      have h2 := le_upper_of_rangeOk h hs hc hp hx hu
      omega

/-- Conformance is downward closed: any sublist of a conforming claim set conforms. -/
theorem rangeOk_sublist {specs : List RangeSpec} {cs ds : Claim.Set} (hsub : ds.Sublist cs)
    (h : rangeOk specs cs = true) : rangeOk specs ds = true := by
  rw [rangeOk_iff] at h ⊢
  exact fun c hc => h c (hsub.mem hc)

/-- Filtering by rank can never introduce a range defect. -/
theorem rangeOk_truthy {specs : List RangeSpec} {cs : Claim.Set} (h : rangeOk specs cs = true) :
    rangeOk specs (Claim.truthy cs) = true :=
  rangeOk_sublist (List.filter_sublist) h

/-- Conformance splits over concatenation. -/
theorem rangeOk_append (specs : List RangeSpec) (cs ds : Claim.Set) :
    rangeOk specs (cs ++ ds) = true ↔ rangeOk specs cs = true ∧ rangeOk specs ds = true := by
  simp only [rangeOk_iff, List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-- Dropping constraints preserves conformance. -/
theorem rangeOk_sublist_specs {specs specs' : List RangeSpec} {cs : Claim.Set}
    (hsub : specs'.Sublist specs) (h : rangeOk specs cs = true) : rangeOk specs' cs = true := by
  rw [rangeOk_iff] at h ⊢
  exact fun c hc s hs => h c hc s (hsub.mem hs)

/-- A property mentioned by no constraint of the table is unconstrained. -/
theorem rangeOk_of_no_spec {specs : List RangeSpec} {cs : Claim.Set}
    (h : ∀ c ∈ cs, ∀ s ∈ specs, c.pid ≠ s.pid) : rangeOk specs cs = true := by
  rw [rangeOk_iff]
  intro c hc s hs x hp
  exact absurd hp (h c hc s hs)

/-! ### The difference-within-range constraint -/

/-- A **difference within range constraint** (Q21510854): the value of `pid` minus
the value of `base`, taken on the same item, must lie in the given interval. -/
structure DiffSpec where
  /-- The constrained property, e.g. `date of death` (P570). -/
  pid : Pid
  /-- The property it is compared with, e.g. `date of birth` (P569). -/
  base : Pid
  /-- The minimum of the difference. -/
  lower : Bound := .unbounded
  /-- The maximum of the difference. -/
  upper : Bound := .unbounded
deriving DecidableEq, Repr, Inhabited

namespace DiffSpec

variable (d : DiffSpec)

/-- The differences the constraint admits. -/
def Admits (x : Int) : Prop := d.lower.LowerOk x ∧ d.upper.UpperOk x

instance (x : Int) : Decidable (d.Admits x) := by unfold Admits; infer_instance

/-- Reversing the two properties negates the interval. -/
theorem admits_swap {x : Int} (h : d.Admits x) :
    Admits ⟨d.base, d.pid, d.upper.neg, d.lower.neg⟩ (-x) :=
  ⟨(Bound.neg_upper_lower d.upper x).2 h.2, (Bound.neg_lower_upper d.lower x).2 h.1⟩

/-- Differences compose: chaining two difference constraints gives a third one whose
interval is the sum of the two intervals. -/
theorem admits_trans (e : DiffSpec) {x y z : Int} (h₁ : d.Admits (x - y)) (h₂ : e.Admits (y - z)) :
    Admits ⟨d.pid, e.base, d.lower.add e.lower, d.upper.add e.upper⟩ (x - z) := by
  have hx : x - z = (x - y) + (y - z) := by ring
  refine ⟨?_, ?_⟩
  · rw [hx]; exact Bound.addLower _ _ h₁.1 h₂.1
  · rw [hx]; exact Bound.addUpper _ _ h₁.2 h₂.2

/-- The pair of a constrained claim and a claim it is compared with passes when the
difference of their numeric contents is admitted. -/
def pairOk (c b : Claim) : Bool :=
  if c.pid = d.pid ∧ b.pid = d.base ∧ b.subject = c.subject then
    match c.value.numeric?, b.value.numeric? with
    | some x, some y => decide (d.Admits (x - y))
    | _, _ => true
  else true

/-- The executable check on a whole claim set. -/
def setOk (cs : Claim.Set) : Bool := cs.all fun c => cs.all fun b => d.pairOk c b

theorem pairOk_iff (c b : Claim) :
    d.pairOk c b = true ↔
      ∀ x y, c.pid = d.pid → b.pid = d.base → b.subject = c.subject →
        c.value.numeric? = some x → b.value.numeric? = some y → d.Admits (x - y) := by
  unfold pairOk
  by_cases h : c.pid = d.pid ∧ b.pid = d.base ∧ b.subject = c.subject
  · obtain ⟨h1, h2, h3⟩ := h
    cases hc : c.value.numeric? <;> cases hb : b.value.numeric? <;>
      simp_all
  · simp only [h, if_false]
    simp only [true_iff]
    intro x y h1 h2 h3 _ _
    exact absurd ⟨h1, h2, h3⟩ h

theorem setOk_iff (cs : Claim.Set) :
    d.setOk cs = true ↔
      ∀ c ∈ cs, ∀ b ∈ cs, ∀ x y, c.pid = d.pid → b.pid = d.base → b.subject = c.subject →
        c.value.numeric? = some x → b.value.numeric? = some y → d.Admits (x - y) := by
  simp [setOk, List.all_eq_true, pairOk_iff]

/-- A constraint with a non-negative minimum orders the two properties: the value of
the constrained property is at least the value of the property it is compared with.
This is what makes `date of death` come after `date of birth`. -/
theorem base_le_of_setOk {cs : Claim.Set} (h : d.setOk cs = true) {a : Int} (ha : 0 ≤ a)
    (hl : d.lower = .finite a) {c b : Claim} (hc : c ∈ cs) (hb : b ∈ cs)
    (hcp : c.pid = d.pid) (hbp : b.pid = d.base) (hs : b.subject = c.subject)
    {x y : Int} (hx : c.value.numeric? = some x) (hy : b.value.numeric? = some y) : y ≤ x := by
  have := (d.setOk_iff cs).1 h c hc b hb x y hcp hbp hs hx hy
  have h1 := this.1
  rw [hl] at h1
  simp only [Bound.lowerOk_finite] at h1
  omega

/-- Conformance is downward closed along sublists. -/
theorem setOk_sublist {cs ds : Claim.Set} (hsub : ds.Sublist cs) (h : d.setOk cs = true) :
    d.setOk ds = true := by
  rw [setOk_iff] at h ⊢
  exact fun c hc b hb => h c (hsub.mem hc) b (hsub.mem hb)

/-- In particular the truthy fragment of a conforming base conforms. -/
theorem setOk_truthy {cs : Claim.Set} (h : d.setOk cs = true) :
    d.setOk (Claim.truthy cs) = true :=
  setOk_sublist d (List.filter_sublist) h

end DiffSpec

/-! ### Propagating a range along a difference constraint -/

/-- **Constraint propagation, lower end**: a minimum on the property a difference
constraint compares with, together with a minimum for the difference, bounds the
constrained property from below. -/
theorem lower_le_of_diff {specs : List RangeSpec} {cs : Claim.Set}
    (hr : rangeOk specs cs = true) {d : DiffSpec} (hd : d.setOk cs = true)
    {sb : RangeSpec} (hsb : sb ∈ specs) (hpb : sb.pid = d.base)
    {c b : Claim} (hc : c ∈ cs) (hb : b ∈ cs) (hcp : c.pid = d.pid) (hbp : b.pid = d.base)
    (hs : b.subject = c.subject) {x y a m : Int}
    (hx : c.value.numeric? = some x) (hy : b.value.numeric? = some y)
    (hlow : sb.lower = .finite a) (hdl : d.lower = .finite m) : a + m ≤ x := by
  have hay : a ≤ y := lower_le_of_rangeOk hr hsb hb (hbp.trans hpb.symm) hy hlow
  have hdiff := (d.setOk_iff cs).1 hd c hc b hb x y hcp hbp hs hx hy
  have h1 := hdiff.1
  rw [hdl] at h1
  simp only [Bound.lowerOk_finite] at h1
  omega

/-- **Constraint propagation, upper end**: a maximum on the compared property and a
maximum for the difference bound the constrained property from above. -/
theorem le_upper_of_diff {specs : List RangeSpec} {cs : Claim.Set}
    (hr : rangeOk specs cs = true) {d : DiffSpec} (hd : d.setOk cs = true)
    {sb : RangeSpec} (hsb : sb ∈ specs) (hpb : sb.pid = d.base)
    {c b : Claim} (hc : c ∈ cs) (hb : b ∈ cs) (hcp : c.pid = d.pid) (hbp : b.pid = d.base)
    (hs : b.subject = c.subject) {x y k M : Int}
    (hx : c.value.numeric? = some x) (hy : b.value.numeric? = some y)
    (hup : sb.upper = .finite k) (hdu : d.upper = .finite M) : x ≤ k + M := by
  have hyk : y ≤ k := le_upper_of_rangeOk hr hsb hb (hbp.trans hpb.symm) hy hup
  have hdiff := (d.setOk_iff cs).1 hd c hc b hb x y hcp hbp hs hx hy
  have h2 := hdiff.2
  rw [hdu] at h2
  simp only [Bound.upperOk_finite] at h2
  omega

/-! ### A worked fragment -/

namespace RangeExample

open RankExample (Q P)

/-- `population` (P1082) may not be negative, and no upper bound is given. -/
def populationRange : RangeSpec := { pid := P "P1082", lower := .finite 0 }

/-- `date of birth` (P569), recorded by its year, must lie in a plausible range. -/
def birthRange : RangeSpec :=
  { pid := P "P569", lower := .finite (-4000), upper := .finite 2100 }

/-- The table of range constraints of the fragment. -/
def specs : List RangeSpec := [populationRange, birthRange]

/-- `date of death` (P570) must be between 0 and 150 years after `date of birth`
(P569). -/
def lifespan : DiffSpec :=
  { pid := P "P570", base := P "P569", lower := .finite 0, upper := .finite 150 }

/-- Berlin's ranked population statements pass the range constraints. -/
theorem berlin_rangeOk : rangeOk specs RankExample.berlin = true := by decide

/-- A stylised person: born 1952, died 2001 -- inside both constraints. -/
def adams : Claim.Set :=
  [ { subject := Q "Q42", pid := P "P569", value := .time 1952 },
    { subject := Q "Q42", pid := P "P570", value := .time 2001 } ]

theorem adams_rangeOk : rangeOk specs adams = true := by decide

theorem adams_lifespan : lifespan.setOk adams = true := by decide

/-- A negative population is rejected. -/
theorem negative_population_rejected :
    rangeOk specs [{ subject := Q "Q64", pid := P "P1082", value := .quantity (-1) }] = false := by
  decide

/-- A birth year in the far future is rejected. -/
theorem future_birth_rejected :
    rangeOk specs [{ subject := Q "Q42", pid := P "P569", value := .time 3000 }] = false := by
  decide

/-- A death preceding the birth is rejected by the difference constraint, even though
both years are individually in range. -/
def timeTraveller : Claim.Set :=
  [ { subject := Q "Q42", pid := P "P569", value := .time 2001 },
    { subject := Q "Q42", pid := P "P570", value := .time 1952 } ]

theorem timeTraveller_rangeOk : rangeOk specs timeTraveller = true := by decide

theorem timeTraveller_lifespan_rejected : lifespan.setOk timeTraveller = false := by decide

/-- An implausibly long life is rejected too. -/
theorem methuselah_rejected :
    lifespan.setOk
      [ { subject := Q "Q42", pid := P "P569", value := .time 1000 },
        { subject := Q "Q42", pid := P "P570", value := .time 1969 } ] = false := by decide

/-- Two different items may have wholly unrelated birth and death years: the
constraint only compares values of the same item. -/
theorem cross_item_ignored :
    lifespan.setOk
      [ { subject := Q "Q42", pid := P "P569", value := .time 1952 },
        { subject := Q "Q64", pid := P "P570", value := .time 1900 } ] = true := by decide

/-- A base whose only offence sits on a deprecated statement is rejected, while its
truthy fragment -- what a default query returns -- passes. -/
def withDeprecated : Claim.Set :=
  { subject := Q "Q64", pid := P "P1082", value := .quantity (-5), rank := .deprecated } ::
    RankExample.berlin

theorem withDeprecated_rejected : rangeOk specs withDeprecated = false := by decide

theorem withDeprecated_truthy_ok : rangeOk specs (Claim.truthy withDeprecated) = true := by decide

/-- Item-valued statements are outside the scope of a range constraint. -/
theorem item_value_unconstrained :
    rangeOk specs [{ subject := Q "Q64", pid := P "P1082", value := .item (Q "Q183") }] = true := by
  decide

end RangeExample

end Wikidata
