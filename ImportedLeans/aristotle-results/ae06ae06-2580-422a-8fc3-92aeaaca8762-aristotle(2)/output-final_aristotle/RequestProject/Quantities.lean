import RequestProject.Engine

/-!
# Quantities: units and uncertainty intervals

Wikidata's *quantity* datatype is not a bare number: a quantity carries an
`amount`, an optional uncertainty interval given by a lower and an upper bound,
and a `unit` — an item, such as *metre* (Q11573).  Units are related to each other
by `conversion to SI unit` (P2370), which records the factor converting a unit
into the corresponding SI unit.

This file formalises that datatype and the arithmetic of unit conversion.

* `Wikidata.Quantity` — amount, bounds and unit, with well-formedness
  (`lowerBound ≤ amount ≤ upperBound`) and the interval `Covers` it denotes.
* `Wikidata.Quantity.scale` — rescaling by a factor, with the laws: scaling is
  functorial (`scale_scale`, `scale_one`), preserves well-formedness and, for a
  positive factor, preserves and reflects the interval and the order of amounts.
* `Wikidata.UnitSystem` — a table of `conversion to SI unit` factors, the SI value
  `siValue` of a quantity, and the comparison of quantities *across* units.
  Proved: comparison by SI value is a total preorder, quantities agreeing in SI
  value are interchangeable for it, and conversion of a whole quantity into SI
  units is well-formed and covers exactly the converted values.
* `Wikidata.Quantity.Consistent` — two measurements are consistent when their
  uncertainty intervals overlap.  Proved: consistency is reflexive on well-formed
  quantities and symmetric, and is invariant under conversion to a common unit,
  so whether two measurements agree does not depend on the unit they are recorded
  in.

The worked fragment records a length as 1 kilometre and as 1000 metres — the same
SI value, hence consistent — while 1 kilometre and 1 metre are not.
-/

namespace Wikidata

/-- A Wikidata quantity: an amount with an uncertainty interval and a unit. -/
structure Quantity where
  /-- The amount. -/
  amount : ℚ
  /-- The lower bound of the uncertainty interval. -/
  lowerBound : ℚ := amount
  /-- The upper bound of the uncertainty interval. -/
  upperBound : ℚ := amount
  /-- The unit, an item such as *metre* (Q11573). -/
  unit : Qid
deriving DecidableEq, Repr, Inhabited

namespace Quantity

variable (q : Quantity)

/-- A quantity is well-formed when its amount lies inside its uncertainty
interval. -/
def Wf : Prop := q.lowerBound ≤ q.amount ∧ q.amount ≤ q.upperBound

/-- The decision procedure for well-formedness. -/
def wfB : Bool := decide (q.lowerBound ≤ q.amount) && decide (q.amount ≤ q.upperBound)

@[simp] theorem wfB_iff : q.wfB = true ↔ q.Wf := by simp [wfB, Wf]

/-- The values the quantity is compatible with: its uncertainty interval. -/
def Covers (x : ℚ) : Prop := q.lowerBound ≤ x ∧ x ≤ q.upperBound

theorem covers_amount (h : q.Wf) : q.Covers q.amount := h

/-- Rescaling a quantity by a factor, keeping the unit implicit in the caller. -/
def scale (k : ℚ) (u : Qid) : Quantity where
  amount := k * q.amount
  lowerBound := k * q.lowerBound
  upperBound := k * q.upperBound
  unit := u

@[simp] theorem scale_amount (k : ℚ) (u : Qid) : (q.scale k u).amount = k * q.amount := rfl

@[simp] theorem scale_lowerBound (k : ℚ) (u : Qid) :
    (q.scale k u).lowerBound = k * q.lowerBound := rfl

@[simp] theorem scale_upperBound (k : ℚ) (u : Qid) :
    (q.scale k u).upperBound = k * q.upperBound := rfl

@[simp] theorem scale_unit (k : ℚ) (u : Qid) : (q.scale k u).unit = u := rfl

/-- Scaling by `1` changes nothing but the recorded unit. -/
theorem scale_one : q.scale 1 q.unit = q := by
  cases q; simp [scale]

/-- Scaling is functorial: two conversions compose into one. -/
theorem scale_scale (k k' : ℚ) (u u' : Qid) :
    (q.scale k u).scale k' u' = q.scale (k' * k) u' := by
  cases q; simp [scale, mul_assoc]

/-- A positive rescaling preserves well-formedness. -/
theorem wf_scale {k : ℚ} (hk : 0 < k) (u : Qid) (h : q.Wf) : (q.scale k u).Wf :=
  ⟨by simpa using mul_le_mul_of_nonneg_left h.1 hk.le,
   by simpa using mul_le_mul_of_nonneg_left h.2 hk.le⟩

/-- A positive rescaling transports the uncertainty interval exactly. -/
theorem covers_scale_iff {k : ℚ} (hk : 0 < k) (u : Qid) (x : ℚ) :
    (q.scale k u).Covers (k * x) ↔ q.Covers x := by
  simp only [Covers, scale_lowerBound, scale_upperBound]
  constructor
  · intro h
    exact ⟨le_of_mul_le_mul_left h.1 hk, le_of_mul_le_mul_left h.2 hk⟩
  · intro h
    exact ⟨mul_le_mul_of_nonneg_left h.1 hk.le, mul_le_mul_of_nonneg_left h.2 hk.le⟩

/-- A positive rescaling preserves and reflects the order of amounts. -/
theorem scale_amount_le_iff {k : ℚ} (hk : 0 < k) (u u' : Qid) (q' : Quantity) :
    (q.scale k u).amount ≤ (q'.scale k u').amount ↔ q.amount ≤ q'.amount := by
  simpa using mul_le_mul_iff_of_pos_left hk

/-! ### Consistency of measurements -/

/-- Two quantities are *consistent* when their uncertainty intervals overlap. -/
def Consistent (q q' : Quantity) : Prop := ∃ x, q.Covers x ∧ q'.Covers x

theorem consistent_comm {q q' : Quantity} (h : Consistent q q') : Consistent q' q := by
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, hx', hx⟩

theorem consistent_self (h : q.Wf) : Consistent q q :=
  ⟨q.amount, covers_amount q h, covers_amount q h⟩

/-- Whether two measurements agree does not depend on the unit they are converted
to: a common positive rescaling preserves and reflects consistency. -/
theorem consistent_scale_iff {k : ℚ} (hk : 0 < k) (u u' : Qid) (q q' : Quantity) :
    Consistent (q.scale k u) (q'.scale k u') ↔ Consistent q q' := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    refine ⟨x / k, ?_, ?_⟩
    · exact (covers_scale_iff q hk u (x / k)).1 (by rwa [mul_div_cancel₀ _ hk.ne'])
    · exact (covers_scale_iff q' hk u' (x / k)).1 (by rwa [mul_div_cancel₀ _ hk.ne'])
  · rintro ⟨x, hx, hx'⟩
    exact ⟨k * x, (covers_scale_iff q hk u x).2 hx, (covers_scale_iff q' hk u' x).2 hx'⟩

end Quantity

/-! ### Unit systems -/

/-- A table of `conversion to SI unit` (P2370) factors: the factor converting each
unit into the SI unit `si`. -/
structure UnitSystem where
  /-- The SI unit all the others are converted to. -/
  si : Qid
  /-- The conversion factor of each unit (missing units default to `1`). -/
  factors : List (Qid × ℚ) := []
deriving DecidableEq, Repr, Inhabited

namespace UnitSystem

variable (U : UnitSystem)

/-- The conversion factor of a unit. -/
def factor (u : Qid) : ℚ := (U.factors.lookup u).getD 1

/-- All recorded conversion factors are positive. -/
def factorsPositive : Bool := U.factors.all (fun p => decide (0 < p.2))

theorem factor_pos (h : U.factorsPositive = true) (u : Qid) : 0 < U.factor u := by
  simp only [factorsPositive, List.all_eq_true, decide_eq_true_eq] at h
  unfold factor
  cases hu : U.factors.lookup u with
  | none => norm_num
  | some k =>
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hu
    have : (u, k) ∈ U.factors := by rw [hl]; simp
    simpa using h (u, k) this

/-- The quantity converted into the SI unit. -/
def toSI (q : Quantity) : Quantity := q.scale (U.factor q.unit) U.si

/-- The numerical value of a quantity in the SI unit. -/
def siValue (q : Quantity) : ℚ := U.factor q.unit * q.amount

@[simp] theorem toSI_amount (q : Quantity) : (U.toSI q).amount = U.siValue q := rfl

@[simp] theorem toSI_unit (q : Quantity) : (U.toSI q).unit = U.si := rfl

/-- Conversion to SI units preserves well-formedness. -/
theorem wf_toSI (h : U.factorsPositive = true) {q : Quantity} (hq : q.Wf) : (U.toSI q).Wf :=
  q.wf_scale (U.factor_pos h q.unit) U.si hq

/-- Conversion transports the uncertainty interval exactly. -/
theorem covers_toSI_iff (h : U.factorsPositive = true) (q : Quantity) (x : ℚ) :
    (U.toSI q).Covers (U.factor q.unit * x) ↔ q.Covers x :=
  q.covers_scale_iff (U.factor_pos h q.unit) U.si x

/-- Comparison of quantities across units, by their SI value. -/
def Le (q q' : Quantity) : Prop := U.siValue q ≤ U.siValue q'

theorem le_refl (q : Quantity) : U.Le q q := le_rfl

theorem le_trans {q q' q'' : Quantity} (h : U.Le q q') (h' : U.Le q' q'') : U.Le q q'' :=
  _root_.le_trans h h'

theorem le_total (q q' : Quantity) : U.Le q q' ∨ U.Le q' q := _root_.le_total _ _

/-- Quantities with the same SI value are interchangeable for the comparison. -/
theorem le_congr {q q' r : Quantity} (h : U.siValue q = U.siValue q') :
    U.Le q r ↔ U.Le q' r := by simp [Le, h]

/-- A quantity recorded in a unit and its conversion into SI units have the same
SI value, since the SI unit converts to itself by the factor `1` whenever it is
not listed in the table. -/
theorem siValue_toSI (q : Quantity) (hsi : U.factor U.si = 1) :
    U.siValue (U.toSI q) = U.siValue q := by
  simp [siValue, toSI, Quantity.scale, hsi]

end UnitSystem

/-! ### A worked fragment: metres, kilometres and centimetres -/

namespace QuantityExample

open Wikidata

/-- The unit *metre* (Q11573). -/
def metre : Qid := .wd "Q11573"
/-- The unit *kilometre* (Q828224). -/
def kilometre : Qid := .wd "Q828224"
/-- The unit *centimetre* (Q174728). -/
def centimetre : Qid := .wd "Q174728"

/-- The SI unit system for lengths: the factors `conversion to SI unit` (P2370). -/
def lengths : UnitSystem where
  si := metre
  factors := [(metre, 1), (kilometre, 1000), (centimetre, 1 / 100)]

theorem lengths_positive : lengths.factorsPositive = true := by
  norm_num [UnitSystem.factorsPositive, lengths]

/-- The conversion factors of the three units. -/
theorem factor_metre : lengths.factor metre = 1 := by decide

theorem factor_kilometre : lengths.factor kilometre = 1000 := by decide

theorem factor_centimetre : lengths.factor centimetre = 1 / 100 := rfl

/-- One kilometre. -/
def oneKm : Quantity := { amount := 1, unit := kilometre }
/-- One thousand metres. -/
def thousandM : Quantity := { amount := 1000, unit := metre }
/-- One metre. -/
def oneM : Quantity := { amount := 1, unit := metre }
/-- A length measured as `1000 ± 5` metres. -/
def roughKm : Quantity :=
  { amount := 1000, lowerBound := 995, upperBound := 1005, unit := metre }

/-- One kilometre and one thousand metres have the same SI value. -/
theorem km_eq_thousandM : lengths.siValue oneKm = lengths.siValue thousandM := by
  simp only [UnitSystem.siValue, oneKm, thousandM, factor_metre, factor_kilometre]
  norm_num

/-- Hence each is at most the other. -/
theorem km_le_thousandM : lengths.Le oneKm thousandM := le_of_eq km_eq_thousandM

/-- One metre is strictly less than one kilometre, so the comparison across units
is not degenerate. -/
theorem oneM_lt_oneKm : lengths.siValue oneM < lengths.siValue oneKm := by
  simp only [UnitSystem.siValue, oneM, oneKm, factor_metre, factor_kilometre]
  norm_num

/-- The rough measurement is well-formed … -/
theorem roughKm_wf : roughKm.Wf := by
  constructor <;> norm_num [roughKm]

/-- … and is consistent with the exact one thousand metres. -/
theorem roughKm_consistent : Quantity.Consistent roughKm thousandM := by
  refine ⟨1000, ⟨by norm_num [roughKm], by norm_num [roughKm]⟩, ?_⟩
  exact ⟨by norm_num [thousandM], by norm_num [thousandM]⟩

/-- One metre is *not* consistent with the rough kilometre: their intervals are
disjoint. -/
theorem oneM_not_consistent : ¬ Quantity.Consistent roughKm oneM := by
  rintro ⟨x, ⟨hl, -⟩, -, hu⟩
  simp only [roughKm, oneM] at hl hu
  linarith

/-- Converting the rough measurement into SI units leaves it well-formed. -/
theorem toSI_roughKm_wf : (lengths.toSI roughKm).Wf :=
  lengths.wf_toSI lengths_positive roughKm_wf

/-- Converting one kilometre into metres gives exactly one thousand metres. -/
theorem toSI_oneKm : lengths.toSI oneKm = thousandM := by
  simp only [UnitSystem.toSI, oneKm, factor_kilometre, Quantity.scale, thousandM]
  norm_num [lengths]

end QuantityExample

end Wikidata
