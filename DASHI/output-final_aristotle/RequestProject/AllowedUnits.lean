/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Quantities
import RequestProject.PropertyEngine

/-!
# The allowed-units constraint (Q21514353)

A Wikidata property whose values are quantities usually restricts the *unit*
those quantities may be recorded in: `height` (P2048) expects a length, not a
duration.  This is the **allowed units constraint** (Q21514353): the property
declares a list of unit items, and every quantity-valued statement of the
property must use one of them.

`RequestProject.Quantities` already has the quantity datatype, the
`conversion to SI unit` (P2370) table and the comparison of quantities across
units.  This file adds the constraint on top of it.

* `Wikidata.UnitConstraint` — a property together with its list of allowed units,
  the abstract requirement `UnitConstraint.Satisfies` on a table of
  quantity-valued statements, and the executable check `UnitConstraint.checkB`,
  proved to decide it exactly (`UnitConstraint.checkB_iff`) and to report exactly
  the offending statements (`UnitConstraint.mem_violations_iff`).
* Proved: enlarging the list of allowed units only weakens the constraint; an
  empty list forces the property to have no quantity statements; a constraint is
  satisfied by the statements it does not mention, and adding a statement in an
  allowed unit preserves it.
* **Normalisation**: converting every value into the SI unit of a unit system
  satisfies the constraint that allows the SI unit — and, when the system is
  positive and the SI unit converts to itself, it changes neither the SI value
  nor the well-formedness of any measurement
  (`Wikidata.UnitConstraint.satisfies_normalise`,
  `Wikidata.UnitConstraint.siValue_normalise`).  So a base violating an
  allowed-units constraint can always be repaired without losing information.

The worked fragment records three heights, one of them in centimetres, against a
constraint allowing only metres: the checker reports exactly that statement, the
normalised base passes, and the repaired value denotes the same length.
-/

namespace Wikidata

/-- The **allowed units constraint** (Q21514353) of a property: the units its
quantity values may use. -/
structure UnitConstraint where
  /-- The constrained property, e.g. `height` (P2048). -/
  prop : Pid
  /-- The allowed unit items. -/
  units : List Qid
deriving DecidableEq, Repr, Inhabited

namespace UnitConstraint

variable (C : UnitConstraint)

/-- The abstract requirement on a table of quantity-valued statements: every
value uses an allowed unit. -/
def Satisfies (C : UnitConstraint) (stmts : List (Qid × Quantity)) : Prop :=
  ∀ p ∈ stmts, p.2.unit ∈ C.units

/-- The executable check. -/
def checkB (stmts : List (Qid × Quantity)) : Bool :=
  stmts.all (fun p => C.units.contains p.2.unit)

/-- The statements the check objects to. -/
def violations (stmts : List (Qid × Quantity)) : List (Qid × Quantity) :=
  stmts.filter (fun p => !C.units.contains p.2.unit)

@[simp] theorem checkB_iff (stmts : List (Qid × Quantity)) :
    C.checkB stmts = true ↔ C.Satisfies stmts := by
  simp [checkB, Satisfies]

theorem mem_violations_iff {stmts : List (Qid × Quantity)} {p : Qid × Quantity} :
    p ∈ C.violations stmts ↔ p ∈ stmts ∧ p.2.unit ∉ C.units := by
  simp [violations, List.mem_filter]

/-- The check passes exactly when it reports nothing. -/
theorem violations_eq_nil_iff (stmts : List (Qid × Quantity)) :
    C.violations stmts = [] ↔ C.Satisfies stmts := by
  rw [violations, List.filter_eq_nil_iff]
  simp [Satisfies]

/-- Allowing more units only weakens the constraint. -/
theorem satisfies_mono {C C' : UnitConstraint} (h : C.units ⊆ C'.units)
    {stmts : List (Qid × Quantity)} (hs : C.Satisfies stmts) : C'.Satisfies stmts :=
  fun p hp => h (hs p hp)

/-- Nothing is required of an empty table of statements. -/
theorem satisfies_nil : C.Satisfies [] := by simp [Satisfies]

/-- A constraint allowing no unit at all forces the property to carry no quantity
statements. -/
theorem eq_nil_of_satisfies_units_nil {stmts : List (Qid × Quantity)}
    (hu : C.units = []) (h : C.Satisfies stmts) : stmts = [] := by
  cases stmts with
  | nil => rfl
  | cons a l => exact absurd (h a (by simp)) (by simp [hu])

/-- Adding a statement in an allowed unit preserves the constraint. -/
theorem satisfies_cons {stmts : List (Qid × Quantity)} {p : Qid × Quantity}
    (hp : p.2.unit ∈ C.units) (h : C.Satisfies stmts) : C.Satisfies (p :: stmts) := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hp
  · exact h q hq

/-- Satisfaction only depends on the statements listed. -/
theorem satisfies_append {stmts stmts' : List (Qid × Quantity)} :
    C.Satisfies (stmts ++ stmts') ↔ C.Satisfies stmts ∧ C.Satisfies stmts' := by
  simp only [Satisfies, List.mem_append]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h, h'⟩ p (hp | hp)
    · exact h p hp
    · exact h' p hp

/-! ### Repairing a base by conversion -/

/-- Convert every value of a table into the SI unit of a unit system. -/
def normalise (U : UnitSystem) (stmts : List (Qid × Quantity)) : List (Qid × Quantity) :=
  stmts.map (fun p => (p.1, U.toSI p.2))

@[simp] theorem length_normalise (U : UnitSystem) (stmts : List (Qid × Quantity)) :
    (normalise U stmts).length = stmts.length := by simp [normalise]

/-- The normalised table satisfies any constraint allowing the SI unit. -/
theorem satisfies_normalise {U : UnitSystem} (hsi : U.si ∈ C.units)
    (stmts : List (Qid × Quantity)) : C.Satisfies (normalise U stmts) := by
  intro p hp
  simp only [normalise, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  simpa using hsi

/-- Normalisation does not change what a measurement says: every converted value
has the same SI value as the original. -/
theorem siValue_normalise (U : UnitSystem) (hsi : U.factor U.si = 1)
    (stmts : List (Qid × Quantity)) :
    (normalise U stmts).map (fun p => U.siValue p.2) = stmts.map (fun p => U.siValue p.2) := by
  simp only [normalise, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun p _ => U.siValue_toSI p.2 hsi)

/-- Normalisation preserves well-formedness of every measurement. -/
theorem wf_normalise {U : UnitSystem} (hU : U.factorsPositive = true)
    {stmts : List (Qid × Quantity)} (h : ∀ p ∈ stmts, p.2.Wf) :
    ∀ p ∈ normalise U stmts, p.2.Wf := by
  intro p hp
  simp only [normalise, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact U.wf_toSI hU (h q hq)

end UnitConstraint

/-! ### A worked fragment: heights in metres -/

namespace UnitConstraintExample

open Wikidata QuantityExample

/-- `height` (P2048). -/
def height : Pid := .wd "P2048"

/-- The allowed-units constraint of `height`: metres only. -/
def heightMetres : UnitConstraint := ⟨height, [metre]⟩

/-- Three recorded heights, the last one in centimetres. -/
def heights : List (Qid × Quantity) :=
  [(.wd "Q1", { amount := 2, unit := metre }),
   (.wd "Q2", { amount := 3 / 2, unit := metre }),
   (.wd "Q3", { amount := 180, unit := centimetre })]

/-- The constraint is violated … -/
theorem heights_violate : ¬ heightMetres.Satisfies heights := by
  rw [← UnitConstraint.checkB_iff]
  decide

/-- … by exactly the centimetre statement. -/
theorem heights_violations :
    heightMetres.violations heights = [(.wd "Q3", { amount := 180, unit := centimetre })] := by
  decide

/-- Normalising into the SI unit of the length system repairs the base. -/
theorem normalised_ok :
    heightMetres.Satisfies (UnitConstraint.normalise lengths heights) :=
  UnitConstraint.satisfies_normalise heightMetres (by simp [heightMetres, lengths]) heights

/-- The repaired value is the same length: 180 centimetres becomes 1.8 metres. -/
theorem repaired_value :
    lengths.toSI { amount := 180, unit := centimetre } =
      { amount := 9 / 5, lowerBound := 9 / 5, upperBound := 9 / 5, unit := metre } := by
  simp only [UnitSystem.toSI, factor_centimetre, Quantity.scale]
  norm_num [lengths, metre]

/-- Allowing centimetres as well makes the original base pass. -/
def heightLengths : UnitConstraint := ⟨height, [metre, centimetre]⟩

theorem heights_ok_relaxed : heightLengths.Satisfies heights := by
  rw [← UnitConstraint.checkB_iff]
  decide

end UnitConstraintExample

end Wikidata
