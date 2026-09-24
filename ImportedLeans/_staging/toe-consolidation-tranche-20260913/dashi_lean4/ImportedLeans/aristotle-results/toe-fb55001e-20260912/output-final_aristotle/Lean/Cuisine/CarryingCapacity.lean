import Mathlib

/-!
# Cuisine layer 8: carrying capacity, and a second free-field hole

Lean mirror of the carrying-capacity and demand-exposure block of
`DASHI.Culture.Cuisine.ControlledSuccessCore`.

The Agda `CarryingCapacityProfile` carries three *independent* functions

```agda
    capacityValue : CapacityDimension → Nat
    demandValue   : CapacityDimension → Nat
    standing      : CapacityDimension → CapacityStanding
```

with no law relating `standing` to the two numbers.  This is the same shape of
hole as the free `overallRisk` field of `PublicationImpactAssessment` (see
`Cuisine.Publication`): a profile may report `withinCapacity` on a dimension
whose demand exceeds its capacity.

New content proved here:

* `LooseCapacityProfile.within_while_exceeded` — the hole, exhibited;
* `TightCapacityProfile` — the repair, with `standing` determined by the
  measurements, and the resulting characterisations
  (`exceeded_iff`, `standing_functional`, `standing_antitone_in_capacity`);
* `never_unknown` — an honest consequence of the total repair: a totally
  measured profile can never report `capacityUnknown`, so a fail-closed variant
  is needed for partial measurement;
* `GuardedCapacityProfile` — that variant, with `unknown_of_missing` (a missing
  measurement forces `capacityUnknown`) and `agrees_when_measured`;
* `bakeryBatchExposure_overloaded` — the supplied burst-demand witness really
  does exceed its same-window capacity.
-/

namespace Cuisine.CarryingCapacity

inductive CapacityDimension
  | physicalCapacity | ecologicalCapacity | labourCapacity | socialCapacity
  | ritualCapacity | epistemicCapacity
  deriving DecidableEq, Fintype, Repr

inductive CapacityStanding
  | withinCapacity | capacityExceeded | capacityUnknown
  deriving DecidableEq, Fintype, Repr

open CapacityDimension CapacityStanding

/-! ## The supplied record and its hole -/

/-- The Agda `CarryingCapacityProfile`, exactly as supplied. -/
structure LooseCapacityProfile where
  capacityValue : CapacityDimension → ℕ
  demandValue : CapacityDimension → ℕ
  standing : CapacityDimension → CapacityStanding
  capacityReading : String

/-- **The hole.**  A profile may report `withinCapacity` on a dimension whose
demand is four times its capacity. -/
theorem LooseCapacityProfile.within_while_exceeded :
    ∃ p : LooseCapacityProfile,
      p.capacityValue labourCapacity < p.demandValue labourCapacity ∧
        p.standing labourCapacity = withinCapacity :=
  ⟨{ capacityValue := fun _ => 3
     demandValue := fun _ => 12
     standing := fun _ => withinCapacity
     capacityReading := "unconstrained standing" },
   by decide, rfl⟩

/-! ## The repair -/

/-- Capacity profile whose standing is computed from the measurements. -/
structure TightCapacityProfile where
  capacityValue : CapacityDimension → ℕ
  demandValue : CapacityDimension → ℕ
  standing : CapacityDimension → CapacityStanding
  standingLaw : ∀ d,
    standing d = if demandValue d ≤ capacityValue d then withinCapacity else capacityExceeded

namespace TightCapacityProfile

theorem exceeded_iff (p : TightCapacityProfile) (d : CapacityDimension) :
    p.standing d = capacityExceeded ↔ p.capacityValue d < p.demandValue d := by
  rw [p.standingLaw d]
  split <;> simp_all

theorem within_iff (p : TightCapacityProfile) (d : CapacityDimension) :
    p.standing d = withinCapacity ↔ p.demandValue d ≤ p.capacityValue d := by
  rw [p.standingLaw d]
  split <;> simp_all

/-- The standing is a function of the measurements: two profiles with the same
capacity and demand agree everywhere. -/
theorem standing_functional (p q : TightCapacityProfile)
    (hc : p.capacityValue = q.capacityValue) (hd : p.demandValue = q.demandValue) :
    p.standing = q.standing := by
  funext d
  rw [p.standingLaw d, q.standingLaw d, hc, hd]

/-- Raising the capacity never worsens the standing. -/
theorem standing_antitone_in_capacity (p q : TightCapacityProfile) (d : CapacityDimension)
    (hd : p.demandValue d = q.demandValue d) (hc : p.capacityValue d ≤ q.capacityValue d)
    (h : p.standing d = withinCapacity) : q.standing d = withinCapacity := by
  rw [within_iff] at h ⊢
  omega

/-- **Honest consequence of the total repair.**  A profile with total
measurements can never report `capacityUnknown`; the unknown standing therefore
belongs to a partially measured variant, not to this one. -/
theorem never_unknown (p : TightCapacityProfile) (d : CapacityDimension) :
    p.standing d ≠ capacityUnknown := by
  rw [p.standingLaw d]
  split <;> decide

end TightCapacityProfile

/-! ## The fail-closed variant for partial measurement -/

/-- Standing computed from possibly-missing measurements, failing closed to
`capacityUnknown`. -/
def guardedStanding : Option ℕ → Option ℕ → CapacityStanding
  | some c, some x => if x ≤ c then withinCapacity else capacityExceeded
  | _, _ => capacityUnknown

structure GuardedCapacityProfile where
  capacityValue : CapacityDimension → Option ℕ
  demandValue : CapacityDimension → Option ℕ
  standing : CapacityDimension → CapacityStanding
  standingLaw : ∀ d, standing d = guardedStanding (capacityValue d) (demandValue d)

namespace GuardedCapacityProfile

/-- Fail-closed: a missing measurement on either side forces `capacityUnknown`,
never `withinCapacity`. -/
theorem unknown_of_missing (p : GuardedCapacityProfile) (d : CapacityDimension)
    (h : p.capacityValue d = none ∨ p.demandValue d = none) :
    p.standing d = capacityUnknown := by
  rw [p.standingLaw d]
  rcases h with h | h <;> rw [h] <;> cases p.demandValue d <;> cases p.capacityValue d <;> rfl

/-- Where both measurements are present, the guarded profile agrees with the
total repair. -/
theorem agrees_when_measured (p : GuardedCapacityProfile) (d : CapacityDimension)
    {c x : ℕ} (hc : p.capacityValue d = some c) (hx : p.demandValue d = some x) :
    p.standing d = if x ≤ c then withinCapacity else capacityExceeded := by
  rw [p.standingLaw d, hc, hx]; rfl

/-- Conversely `withinCapacity` is reported only on fully measured
dimensions. -/
theorem measured_of_within (p : GuardedCapacityProfile) (d : CapacityDimension)
    (h : p.standing d = withinCapacity) :
    ∃ c x : ℕ, p.capacityValue d = some c ∧ p.demandValue d = some x ∧ x ≤ c := by
  rw [p.standingLaw d] at h
  rcases hc : p.capacityValue d with _ | c <;> rcases hx : p.demandValue d with _ | x <;>
    rw [hc, hx] at h <;> simp only [guardedStanding] at h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · refine ⟨c, x, rfl, rfl, ?_⟩
    by_contra hle
    rw [if_neg hle] at h
    exact absurd h (by decide)

end GuardedCapacityProfile

/-! ## The supplied burst-demand witness -/

inductive DemandShape
  | smoothDemand | burstDemand | viralBatchDemand | seasonalDemand | unknownDemandShape
  deriving DecidableEq, Fintype, Repr

inductive OverloadKind
  | demandOverload | visibilityExposure | marginCollapse | tourismOverload
  | ingredientPressure | ritualOverload | epistemicOverexposure
  deriving DecidableEq, Fintype, Repr

structure DemandExposure where
  objectLabel : String
  baselineAttention : ℕ
  amplifiedAttention : ℕ
  demandShape : DemandShape
  leadTime : ℕ
  sameWindowCapacity : ℕ
  perishabilityOrFragility : ℕ
  overloadKinds : List OverloadKind
  demandReading : String

/-- The Agda `canonicalBakeryBatchExposure`. -/
def bakeryBatchExposure : DemandExposure where
  objectLabel := "candidate bakery burst-demand pattern"
  baselineAttention := 1
  amplifiedAttention := 12
  demandShape := .viralBatchDemand
  leadTime := 12
  sameWindowCapacity := 3
  perishabilityOrFragility := 8
  overloadKinds := [.demandOverload, .visibilityExposure, .marginCollapse]
  demandReading :=
    "long lead times, narrow service windows, perishability and batch arrivals"

/-- The supplied numbers really do describe an overload: amplified attention
exceeds the same-window capacity, and the lead time exceeds it too.  The Agda
module records the numbers but states no relation between them. -/
theorem bakeryBatchExposure_overloaded :
    bakeryBatchExposure.sameWindowCapacity < bakeryBatchExposure.amplifiedAttention ∧
      bakeryBatchExposure.sameWindowCapacity < bakeryBatchExposure.leadTime ∧
      bakeryBatchExposure.baselineAttention < bakeryBatchExposure.sameWindowCapacity := by
  refine ⟨by decide, by decide, by decide⟩

/-- Reading the exposure as a capacity profile on the labour dimension, the
repaired record reports the overload. -/
def bakeryCapacityProfile : TightCapacityProfile where
  capacityValue := fun _ => bakeryBatchExposure.sameWindowCapacity
  demandValue := fun _ => bakeryBatchExposure.amplifiedAttention
  standing := fun _ =>
    if bakeryBatchExposure.amplifiedAttention ≤ bakeryBatchExposure.sameWindowCapacity then
      withinCapacity
    else capacityExceeded
  standingLaw := fun _ => rfl

theorem bakeryCapacityProfile_exceeded (d : CapacityDimension) :
    bakeryCapacityProfile.standing d = capacityExceeded :=
  (bakeryCapacityProfile.exceeded_iff d).2 (by simp [bakeryCapacityProfile, bakeryBatchExposure])

end Cuisine.CarryingCapacity
