import Mathlib

/-!
# Cuisine layer 3: the mole process route, its defect, and its repair

Lean mirror of `DASHI.Culture.Cuisine.MoleProcessArchitecture`.

## The defect

In the Agda source, `ProcessEvent` is a **record** whose two state arguments are
*phantom* indices:

```agda
record ProcessEvent (before after : CandidateMoleState) : Set where
  constructor processEvent
  field
    operation         : MoleOperation
    thermalStateAfter : ThermalState
    control           : ProcessControl
    eventReading      : String
```

None of the four fields mentions `before` or `after`.  Consequently
`ProcessEvent a b` is inhabited for *every* pair `a b`, and therefore so is
`ProcessRoute a b`, the reflexive-transitive closure built from it.

`MoleProcessArchitecture.canonicalOrderSensitiveRouteWitness` and the regression
`CuisineFormalismTests.moleRouteEndpointsDistinct` establish only that the two
*endpoint constructors* `friedThenRehydratedChileState` and
`rehydratedThenFriedChileState` are different elements of the enumeration.  They
do **not** establish that the two cooking orders are unmergeable, because the
route relation relates everything to everything.  `ProcessRoute` in its supplied
form carries no information beyond the endpoints one chooses to write down.

`DASHI.Culture.Cuisine.CompositionProvenanceCore.Route` has the same shape of
defect: its `routeStep` constructor demands `beforeState transition ≡ a` and
`afterState transition ≡ b`, but `RecipeTransition` is a record with free
`beforeState`/`afterState` fields, so those equations can always be satisfied.

## The repair

`MoleStep` below is an inductive family whose constructors are exactly the ten
`ProcessEvent` values actually named in the Agda module.  Its transitive closure
`MoleRoute` is a genuine reachability relation, and for it the intended
order-sensitivity statement is a theorem: the two chile endpoints are mutually
unreachable.

Everything below is a statement about finite carriers; no rheology, chemistry or
food-safety claim is made or used.
-/

namespace Cuisine.ProcessRoute

/-! ## Mirrored carriers -/

inductive MoleOperation
  | dehydrateOperation | toastOperation | fryOperation | charOperation
  | carboniseOperation | washOperation | rehydrateOperation | grindOperation
  | shearOperation | disperseOperation | reduceOperation | simmerOperation
  | restOperation
  deriving DecidableEq, Fintype, Repr

inductive ThermalState
  | rawThermalState | driedThermalState | toastedThermalState | friedThermalState
  | charredThermalState | controlledCarbonisedState | washedCarbonisedState
  | acridlyBurntState
  deriving DecidableEq, Fintype, Repr

inductive CandidateMoleState
  | rawChileState | friedChileState | rehydratedChileState
  | friedThenRehydratedChileState | rehydratedThenFriedChileState
  | rawSeedState | carbonisedSeedState | washedAshState
  | rawComponentAssemblyState | differentiallyPreparedAssemblyState
  | groundPasteState | hotFatDispersedPasteState | serviceStableMoleState
  deriving DecidableEq, Fintype, Repr

open CandidateMoleState

structure ProcessControl where
  timeCoordinate : ℕ
  temperatureCoordinate : ℕ
  medium : String
  observableTarget : String

/-! ## The supplied definitions, transcribed exactly -/

/-- The Agda record, indices and all.  The indices are phantom: this is the
defect. -/
structure ProcessEvent (_before _after : CandidateMoleState) where
  operation : MoleOperation
  thermalStateAfter : ThermalState
  control : ProcessControl
  eventReading : String

/-- The Agda `ProcessRoute`, built from `ProcessEvent`. -/
inductive ProcessRouteRel : CandidateMoleState → CandidateMoleState → Prop
  | routeStop {s : CandidateMoleState} : ProcessRouteRel s s
  | routeStep {before middle after : CandidateMoleState} :
      ProcessEvent before middle → ProcessRouteRel middle after → ProcessRouteRel before after

/-- **The defect, part one.**  Every pair of states carries an event. -/
theorem processEvent_total (a b : CandidateMoleState) : Nonempty (ProcessEvent a b) :=
  ⟨{ operation := .restOperation
     thermalStateAfter := .rawThermalState
     control := ⟨0, 0, "", ""⟩
     eventReading := "vacuous event: the Agda record ignores its indices" }⟩

/-- **The defect, part two.**  The supplied route relation is the total
relation: `ProcessRoute a b` holds for all `a` and `b`.  So the relation proves
nothing about admissible cooking orders. -/
theorem processRouteRel_total (a b : CandidateMoleState) : ProcessRouteRel a b :=
  (processEvent_total a b).elim fun e => .routeStep e .routeStop

/-- **Consequence for the order-sensitivity witness.**  The two endpoints of
`canonicalOrderSensitiveRouteWitness` are distinct as elements of the
enumeration, yet each is reachable from the other in the supplied route
relation.  Distinct endpoints therefore do not, by themselves, witness
order-sensitivity. -/
theorem supplied_witness_does_not_separate_orders :
    friedThenRehydratedChileState ≠ rehydratedThenFriedChileState ∧
      ProcessRouteRel friedThenRehydratedChileState rehydratedThenFriedChileState ∧
      ProcessRouteRel rehydratedThenFriedChileState friedThenRehydratedChileState :=
  ⟨by decide, processRouteRel_total _ _, processRouteRel_total _ _⟩

/-! ## The repair: an inductive step family

The constructors are exactly the ten named `ProcessEvent` values of the Agda
module: `fryRawChile`, `rehydrateFriedChile`, `rehydrateRawChile`,
`fryRehydratedChile`, `carboniseSeeds`, `washCarbonisedSeeds`,
`prepareAssembly`, `grindAssembly`, `dispersePaste`, `simmerMole`. -/

inductive MoleStep : CandidateMoleState → CandidateMoleState → Prop
  | fryRawChile : MoleStep rawChileState friedChileState
  | rehydrateFriedChile : MoleStep friedChileState friedThenRehydratedChileState
  | rehydrateRawChile : MoleStep rawChileState rehydratedChileState
  | fryRehydratedChile : MoleStep rehydratedChileState rehydratedThenFriedChileState
  | carboniseSeeds : MoleStep rawSeedState carbonisedSeedState
  | washCarbonisedSeeds : MoleStep carbonisedSeedState washedAshState
  | prepareAssembly :
      MoleStep rawComponentAssemblyState differentiallyPreparedAssemblyState
  | grindAssembly : MoleStep differentiallyPreparedAssemblyState groundPasteState
  | dispersePaste : MoleStep groundPasteState hotFatDispersedPasteState
  | simmerMole : MoleStep hotFatDispersedPasteState serviceStableMoleState

/-- Reflexive-transitive closure of the repaired step relation. -/
inductive MoleRoute : CandidateMoleState → CandidateMoleState → Prop
  | stop {s : CandidateMoleState} : MoleRoute s s
  | step {a b c : CandidateMoleState} : MoleStep a b → MoleRoute b c → MoleRoute a c

namespace MoleRoute

theorem single {a b : CandidateMoleState} (h : MoleStep a b) : MoleRoute a b := .step h .stop

theorem trans {a b c : CandidateMoleState} (h₁ : MoleRoute a b) (h₂ : MoleRoute b c) :
    MoleRoute a c := by
  induction h₁ with
  | stop => exact h₂
  | step e _ ih => exact .step e (ih h₂)

end MoleRoute

/-! ### The two supplied chile routes still exist -/

theorem fryThenRehydrateRoute : MoleRoute rawChileState friedThenRehydratedChileState :=
  .step .fryRawChile (.single .rehydrateFriedChile)

theorem rehydrateThenFryRoute : MoleRoute rawChileState rehydratedThenFriedChileState :=
  .step .rehydrateRawChile (.single .fryRehydratedChile)

theorem canonicalAshRoute : MoleRoute rawSeedState washedAshState :=
  .step .carboniseSeeds (.single .washCarbonisedSeeds)

theorem canonicalCandidateMoleRoute :
    MoleRoute rawComponentAssemblyState serviceStableMoleState :=
  .step .prepareAssembly (.step .grindAssembly (.step .dispersePaste (.single .simmerMole)))

/-! ### ... and now order-sensitivity is a theorem -/

/-- The fry-then-rehydrate endpoint is terminal. -/
theorem friedThenRehydrated_terminal (b : CandidateMoleState) :
    ¬ MoleStep friedThenRehydratedChileState b := by rintro ⟨⟩

/-- The rehydrate-then-fry endpoint is terminal. -/
theorem rehydratedThenFried_terminal (b : CandidateMoleState) :
    ¬ MoleStep rehydratedThenFriedChileState b := by rintro ⟨⟩

/-- A route out of a terminal state is trivial. -/
theorem eq_of_route_from_terminal {a b : CandidateMoleState}
    (hterm : ∀ c, ¬ MoleStep a c) (h : MoleRoute a b) : a = b := by
  cases h with
  | stop => rfl
  | step e _ => exact absurd e (hterm _)

/-- **Order-sensitivity, repaired and proved.**  In the repaired route system
the two cooking orders end at mutually unreachable states: frying then
rehydrating cannot be continued into the rehydrate-then-fry product, nor
conversely.  This is the statement the Agda `OrderSensitiveRouteWitness` is
trying to record. -/
theorem orders_are_unmergeable :
    ¬ MoleRoute friedThenRehydratedChileState rehydratedThenFriedChileState ∧
      ¬ MoleRoute rehydratedThenFriedChileState friedThenRehydratedChileState := by
  constructor
  · intro h
    exact absurd (eq_of_route_from_terminal friedThenRehydrated_terminal h) (by decide)
  · intro h
    exact absurd (eq_of_route_from_terminal rehydratedThenFried_terminal h) (by decide)

/-- Lane index: chile lane `0`, seed/ash lane `1`, assembly lane `2`. -/
def moleLane : CandidateMoleState → ℕ
  | rawChileState | friedChileState | rehydratedChileState
  | friedThenRehydratedChileState | rehydratedThenFriedChileState => 0
  | rawSeedState | carbonisedSeedState | washedAshState => 1
  | rawComponentAssemblyState | differentiallyPreparedAssemblyState
  | groundPasteState | hotFatDispersedPasteState | serviceStableMoleState => 2

theorem moleLane_step {a b : CandidateMoleState} (e : MoleStep a b) :
    moleLane a = moleLane b := by cases e <;> rfl

theorem moleLane_route {a b : CandidateMoleState} (h : MoleRoute a b) :
    moleLane a = moleLane b := by
  induction h with
  | stop => rfl
  | step e _ ih => exact (moleLane_step e).trans ih

/-- The repaired relation is genuinely partial: the ash lane and the chile lane
do not communicate. -/
theorem no_route_chile_to_ash : ¬ MoleRoute rawChileState washedAshState := fun h =>
  absurd (moleLane_route h) (by decide)

/-- Progress depth along the supplied steps. -/
def moleDepth : CandidateMoleState → ℕ
  | rawChileState => 0
  | friedChileState => 1
  | rehydratedChileState => 1
  | friedThenRehydratedChileState => 2
  | rehydratedThenFriedChileState => 2
  | rawSeedState => 0
  | carbonisedSeedState => 1
  | washedAshState => 2
  | rawComponentAssemblyState => 0
  | differentiallyPreparedAssemblyState => 1
  | groundPasteState => 2
  | hotFatDispersedPasteState => 3
  | serviceStableMoleState => 4

theorem moleDepth_step {a b : CandidateMoleState} (e : MoleStep a b) :
    moleDepth a < moleDepth b := by cases e <;> decide

theorem moleDepth_route {a b : CandidateMoleState} (h : MoleRoute a b) :
    moleDepth a ≤ moleDepth b := by
  induction h with
  | stop => exact le_rfl
  | step e _ ih => exact le_trans (le_of_lt (moleDepth_step e)) ih

theorem moleRoute_eq_or_depth_lt {a b : CandidateMoleState} (h : MoleRoute a b) :
    a = b ∨ moleDepth a < moleDepth b := by
  cases h with
  | stop => exact Or.inl rfl
  | step e p => exact Or.inr (lt_of_lt_of_le (moleDepth_step e) (moleDepth_route p))

/-- The repaired relation is acyclic: no state is reachable from itself by a
nonempty route. -/
theorem moleRoute_antisymm {a b : CandidateMoleState}
    (h₁ : MoleRoute a b) (h₂ : MoleRoute b a) : a = b := by
  rcases moleRoute_eq_or_depth_lt h₁ with h | h
  · exact h
  · rcases moleRoute_eq_or_depth_lt h₂ with h' | h'
    · exact h'.symm
    · omega

end Cuisine.ProcessRoute
