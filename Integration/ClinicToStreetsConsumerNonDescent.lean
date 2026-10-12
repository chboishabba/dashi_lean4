import Integration.ClinicToStreetsCausalProvenanceMaxCut

/-!
# Clinic-to-Streets consumer-relative non-descent

This is the Lean mirror of the Agda consumer-descent cross-pollination.
The earlier Clinic max-cut shows that atomisation can hide structural provenance.
Here that statement is sharpened to a consumer-relative information-loss theorem:
if a declared consumer needs the structural coordinate, the atomised observer is
not sufficient for that consumer and the consumer cannot factor through it.

The finite witness is structural only. It is not empirical evidence that any
therapy, institution, narrative, or population realises these worlds.
-/

namespace Integration.ClinicToStreetsConsumerNonDescent

structure CausalWorld where
  structuralCoordinate : Bool
  intimateCoordinate : Bool
  intrapsychicCoordinate : Bool
  deriving DecidableEq, Repr

def fullStructuralWorld : CausalWorld := ⟨true, true, true⟩
def sameSurfaceWithoutStructuralWorld : CausalWorld := ⟨false, true, true⟩

def atomisingObserver (world : CausalWorld) : Bool × Bool :=
  (world.intimateCoordinate, world.intrapsychicCoordinate)

def structuralConsumer (world : CausalWorld) : Bool :=
  world.structuralCoordinate

def ConsumerSufficient {State Surface Outcome : Type}
    (observe : State → Surface) (consumer : State → Outcome) : Prop :=
  ∀ left right, observe left = observe right → consumer left = consumer right

def FactorsThrough {State Surface Outcome : Type}
    (observe : State → Surface) (consumer : State → Outcome) : Prop :=
  ∃ factor : Surface → Outcome, ∀ state, factor (observe state) = consumer state

theorem atomised_surface_collision :
    atomisingObserver fullStructuralWorld =
      atomisingObserver sameSurfaceWithoutStructuralWorld := by
  rfl

theorem structural_consumer_separates_collision :
    structuralConsumer fullStructuralWorld ≠
      structuralConsumer sameSurfaceWithoutStructuralWorld := by
  decide

theorem atomisingObserverBlocksStructuralSufficiency :
    ¬ ConsumerSufficient atomisingObserver structuralConsumer := by
  intro sufficient
  have h := sufficient
    fullStructuralWorld
    sameSurfaceWithoutStructuralWorld
    atomised_surface_collision
  exact structural_consumer_separates_collision h

theorem atomisingObserverBlocksStructuralFactorisation :
    ¬ FactorsThrough atomisingObserver structuralConsumer := by
  rintro ⟨factor, hf⟩
  have h :
      structuralConsumer fullStructuralWorld =
        structuralConsumer sameSurfaceWithoutStructuralWorld := by
    calc
      structuralConsumer fullStructuralWorld =
          factor (atomisingObserver fullStructuralWorld) :=
        (hf fullStructuralWorld).symm
      _ = factor (atomisingObserver sameSurfaceWithoutStructuralWorld) := by
        rw [atomised_surface_collision]
      _ = structuralConsumer sameSurfaceWithoutStructuralWorld :=
        hf sameSurfaceWithoutStructuralWorld
  exact structural_consumer_separates_collision h

def contextObserver (world : CausalWorld) : CausalWorld := world

theorem contextObserverIsStructurallySufficient :
    ConsumerSufficient contextObserver structuralConsumer := by
  intro left right same
  cases same
  rfl

structure Boundary where
  atomisedStructuralNonDescentPaid : Bool
  fullContextStructuralSufficiencyPaid : Bool
  oneConsumerDefinesWorldCompleteness : Bool
  finiteCollisionEstablishesEmpiricalCausality : Bool
  nonDescentEstablishesDeliberateIntent : Bool
  deriving Repr

def canonicalBoundary : Boundary :=
  ⟨true, true, false, false, false⟩

end Integration.ClinicToStreetsConsumerNonDescent
