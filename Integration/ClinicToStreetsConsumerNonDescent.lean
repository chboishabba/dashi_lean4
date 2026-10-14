import Integration.ClinicToStreetsCausalProvenanceMaxCut
import Integration.ScopedVerifierConsumerSufficiency

/-!
# Clinic-to-Streets thin consumer-sufficiency adapter

The generic non-descent/factorisation/refinement machinery is already owned by
`Integration.ScopedVerifierConsumerSufficiency`.  This file does not define a
second `ConsumerSufficient`, `FactorsThrough`, or repair calculus.  It supplies
only the Clinic-specific finite causal worlds and instantiates the generic
owner on the atomising structural-provenance collision.
-/

namespace Integration.ClinicToStreetsConsumerNonDescent

namespace Generic := Integration.ScopedVerifierConsumerSufficiency

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

theorem atomised_surface_collision :
    atomisingObserver fullStructuralWorld =
      atomisingObserver sameSurfaceWithoutStructuralWorld := by
  rfl

theorem structural_consumer_separates_collision :
    structuralConsumer fullStructuralWorld ≠
      structuralConsumer sameSurfaceWithoutStructuralWorld := by
  decide

def canonicalAtomisingWitness :
    Generic.ConsumerNonDescentWitness atomisingObserver structuralConsumer :=
  ⟨fullStructuralWorld,
   sameSurfaceWithoutStructuralWorld,
   atomised_surface_collision,
   structural_consumer_separates_collision⟩

theorem atomisingObserverBlocksStructuralFactorisation :
    ¬ Generic.ConsumerFactorization atomisingObserver structuralConsumer :=
  Generic.collisionBlocksFactorization canonicalAtomisingWitness

/-! Exact residual repair using the existing generic factorisation carrier. -/

def structuralResidual (world : CausalWorld) : Bool :=
  world.structuralCoordinate

def repairedObserver (world : CausalWorld) : (Bool × Bool) × Bool :=
  (atomisingObserver world, structuralResidual world)

def structuralResidualRepairsAtomisation :
    Generic.ConsumerFactorization repairedObserver structuralConsumer where
  decode observed := observed.2
  factorizes _ := rfl

theorem anySufficientRepairSeparatesCanonicalCollision :
    ∀ {Refinement : Type} {refine : CausalWorld → Refinement},
      Generic.ConsumerFactorization
        (fun world => (atomisingObserver world, refine world))
        structuralConsumer →
      refine fullStructuralWorld ≠ refine sameSurfaceWithoutStructuralWorld := by
  intro Refinement refine factorization sameRefinement
  apply structural_consumer_separates_collision
  calc
    structuralConsumer fullStructuralWorld =
        factorization.decode (atomisingObserver fullStructuralWorld, refine fullStructuralWorld) :=
      (factorization.factorizes fullStructuralWorld).symm
    _ = factorization.decode (atomisingObserver sameSurfaceWithoutStructuralWorld,
        refine sameSurfaceWithoutStructuralWorld) := by
      rw [atomised_surface_collision, sameRefinement]
    _ = structuralConsumer sameSurfaceWithoutStructuralWorld :=
      factorization.factorizes sameSurfaceWithoutStructuralWorld

def contextObserver (world : CausalWorld) : CausalWorld := world

def contextObserverFactorsStructuralConsumer :
    Generic.ConsumerFactorization contextObserver structuralConsumer where
  decode world := world.structuralCoordinate
  factorizes _ := rfl

structure Boundary where
  reusesGenericConsumerSufficiency : Bool
  reimplementsGenericFactorization : Bool
  atomisedStructuralNonDescentPaid : Bool
  structuralResidualRepairPaid : Bool
  everySufficientRepairSeparatesCanonicalCollision : Bool
  oneCollisionSeparationProvesGlobalConsumerSufficiency : Bool
  oneConsumerDefinesWorldCompleteness : Bool
  finiteCollisionEstablishesEmpiricalCausality : Bool
  nonDescentEstablishesDeliberateIntent : Bool
  deriving Repr

def canonicalBoundary : Boundary :=
  ⟨true, false, true, true, true, false, false, false, false⟩

end Integration.ClinicToStreetsConsumerNonDescent
