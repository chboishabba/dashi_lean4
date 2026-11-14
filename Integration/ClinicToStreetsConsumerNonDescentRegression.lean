import Integration.ScopedVerifierConsumerSufficiency
import Integration.ClinicToStreetsConsumerNonDescent

namespace Integration.ClinicToStreetsConsumerNonDescentRegression

open Integration.ClinicToStreetsConsumerNonDescent
namespace Generic := Integration.ScopedVerifierConsumerSufficiency

example : Generic.ConsumerNonDescentWitness atomisingObserver structuralConsumer :=
  canonicalAtomisingWitness

example : ¬ Generic.ConsumerFactorization atomisingObserver structuralConsumer :=
  atomisingObserverBlocksStructuralFactorisation

example : Generic.ConsumerFactorization repairedObserver structuralConsumer :=
  structuralResidualRepairsAtomisation

example :
    ∀ {Refinement : Type} {refine : CausalWorld → Refinement},
      Generic.ConsumerFactorization
        (fun world => (atomisingObserver world, refine world))
        structuralConsumer →
      refine fullStructuralWorld ≠ refine sameSurfaceWithoutStructuralWorld :=
  anySufficientRepairSeparatesCanonicalCollision

example : Generic.ConsumerFactorization contextObserver structuralConsumer :=
  contextObserverFactorsStructuralConsumer

example : canonicalBoundary.reusesGenericConsumerSufficiency = true := by
  rfl

example : canonicalBoundary.reimplementsGenericFactorization = false := by
  rfl

example : canonicalBoundary.finiteCollisionEstablishesEmpiricalCausality = false := by
  rfl

end Integration.ClinicToStreetsConsumerNonDescentRegression
