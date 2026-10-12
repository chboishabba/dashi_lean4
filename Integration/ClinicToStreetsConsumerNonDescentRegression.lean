import Integration.ClinicToStreetsConsumerNonDescent

namespace Integration.ClinicToStreetsConsumerNonDescentRegression

open Integration.ClinicToStreetsConsumerNonDescent

example : atomisingObserver fullStructuralWorld = atomisingObserver sameSurfaceWithoutStructuralWorld := by
  rfl

example : structuralConsumer fullStructuralWorld ≠ structuralConsumer sameSurfaceWithoutStructuralWorld := by
  decide

example : ¬ ConsumerSufficient atomisingObserver structuralConsumer :=
  atomisingObserverBlocksStructuralSufficiency

example : ¬ FactorsThrough atomisingObserver structuralConsumer :=
  atomisingObserverBlocksStructuralFactorisation

example : ConsumerSufficient contextObserver structuralConsumer :=
  contextObserverIsStructurallySufficient

example : canonicalBoundary.finiteCollisionEstablishesEmpiricalCausality = false := by
  rfl

end Integration.ClinicToStreetsConsumerNonDescentRegression
