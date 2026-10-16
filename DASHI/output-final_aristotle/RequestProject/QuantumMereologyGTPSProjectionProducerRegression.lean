import RequestProject.QuantumMereologyGTPSProjectionProducer

namespace QuantumMereology
namespace GTPSProjectionProducerRegression

example :
    GTPSProjectionProducer.canonicalBoundary.localPlusCommutantProjectorProduced = true :=
  GTPSProjectionProducer.local_plus_commutant_projector_produced

example :
    GTPSProjectionProducer.canonicalBoundary.algebraProjectorProduced = true :=
  GTPSProjectionProducer.algebra_projector_produced

example :
    GTPSProjectionProducer.canonicalBoundary.finiteSourceGTPSShortTimeScoreFullyInstantiated = true :=
  GTPSProjectionProducer.finite_source_gtps_short_time_score_fully_instantiated

example :
    GTPSProjectionProducer.canonicalBoundary.physicalSourceGTPSAutomaticallyIdentified = false :=
  GTPSProjectionProducer.physical_source_gtps_not_automatic

end GTPSProjectionProducerRegression
end QuantumMereology
