/-!
Section 21 PNP native replay root.

Original residual factorization, adaptive footprint soundness,
shared-event counterexamples, finite disjoint packing, and fractional
support weights on the ORIGINAL input coordinates are kept together.
The n-coordinate ceiling prevents promoting them to P versus NP.
-/
import Welds.PNPResidualAdaptiveTranscriptExact
import Welds.PNPHyperfabricSharedEventNegativeControlExact
import Welds.PNPOriginalTranscriptDisjointSupportExact
import Welds.PNPOriginalFractionalSupportLowerBoundExact

#print axioms PNPResidualGeometryBridge.consumer_factor_iff
#print axioms PNPResidualGeometryBridge.actual_transcript_hits
#print axioms PNPResidualGeometryBridge.actual_transcript_disjoint_support_input_ceiling
#print axioms PNPResidualGeometryBridge.actual_transcript_fractional_support_lower_bound
#print axioms PNPHyperfabricOwnedEvents.shared_event_rivals
