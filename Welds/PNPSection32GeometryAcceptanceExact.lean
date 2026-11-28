import Welds.PNPOriginalHallSupportExact
import Welds.PNPFiniteCodePrefixExact
import Welds.PNPFrontierResolutionExact
import Welds.PNPLiveMassPartitionExact

/-! Written import/check root. No kernel acceptance claimed. -/
#check PNPOriginalHallSupport.hall_defect
#check PNPOriginalHallSupport.forced_edge_absent
#check PNPOriginalHallSupport.retire_sound
#check PNPFiniteCodePrefix.compiled_prefix_no_gain
#check PNPFixedSourceGain.missed_source_gain
#check PNPFrontierResolution.puncture_receipt_unique
#check PNPLiveMassPartition.clippedSuccessorCard

#print axioms PNPOriginalHallSupport.forced_edge_absent
#print axioms PNPFiniteCodePrefix.compiled_prefix_no_gain
#print axioms PNPFixedSourceGain.missed_source_gain
#print axioms PNPFrontierResolution.puncture_receipt_unique
