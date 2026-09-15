/-
# Axiom audit for the `master-20dd / lean-7f60` tranche work (lane B control cut)

Building this module prints the transitive axiom dependencies of every headline
theorem added in this round.  Each must report exactly
`[propext, Classical.choice, Quot.sound]`: no `sorry`, no `native_decide`, no
project-local axiom, no `@[implemented_by]`.
-/
import RequestProject.NavierStokes.CriticalWeightDifferenceTransfer
import RequestProject.NavierStokes.CriticalProductionWitness

-- Dyadic weight geometry: the two `DyadicShellBounds` fields, the triad transfer
-- bound, the `ℓ¹` no-go, and the commutator no-go.
#print axioms ClayNS.Waleffe.waveMaxCoord_le_critWeight
#print axioms ClayNS.Waleffe.critWeight_le_two_mul
#print axioms ClayNS.Waleffe.critWeight_add_le
#print axioms ClayNS.Waleffe.exists_sum_inv_critWeight_ge
#print axioms ClayNS.Waleffe.no_highlow_commutator_gain

-- S1a / S1b / S2a on the literal Galerkin carrier.
#print axioms ClayNS.Waleffe.GalerkinFlow.critProduction_pairing_symm
#print axioms ClayNS.Waleffe.GalerkinFlow.critProductionRate_eq_output_pairing
#print axioms ClayNS.Waleffe.GalerkinFlow.critEnergy_hasDerivAt
#print axioms ClayNS.Waleffe.GalerkinFlow.critEnergy_balance

-- S2b: the target's consumer, the homogeneity of the folds, and the no-go.
#print axioms ClayNS.Waleffe.retained_viscosity_budget
#print axioms ClayNS.Waleffe.critEnergyOf_scale
#print axioms ClayNS.Waleffe.critDissipationOf_scale
#print axioms ClayNS.Waleffe.critProductionOf_scale
#print axioms ClayNS.Waleffe.no_subcubic_remainder_absorption

-- The explicit witness state.
#print axioms ClayNS.Waleffe.witField_support
#print axioms ClayNS.Waleffe.witField_transverse
#print axioms ClayNS.Waleffe.witField_reality
#print axioms ClayNS.Waleffe.critProductionOf_witField
#print axioms ClayNS.Waleffe.witField_unweighted_neutral
#print axioms ClayNS.Waleffe.no_subcubic_remainder_absorption_wit

-- Cancellation-preserving structure of the production.
#print axioms ClayNS.Waleffe.weighted_production_eq_weightDifference
#print axioms ClayNS.Waleffe.weighted_production_const_eq_zero
#print axioms ClayNS.Waleffe.critProductionOf_eq_weightDifference
#print axioms ClayNS.Waleffe.critProductionOf_eq_shellJump_sum
