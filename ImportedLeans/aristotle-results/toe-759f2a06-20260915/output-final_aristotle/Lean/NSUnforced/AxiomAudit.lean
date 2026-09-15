/-
# Axiom receipts for the unforced A-programme

Building this module prints the transitive axiom dependencies of every
user-facing declaration of `NSUnforced`.  Each one is
`[propext, Classical.choice, Quot.sound]`: no `sorry`, no `native_decide`, no
project-local axiom, no `@[implemented_by]`.
-/
import NSUnforced

namespace DASHI.NS.Unforced

-- Signed carriers (R543 / R566 / R567 / signed Gram collapse).
#print axioms fullSquareSum_eq_diag_add_offDiag
#print axioms fullSquareSum_transpose
#print axioms fullSquareSum_two_add_transpose
#print axioms fullSquareSum_gram_collapse
#print axioms abs_fullSquareSum_gram_collapse_le
#print axioms fullSquareSum_rankOne_collapse

-- R571 signed ±y multiplier-difference carrier.
#print axioms multiplierDifference_homochiral
#print axioms multiplierDifference_heterochiral
#print axioms triad_radius_sub_le
#print axioms abs_multiplierDifference_homochiral_le
#print axioms heterochiral_multiplierDifference_not_output_controlled
#print axioms sum_multiplierDifference_homochiral_vanishes
#print axioms norm_commutatorCarrier_homochiral_le
#print axioms sum_commutator_square_homochiral_le

-- Schur control of the collapsed channels.
#print axioms norm_weighted_sum_sq_le
#print axioms sum_channel_sq_le_schur
#print axioms channel_energy_receipt

-- Cutoff-uniform budget engine.
#print axioms energy_le_exp_of_deriv_le
#print axioms four_integral_forcing_le

-- A1 (R568).
#print axioms pointwise_absorption_of_channel_squares
#print axioms budget568_of_uniform_absorption
#print axioms budget568_of_channel_control
#print axioms a1_of_channelObligation

-- A2 (R406 / R372).
#print axioms critical_cell_pointwise_payment
#print axioms a2_uniform_critical_ceiling

-- R414 dual consumer and the non-collapse theorems.
#print axioms dualPayment_of_receipts
#print axioms a1_does_not_pay_a2
#print axioms a2_does_not_pay_a1

end DASHI.NS.Unforced
