/-
# Axiom audit for the 2026-09-15 tranche work (lane B)

Building this module prints the transitive axiom dependencies of every headline
theorem added in this session.  Each must report exactly
`[propext, Classical.choice, Quot.sound]`: no `sorry`, no `native_decide`, no
project-local axiom, no `@[implemented_by]`.

This audits only the *new* material.  The imported TOE `NSUnforced` library has
its own audit module, `NSUnforced.AxiomAudit`, which is on the build surface and
is checked here too.
-/
import RequestProject.NavierStokes.R571PairedSecondMoment
import RequestProject.NavierStokes.HeterochiralOutputGain
import RequestProject.NavierStokes.ProofDebtRouterMirror

-- R571 Gate-A radial leaves (A1, A2)
#print axioms RequestProject.NavierStokes.R571.norm_second_difference_nonneg
#print axioms RequestProject.NavierStokes.R571.norm_second_difference_le
#print axioms RequestProject.NavierStokes.R571.abs_radialIncrement_le
#print axioms RequestProject.NavierStokes.R571.abs_centeredRadialDefect_le
#print axioms RequestProject.NavierStokes.R571.abs_centeredRadialDefect_le_of_one_le_norm
#print axioms RequestProject.NavierStokes.R571.centeredRadialDefect_bound_is_order_sharp
#print axioms RequestProject.NavierStokes.R571.centeredRadialDefect_ne_zero

-- Paired second moment on the real carrier
#print axioms RequestProject.NavierStokes.R571.paired_commutator_identity
#print axioms RequestProject.NavierStokes.R571.finite_weighted_paired_commutator_identity
#print axioms RequestProject.NavierStokes.R571.paired_second_moment_pointwise
#print axioms RequestProject.NavierStokes.R571.r571_pairedSecondMoment_of_stateEnvelope
#print axioms RequestProject.NavierStokes.R571.r571_finite_pairedSecondMoment_of_stateEnvelope
#print axioms RequestProject.NavierStokes.R571.r571_pairedSecondMoment_nonvacuous

-- Heterochiral output gain
#print axioms RequestProject.NavierStokes.Heterochiral.heterochiral_radialSum_mul_defect_le
#print axioms RequestProject.NavierStokes.Heterochiral.cross_helical_same_axis_eq_zero
#print axioms RequestProject.NavierStokes.Heterochiral.cross_helical_antiparallel_eq_zero
#print axioms RequestProject.NavierStokes.Heterochiral.nrm_cross_helical_le
#print axioms RequestProject.NavierStokes.Heterochiral.heterochiral_vertex_output_controlled
#print axioms RequestProject.NavierStokes.Heterochiral.sum_heterochiral_square_le
#print axioms RequestProject.NavierStokes.Heterochiral.exists_unit_helical_vector

-- Proof-debt router mirror
#print axioms RequestProject.NavierStokes.ProofDebtRouter.no_receipt_to_theorem
#print axioms RequestProject.NavierStokes.ProofDebtRouter.novelOpen_always_researched
#print axioms RequestProject.NavierStokes.ProofDebtRouter.mathematicalDebt_never_delegated
