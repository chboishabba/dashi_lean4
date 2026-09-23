import Integration.RiemannSmoothNormalizedWindow
import Integration.RiemannPoleQuotientAdaptiveSelection
import Integration.RiemannPoleQuotientReduction

/-!
# Axiom audit for the pole–quotient reduction lane

Every line must report only a subset of
`{propext, Classical.choice, Quot.sound}`.  In particular no declaration of this
lane depends on a postulated analytic input: the manuscript's unproved analytic
content appears only as *hypotheses* of the reduction theorems
(`LowRegionVerified`, `HighOrdinateContradiction`, `PoleQuotientRealization`),
never as an axiom.
-/

/-! ### Integration.RiemannSmoothNormalizedWindow (Lemma 3.1) -/

#print axioms Integration.RiemannPoleQuotient.stdBumpProfile
#print axioms Integration.RiemannPoleQuotient.window_even
#print axioms Integration.RiemannPoleQuotient.window_nonneg
#print axioms Integration.RiemannPoleQuotient.window_contDiff
#print axioms Integration.RiemannPoleQuotient.window_hasCompactSupport
#print axioms Integration.RiemannPoleQuotient.window_support
#print axioms Integration.RiemannPoleQuotient.window_integral_eq_one
#print axioms Integration.RiemannPoleQuotient.window_pos_at_centre
#print axioms Integration.RiemannPoleQuotient.windowMass_pos
#print axioms Integration.RiemannPoleQuotient.smooth_normalized_window
#print axioms Integration.RiemannPoleQuotient.window_support_lt_log_two

/-! ### Integration.RiemannAdaptiveCutoffCrossingCompatibility (Lemma 5.1) -/

#print axioms Integration.RiemannPoleQuotient.eventually_quarter_period_crossing
#print axioms Integration.RiemannPoleQuotient.eventually_far_tail_small
#print axioms Integration.RiemannPoleQuotient.adaptive_cutoff_eventually
#print axioms Integration.RiemannPoleQuotient.adaptive_cutoff_compatible

/-! ### Integration.RiemannPoleQuotientTerminal (Theorem 8.1, Proposition 6.3) -/

#print axioms Integration.RiemannPoleQuotient.terminal_contradiction
#print axioms Integration.RiemannPoleQuotient.strictHigh_of_certificate
#print axioms Integration.RiemannPoleQuotient.terminal_contradiction_of_certificate
#print axioms Integration.RiemannPoleQuotient.balance_and_split_consistent

/-! ### Integration.RiemannPoleQuotientAdaptiveSelection (§7) -/

#print axioms Integration.RiemannPoleQuotient.exists_cutoff_strictHigh
#print axioms Integration.RiemannPoleQuotient.no_response_family_with_margin

/-! ### Integration.RiemannPoleQuotientReduction (Theorem 9.1) -/

#print axioms Integration.RiemannPoleQuotient.zeta_eq_zero_iff_completed
#print axioms Integration.RiemannPoleQuotient.zeta_zero_one_sub
#print axioms Integration.RiemannPoleQuotient.re_lt_one_of_zeta_eq_zero
#print axioms Integration.RiemannPoleQuotient.re_pos_of_zeta_eq_zero
#print axioms Integration.RiemannPoleQuotient.highOrdinateContradiction_of_realization
#print axioms Integration.RiemannPoleQuotient.riemannHypothesis_of_low_and_high
#print axioms Integration.RiemannPoleQuotient.riemannHypothesis_of_low_and_poleQuotient
