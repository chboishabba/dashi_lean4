import MillenniumExternal.COMMIT_PIN
import MillenniumExternal.TerminalCensus
import MillenniumExternal.ExternalTargetFrontier
import MillenniumExternal.SameObjectMaxCut
import MillenniumExternal.CompletionMaxCut
import MillenniumExternal.ProofResolutionMaxCut
import Synthesis.MillenniumBSDProjectiveRankWeld

/-!
Aggregate root for the external Millennium acceptance/audit layer.

`SameObjectMaxCut` prevents already-paid literal/same-object/physical-object
welds from being reopened. `CompletionMaxCut` names the post-identity producer
leaves from the base acceptance branch, while `ProofResolutionMaxCut` imposes
the current submission-pass rule: P≠NP, RH, Navier--Stokes and BSD are searched
and composed as already-proved lanes and may not acquire replacement
mathematical hypotheses here.
-/

#print axioms Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#print axioms Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#print axioms Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#print axioms Synthesis.Millennium.BSD.projective_rank_carrier_paid
#print axioms NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame
#print axioms Synthesis.Millennium.Hodge.doublePointCycle_isWeilDivisor
#print axioms RequestProject.YangMills.probabilityCovariance_exponential_bound_of_weak_limit

#check MillenniumExternal.no_faithful_resolution_lane_permits_new_mathematics
#check MillenniumExternal.navierStokes_source_term_is_resolved
#check MillenniumExternal.pnp_rh_bsd_still_require_donor_resolution
#check MillenniumExternal.resolution_board_agrees_with_same_object_cut
