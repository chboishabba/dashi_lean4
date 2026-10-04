import Integration.OggSSP2BTateGradingConventionBridge

/-!
# Weight-two 2B Tate Brauer-trace bridge

The class-fusion B' screen needs one precise source seam.

Borcherds--Ryba / Urano's Tate trace identity for a central element g of prime
order p and a p-regular commuting element h is

  BrauerTr(h | Hhat0(g,A)) - BrauerTr(h | Hhat1(g,A)) = Tr(g h | A).

For the 2B Moonshine weight-two piece, the existing grading/vanishing source
has Hhat1 = 0.  Therefore at this one degree the ordinary Monster trace of g*h
is exactly the Brauer trace on the 276-dimensional Hhat0 head.

This is the source justification for the GAP screen
`twob_tate276_m24_brauer_character_screen.g`.  It deliberately avoids relying
on competing printed sign conventions for the full generating-series
Hhat0/Hhat1 split: the supertrace identity plus weight-two Hhat1-vanishing is
enough.
-/

namespace Integration.OggSSP2BTateWeightTwoBrauerTraceBridge

namespace T := Integration.OggSSP2BActualRestrictedTate
namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities

/-- The source-level algebraic compiler: if the Tate super-Brauer trace is the
ordinary g*h trace and Hhat1 vanishes, then the Hhat0 Brauer trace is exactly
the ordinary g*h trace. -/
theorem hhat0_trace_eq_gh_trace_of_supertrace_and_hhat1_zero
    {h0 h1 gh : ℤ}
    (supertrace : h0 - h1 = gh)
    (hhat1Zero : h1 = 0) :
    h0 = gh := by
  omega

/-- The repo's source owner has the required weight-two Hhat1 vanishing. -/
theorem weight_two_hhat1_length_zero :
    T.gradeH1Length M.weightTwo = 0 :=
  T.weight_two_ordinary_tate_lengths.2

/-- Contract used by a concrete p-regular class calculation.  `brauerH0`,
`brauerH1`, and `monsterGhTrace` are the three integer character values for
one fixed odd-order h. -/
structure WeightTwoClassTraceReceipt where
  brauerH0 : ℤ
  brauerH1 : ℤ
  monsterGhTrace : ℤ
  supertraceIdentity : brauerH0 - brauerH1 = monsterGhTrace
  hhat1Vanishing : brauerH1 = 0

namespace WeightTwoClassTraceReceipt

theorem h0_eq_monster_gh_trace (r : WeightTwoClassTraceReceipt) :
    r.brauerH0 = r.monsterGhTrace :=
  hhat0_trace_eq_gh_trace_of_supertrace_and_hhat1_zero
    r.supertraceIdentity r.hhat1Vanishing

end WeightTwoClassTraceReceipt

/-- Semantic boundary: the bridge identifies character values at weight two;
it does not by itself construct an M24 module isomorphism or the M22:2 outer
action on a selected ten-dimensional quotient. -/
inductive WeightTwoTraceEqualityConstructsSameObjectModule : Prop

theorem trace_equality_does_not_construct_same_object_module :
    ¬ WeightTwoTraceEqualityConstructsSameObjectModule := by
  intro h
  cases h

end Integration.OggSSP2BTateWeightTwoBrauerTraceBridge
