import Synthesis.MillenniumBSDSameCurveSelmerDefectExact

/-!
# BSD Clay core = zero same-curve Selmer defect, conditional on the analytic bridge

No new rank carrier is introduced here.

`UniversalSelmerDefectAnalyticBridge` already names the genuinely independent
analytic comparison work between the same-curve Selmer rank and the canonical
analytic rank.  Conditional on that bridge, the remaining arithmetic statement
is exactly zero defect:

  BSDClayCoreObligation bg
    <-> UniversalSelmerDefectZero bg bridge.arithmetic.

Thus a Selmer route cannot hide the reverse BSD inequality inside a generic
`selmer <= MW` premise.  On the existing same-curve decomposition that premise
is literally the zero-defect theorem.
-/

namespace Synthesis.Millennium.BSD

/-- Under an independently proved same-curve Selmer/analytic bridge, BSD implies
that the arithmetic defect vanishes on every literal rational elliptic curve. -/
theorem universalSelmerDefectZero_of_bsdClayCore
    (bg : BSDEstablishedBackground)
    (bridge : UniversalSelmerDefectAnalyticBridge bg)
    (hBSD : BSDClayCoreObligation bg) :
    UniversalSelmerDefectZero bg bridge.arithmetic := by
  intro E
  have hRank : bg.analytic.rank E = bg.algebraic.rank E :=
    hBSD E (Set.mem_univ E)
  have hSelmerLeMW :
      bridge.arithmetic.selmerRank E <= bg.algebraic.rank E := by
    exact (bridge.selmer_le_analytic E).trans_eq hRank
  exact
    (bridge.arithmetic.selmer_le_mordellWeil_iff_defect_zero E).1
      hSelmerLeMW

/-- Exact max-cut equivalence for the Selmer route.  The analytic bridge is not
proved here and is not counted as arithmetic progress. -/
theorem bsdClayCore_iff_universalSelmerDefectZero
    (bg : BSDEstablishedBackground)
    (bridge : UniversalSelmerDefectAnalyticBridge bg) :
    BSDClayCoreObligation bg
      <-> UniversalSelmerDefectZero bg bridge.arithmetic := by
  constructor
  · exact universalSelmerDefectZero_of_bsdClayCore bg bridge
  · exact bsdClayCore_of_selmerDefectBridge_and_zero bg bridge

end Synthesis.Millennium.BSD
