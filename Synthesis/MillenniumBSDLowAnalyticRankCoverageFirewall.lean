import Synthesis.MillenniumBSDUniversalRankInequalityMechanisms

/-!
# BSD low-analytic-rank coverage firewall

Gross--Zagier/Kolyvagin-type input is genuinely strong on the subdomain where
the canonical analytic rank is at most one.  It can close BOTH directional
rank inequalities there.

That does not make it a universal BSD mechanism.

This owner makes the missing promotion theorem explicit: a low-rank mechanism
reaches the frozen Clay endpoint only after a separate proof that every literal
rational elliptic curve lies in the low-analytic-rank domain.

No such coverage theorem is asserted here.
-/

namespace Synthesis.Millennium.BSD

def AnalyticRankAtMostOne
    (bg : BSDEstablishedBackground)
    (E : RationalEllipticCurve) : Prop :=
  bg.analytic.rank E ≤ 1

/-- Exact rank equality on the established low-analytic-rank domain. -/
def LowAnalyticRankEqualityMechanism
    (bg : BSDEstablishedBackground) : Prop :=
  ∀ E : RationalEllipticCurve,
    AnalyticRankAtMostOne bg E →
    bg.analytic.rank E = bg.algebraic.rank E

theorem lowerRankBound_on_lowAnalyticRank
    (bg : BSDEstablishedBackground)
    (h : LowAnalyticRankEqualityMechanism bg)
    (E : RationalEllipticCurve)
    (hE : AnalyticRankAtMostOne bg E) :
    bg.algebraic.rank E ≤ bg.analytic.rank E := by
  exact Nat.le_of_eq (h E hE).symm

theorem upperRankBound_on_lowAnalyticRank
    (bg : BSDEstablishedBackground)
    (h : LowAnalyticRankEqualityMechanism bg)
    (E : RationalEllipticCurve)
    (hE : AnalyticRankAtMostOne bg E) :
    bg.analytic.rank E ≤ bg.algebraic.rank E := by
  exact Nat.le_of_eq (h E hE)

/-- The exact extra theorem needed to promote a low-rank result to universal
BSD: every curve must belong to the low-analytic-rank domain. -/
def UniversalLowAnalyticRankCoverage
    (bg : BSDEstablishedBackground) : Prop :=
  ∀ E : RationalEllipticCurve,
    AnalyticRankAtMostOne bg E

theorem bsdClayCore_of_lowRankMechanism_and_universalCoverage
    (bg : BSDEstablishedBackground)
    (hLow : LowAnalyticRankEqualityMechanism bg)
    (hCoverage : UniversalLowAnalyticRankCoverage bg) :
    BSDClayCoreObligation bg := by
  intro E _
  exact hLow E (hCoverage E)

/-!
The point of this theorem is fail-closed attribution:

  low-rank equality theorem + universal low-rank coverage -> BSD.

The first input is established mathematics in important settings.
The second input is not supplied by the low-rank theorem and must never be
silently inferred from it.

Therefore the Gross--Zagier/Kolyvagin lane is a genuine partial mechanism but
not the missing universal rank bridge.
-/

end Synthesis.Millennium.BSD
