import Synthesis.MillenniumBSDUniversalSelmerAnalyticMaxCut
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact

/-!
# BSD universal rank inequality mechanisms

The frozen Clay theorem is split into the two genuinely independent directions

  Mordell--Weil rank <= analytic rank
  analytic rank <= Mordell--Weil rank.

The repository already contains a literal worked-case 2-Selmer subgroup,
a global Kummer map into it, an injective quotient map, and the literal
cokernel of that map. Those are real arithmetic objects, but they are attached
to the worked rational curve rather than universally parameterized by the
frozen RationalEllipticCurve.

This file therefore does not build another generic Selmer-rank mediator.
Instead it records the exact theorem shapes a universal elliptic-Selmer object
would have to support to shorten either side of the rank sandwich.
-/

namespace Synthesis.Millennium.BSD

def UniversalBSDLowerRankBound
    (bg : BSDEstablishedBackground) : Prop :=
  ∀ E : RationalEllipticCurve,
    bg.algebraic.rank E ≤ bg.analytic.rank E

def UniversalBSDUpperRankBound
    (bg : BSDEstablishedBackground) : Prop :=
  ∀ E : RationalEllipticCurve,
    bg.analytic.rank E ≤ bg.algebraic.rank E

theorem bsdClayCore_of_independent_rank_bounds
    (bg : BSDEstablishedBackground)
    (hLower : UniversalBSDLowerRankBound bg)
    (hUpper : UniversalBSDUpperRankBound bg) :
    BSDClayCoreObligation bg := by
  intro E _
  exact Nat.le_antisymm (hUpper E) (hLower E)

/-!
## Kummer / Selmer route to the lower direction

The arithmetic input naturally supplied by a Kummer injection has the shape

  MW rank <= Selmer rank.

To reach the lower BSD inequality it still needs an independently proved
analytic cap

  Selmer rank <= analytic rank.
-/

structure UniversalSelmerLowerMechanism
    (bg : BSDEstablishedBackground) where
  selmerRank : RationalEllipticCurve → ℕ
  mordellWeil_le_selmer :
    ∀ E, bg.algebraic.rank E ≤ selmerRank E
  selmer_le_analytic :
    ∀ E, selmerRank E ≤ bg.analytic.rank E

theorem lowerRankBound_of_selmer
    (bg : BSDEstablishedBackground)
    (route : UniversalSelmerLowerMechanism bg) :
    UniversalBSDLowerRankBound bg := by
  intro E
  exact (route.mordellWeil_le_selmer E).trans
    (route.selmer_le_analytic E)

/-!
## Selmer route to the upper direction

To obtain the reverse BSD inequality through the same intermediate, one needs

  analytic rank <= Selmer rank
  Selmer rank <= MW rank.

The second inequality is qualitatively different from the ordinary Kummer
injection direction. It says the Selmer excess over Mordell--Weil rank has
collapsed. In a classical descent interpretation this is where a nontrivial
Selmer/Sha defect theorem would have to enter.

No such universal theorem is asserted here.
-/

structure UniversalSelmerUpperMechanism
    (bg : BSDEstablishedBackground) where
  selmerRank : RationalEllipticCurve → ℕ
  analytic_le_selmer :
    ∀ E, bg.analytic.rank E ≤ selmerRank E
  selmer_le_mordellWeil :
    ∀ E, selmerRank E ≤ bg.algebraic.rank E

theorem upperRankBound_of_selmer
    (bg : BSDEstablishedBackground)
    (route : UniversalSelmerUpperMechanism bg) :
    UniversalBSDUpperRankBound bg := by
  intro E
  exact (route.analytic_le_selmer E).trans
    (route.selmer_le_mordellWeil E)

/-!
## Directionality no-go
-/

theorem common_selmer_upper_bound_does_not_force_upper_rank_bound :
    ∃ (mw selmer analytic : ℕ),
      mw ≤ selmer ∧
      analytic ≤ selmer ∧
      ¬ analytic ≤ mw := by
  exact ⟨0, 1, 1, by decide, by decide, by decide⟩

theorem lower_direction_is_exactly_transitive
    {mw selmer analytic : ℕ}
    (hMS : mw ≤ selmer)
    (hSA : selmer ≤ analytic) :
    mw ≤ analytic :=
  hMS.trans hSA

/-!
## Worked-case Selmer scope guard

The existing exact sequence is valuable evidence that the arithmetic side is
not merely a wrapper. But its Selmer object has no RationalEllipticCurve
parameter, so it cannot by itself inhabit either universal mechanism above.
-/

abbrev ExistingWorkedCaseTwoSelmer :=
  explicitTwoSelmerSubgroup

abbrev ExistingWorkedCaseSelmerCokernel :=
  ExplicitTwoSelmerCokernel

/-!
## Max-cut consequence

A universal Selmer development is worth doing only if it is aimed at one of
two specific missing theorems:

LOWER lane
  construct universal elliptic Selmer
  + MW <= Selmer
  + Selmer <= analytic
  -> MW <= analytic.

UPPER lane
  construct universal elliptic Selmer
  + analytic <= Selmer
  + Selmer <= MW
  -> analytic <= MW.

The ordinary Kummer injection naturally contributes only to the first lane.
The second lane requires genuinely new defect-control input or a different
universal mechanism.

Once both independently sourced inequalities exist, the theorem
bsdClayCore_of_independent_rank_bounds reaches the frozen Clay endpoint.
-/

end Synthesis.Millennium.BSD
