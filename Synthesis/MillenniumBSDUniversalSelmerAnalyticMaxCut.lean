import Synthesis.MillenniumBSDUniversalRankWeld

/-!
# BSD universal Selmer / analytic max-cut

The frozen BSD Clay owner already binds the literal rational elliptic curve,
literal Hasse--Weil L-series continuation, analytic order at s = 1, and
Mordell--Weil free rank.

This file tests the proposed universal Selmer route at the theorem level.

Two facts are made explicit.

1. An unconstrained intermediate "Selmer rank" carrying equalities to both the
   analytic and Mordell--Weil ranks is exactly equivalent to BSD itself.  It is
   therefore only a relocation of the conjecture unless the intermediate rank
   is independently constructed from a genuine elliptic Selmer object.

2. The standard-looking one-sided shape

     MW rank <= Selmer rank
     Selmer rank = analytic rank

   yields only

     MW rank <= analytic rank.

   It does not by logic alone yield rank equality; the reverse inequality (or
   an independent zero-defect theorem) is still required.

The pinned Mathlib tree currently exposes Dedekind-domain Selmer groups, but no
elliptic-curve Selmer/Kummer carrier on the exact WeierstrassCurve Q object
used by the frozen Clay owner.  Accordingly this file does not invent such a
carrier.
-/

namespace Synthesis.Millennium.BSD

structure BSDRankMediator
    (bg : BSDEstablishedBackground) where
  rank : RationalEllipticCurve → ℕ

def UniversalBSDMediatorWeld
    (bg : BSDEstablishedBackground)
    (m : BSDRankMediator bg) : Prop :=
  ∀ E : RationalEllipticCurve,
    bg.analytic.rank E = m.rank E ∧
    m.rank E = bg.algebraic.rank E

theorem bsdClayCoreOfMediatorWeld
    (bg : BSDEstablishedBackground)
    (m : BSDRankMediator bg)
    (h : UniversalBSDMediatorWeld bg m) :
    BSDClayCoreObligation bg := by
  intro E _
  exact (h E).1.trans (h E).2

theorem mediatorWeldOfBSDClayCore
    (bg : BSDEstablishedBackground)
    (h : BSDClayCoreObligation bg) :
    ∃ m : BSDRankMediator bg, UniversalBSDMediatorWeld bg m := by
  let m : BSDRankMediator bg :=
    { rank := bg.algebraic.rank }
  refine ⟨m, ?_⟩
  intro E
  constructor
  · exact h E (Set.mem_univ E)
  · rfl

theorem existsMediatorWeld_iff_BSDClayCore
    (bg : BSDEstablishedBackground) :
    (∃ m : BSDRankMediator bg, UniversalBSDMediatorWeld bg m) ↔
      BSDClayCoreObligation bg := by
  constructor
  · rintro ⟨m, hm⟩
    exact bsdClayCoreOfMediatorWeld bg m hm
  · exact mediatorWeldOfBSDClayCore bg

/-!
## One-sided Selmer-shaped comparison

An arithmetic injection or Kummer map typically points from Mordell--Weil
information into a Selmer object. Even if an analytic theorem identifies the
selected Selmer rank with the analytic order, those two statements alone
provide only one inequality.
-/

structure BSDOneSidedSelmerShape
    (bg : BSDEstablishedBackground) where
  selmerRank : RationalEllipticCurve → ℕ
  mordellWeil_le_selmer :
    ∀ E, bg.algebraic.rank E ≤ selmerRank E
  selmer_eq_analytic :
    ∀ E, selmerRank E = bg.analytic.rank E

theorem mordellWeil_le_analytic_of_oneSidedSelmer
    (bg : BSDEstablishedBackground)
    (s : BSDOneSidedSelmerShape bg)
    (E : RationalEllipticCurve) :
    bg.algebraic.rank E ≤ bg.analytic.rank E := by
  exact (s.mordellWeil_le_selmer E).trans_eq (s.selmer_eq_analytic E)

theorem oneSidedSelmerShape_not_logically_rankEquality :
    ∃ (m s a : ℕ), m ≤ s ∧ s = a ∧ a ≠ m := by
  exact ⟨0, 1, 1, by decide, rfl, by decide⟩

/-!
## Exact universal rank-sandwich target

For the frozen canonical ranks, the smallest comparison-shaped theorem
sufficient for BSD is the two-sided inequality pair. A genuine Selmer
mechanism may prove these through an independently defined elliptic Selmer
object, but both directions must ultimately be discharged.
-/

def UniversalBSDRankSandwich
    (bg : BSDEstablishedBackground) : Prop :=
  (∀ E : RationalEllipticCurve,
      bg.algebraic.rank E ≤ bg.analytic.rank E) ∧
  (∀ E : RationalEllipticCurve,
      bg.analytic.rank E ≤ bg.algebraic.rank E)

theorem bsdClayCoreOfRankSandwich
    (bg : BSDEstablishedBackground)
    (h : UniversalBSDRankSandwich bg) :
    BSDClayCoreObligation bg := by
  intro E _
  exact Nat.le_antisymm (h.2 E) (h.1 E)

theorem rankSandwichOfBSDClayCore
    (bg : BSDEstablishedBackground)
    (h : BSDClayCoreObligation bg) :
    UniversalBSDRankSandwich bg := by
  constructor
  · intro E
    exact Nat.le_of_eq (h E (Set.mem_univ E)).symm
  · intro E
    exact Nat.le_of_eq (h E (Set.mem_univ E))

theorem universalBSDRankSandwich_iff_clayCore
    (bg : BSDEstablishedBackground) :
    UniversalBSDRankSandwich bg ↔ BSDClayCoreObligation bg := by
  exact ⟨bsdClayCoreOfRankSandwich bg, rankSandwichOfBSDClayCore bg⟩

/-!
## Max-cut consequence

An arbitrary mediator is a no-go: it is propositionally equivalent to BSD.

A productive Selmer route therefore has to add an independently defined
elliptic Selmer object on the same curve and prove genuinely asymmetric input
theorems strong enough to discharge both sides of UniversalBSDRankSandwich
(or an equivalent zero-defect statement).

Until an elliptic Selmer/Kummer carrier exists on the pinned Mathlib
WeierstrassCurve Q object, adding further abstract descent wrappers would not
shorten the Clay theorem.
-/

end Synthesis.Millennium.BSD
