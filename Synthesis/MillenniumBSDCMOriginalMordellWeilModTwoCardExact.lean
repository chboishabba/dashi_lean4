import Synthesis.MillenniumBSDCMActualE2H1ExplicitImageWeldExact
import Synthesis.MillenniumBSDCMOriginalExplicitCokernelZeroExact
import Mathlib.Tactic

/-!
# Selected BSD curve: actual E(Q)/2E(Q) has four classes

The existing proof owners give two ORIGINAL group/object equivalences:
* the global Kummer quotient-to-explicit Selmer multiplicative equivalence;
* the four-element rational 2-torsion code-to-original explicit Selmer
  equivalence.

Compose these exact maps, with no fresh dimension receipt. The source
also gives an actual finiteness/cardinality proof for the quotient,
but deliberately does not declare Mordell-Weil rank zero: the
finitely-generated/rank-vs-mod-two lemma and identification of all
rational 2-torsion are separately required.

K0 pinned local Lean kernel acceptance remains open.
-/

namespace Synthesis.Millennium.BSD

/-- An explicitly enumerated Fintype for the original four
rational two-torsion constructors, not a new model or oracle. -/
instance cmRationalTwoTorsionPointFintype :
    Fintype RationalTwoTorsionPoint where
  elems := {.infinity, .zero, .one, .negOne}
  complete T := by cases T <;> simp

theorem cmRationalTwoTorsionPoint_card_eq_four :
    Fintype.card RationalTwoTorsionPoint = 4 := by
  decide

/-- The original explicit Selmer carrier has four elements. -/
noncomputable instance cmOriginalExplicitTwoSelmerFintype :
    Fintype explicitTwoSelmerSubgroup :=
  Fintype.ofEquiv RationalTwoTorsionPoint
    cmTorsionEquivOriginalExplicitSelmer

theorem cmOriginalExplicitTwoSelmer_card_eq_four :
    Fintype.card explicitTwoSelmerSubgroup = 4 := by
  calc
    Fintype.card explicitTwoSelmerSubgroup =
        Fintype.card RationalTwoTorsionPoint :=
      Fintype.card_congr cmTorsionEquivOriginalExplicitSelmer.symm
    _ = 4 := cmRationalTwoTorsionPoint_card_eq_four

/-- A literal four-code equivalence for E(Q)/2E(Q). This is a
consequence of the original global quotient and original explicit
descent, not an abstract group-cardinality hypothesis. -/
noncomputable def cmOriginalMordellWeilModuloTwoEquivTorsion :
    (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) ≃
      RationalTwoTorsionPoint :=
  cmGlobalKummerQuotientEquivExplicitSelmer.toEquiv.trans
    cmTorsionEquivOriginalExplicitSelmer.symm

noncomputable instance cmMordellWeilModuloTwoFintype :
    Fintype
      (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) :=
  Fintype.ofEquiv RationalTwoTorsionPoint
    cmOriginalMordellWeilModuloTwoEquivTorsion.symm

/-- This is the exact cardinality result needed by the independent
Mordell-Weil rank theorem. It does not itself prove rank zero. -/
theorem cmOriginalMordellWeilModuloTwo_card_eq_four :
    Fintype.card
      (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) = 4 := by
  calc
    Fintype.card
        (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) =
      Fintype.card RationalTwoTorsionPoint :=
      Fintype.card_congr cmOriginalMordellWeilModuloTwoEquivTorsion
    _ = 4 := cmRationalTwoTorsionPoint_card_eq_four

end Synthesis.Millennium.BSD
