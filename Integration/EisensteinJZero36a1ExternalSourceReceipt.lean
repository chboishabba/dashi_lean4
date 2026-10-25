/-!
# External-source receipt for the concrete curve y^2 = x^3 + 1

This file is provenance only.  It records externally acquired metadata used to
orient the remaining bad-prime/global roadmap; none of the strings or booleans
below are theorem authority.

Sources consulted in this tranche:

* William Stein's Cremona-derived `LRatios` table, which lists conductor `36`,
  class `A`, curve `1` with Weierstrass coefficients `[0,0,0,0,1]`.
  https://wstein.org/Tables/lratio/

* PARI/GP User's Guide, which explicitly identifies
  `ellinit([0,0,0,0,1])`, `y^2=x^3+1`, with `ellinit("36a1")`, exhibits the
  reduction over `F_2` as singular, and records the short-Weierstrass
  discriminant formula `Delta = -64*a4^3 - 432*a6^2`.
  https://pari.math.u-bordeaux.fr/pub/pari/manuals/2.7.6/users.pdf

For `a4=0`, `a6=1`, that external discriminant formula yields `Delta=-432`,
so its rational prime divisors are 2 and 3.  The repository separately proves
literal singular-reduction facts over both `F_2` and `F_3`; it does not treat
this external receipt as a proof of those Lean theorems.

Attribution firewall:
* external database/manual metadata stays externally attributed;
* Mathlib generic infrastructure stays Mathlib-attributed;
* DASHI/Lean specialisation/composition stays DASHI-attributed;
* no external source is promoted to a kernel proof object.
-/

namespace Integration.EisensteinJZero36a1ExternalSourceReceipt

structure ExternalCurveSourceReceipt where
  curveLabel : String
  equation : String
  conductor : Nat
  discriminant : Int
  badRationalPrimes : List Nat
  steinTableSource : String
  pariGuideSource : String
  externalCurveLabelObserved : Bool
  externalEquationObserved : Bool
  externalConductor36Observed : Bool
  externalDiscriminantFormulaObserved : Bool
  externalF2SingularityExampleObserved : Bool
  externalSourceIsProofAuthority : Bool
  mathlibInfrastructureAttributedToExternalSource : Bool
  dashiSpecializationAttributedToExternalSource : Bool
  deriving Repr

/-- External metadata receipt; not theorem authority. -/
def receipt : ExternalCurveSourceReceipt where
  curveLabel := "36a1"
  equation := "y^2 = x^3 + 1"
  conductor := 36
  discriminant := -432
  badRationalPrimes := [2, 3]
  steinTableSource := "https://wstein.org/Tables/lratio/"
  pariGuideSource := "https://pari.math.u-bordeaux.fr/pub/pari/manuals/2.7.6/users.pdf"
  externalCurveLabelObserved := true
  externalEquationObserved := true
  externalConductor36Observed := true
  externalDiscriminantFormulaObserved := true
  externalF2SingularityExampleObserved := true
  externalSourceIsProofAuthority := false
  mathlibInfrastructureAttributedToExternalSource := false
  dashiSpecializationAttributedToExternalSource := false

end Integration.EisensteinJZero36a1ExternalSourceReceipt
