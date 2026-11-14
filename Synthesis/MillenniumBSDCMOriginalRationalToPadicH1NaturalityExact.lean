import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Synthesis.MillenniumBSDActualRationalPointGroup
import Mathlib.Tactic

/-!
# K1: original global rational point → p-adic H¹ localization square

Existing source owners:
* totalGlobalKummer_localizes: literal x-T evaluation of the
  original rational elliptic point commutes with Q→Q_p;
* explicitSelmerToGenericTwoTorsionH1_squareClass:
  original global E[2] H¹ class corresponds to x-T square classes;
* padicH1SquareClassNaturality_paid:
  the group-cohomology restriction square is genuinely natural,
  PROVIDED the original scalar local quadratic Kummer equivalence
  and its naturality are supplied.

We JOIN THESE EXACT owners to give the literal point-level
commuting square on the SAME RationalProjectivePoint and
PadicProjectivePoint p carriers, for ALL primes p. The only
remaining local scalar premise is
    h : PadicQuadraticKummerCompatibility p.
It is EXPLICIT and this module does NOT inhabit that record.

The missing full K1 equivalence and elliptic local H¹ image
identification are separate. Source-written; local Lean kernel
acceptance pending.
-/

namespace Synthesis.Millennium.BSD

/-- Original E(Q) Kummer class restricted to G_{Qp}, evaluated
under the compatible local E[2] H¹/square-class equivalence,
equals the original local x-T Kummer evaluation at the
actual localized rational elliptic point. -/
theorem cmOriginalPoint_E2H1Restriction_eq_localXT
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p)
    (P : RationalProjectivePoint) :
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p)
          (explicitSelmerToGenericTwoTorsionH1
            (globalKummerToSelmer P)))) =
      totalLocalKummer p (localizeRationalProjectivePoint p P) := by
  have hNat :=
    padicH1SquareClassNaturality_paid p h
      (explicitSelmerToGenericTwoTorsionH1
        (globalKummerToSelmer P))
  rw [explicitSelmerToGenericTwoTorsionH1_squareClass] at hNat
  change
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p)
          (explicitSelmerToGenericTwoTorsionH1
            (globalKummerToSelmer P)))) =
      localizeKummerPair p (totalGlobalKummer P) at hNat
  exact hNat.trans (totalGlobalKummer_localizes p P).symm

end Synthesis.Millennium.BSD
