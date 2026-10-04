import Synthesis.MillenniumBSDCMQuarterPointBoundaryExact
import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Mathlib.Tactic

/-!
# Selected CM curve: global geometric Kummer localizes to literal p-adic x-T

The selected-curve global comparison is now closed on every rational point.
This owner pushes that theorem through the two already-paid localization
squares:

1. the literal explicit identity
     totalLocalKummer(localize P) = localize(totalGlobalKummer P);
2. generic continuous-H¹ restriction naturality, conditional only on the
   scalar p-adic Kummer compatibility equivalence.

Thus no new local elliptic representation or cohomology carrier is introduced.
The only arithmetic input is the already-named scalar theorem
`PadicQuadraticKummerCompatibility p`.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- The now-paid global geometric/x-T equality localizes literally to the
repository's existing total local Kummer map on every rational point. -/
theorem cmRationalCohomologicalKummerXT_localizes
    (p : ℕ) [Fact p.Prime]
    (P : RationalProjectivePoint) :
    localizeKummerPair p
        (cmRationalCohomologicalKummerXTSquareClass P) =
      totalLocalKummer p (localizeRationalProjectivePoint p P) := by
  rw [cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_paid]
  exact (totalGlobalKummer_localizes p P).symm

/-- Global generic-E[2] H¹ class reconstructed from the literal x-T class of
`P`.  By the paid global comparison this is the same square-class class as the
direct geometric Kummer construction, expressed on the generic trivial
coefficient object used by restriction naturality. -/
noncomputable def cmRationalGenericKummerH1
    (P : RationalProjectivePoint) :
    ContinuousCohomology.continuousCohomology 1
      (genericTwoTorsionRepresentation RationalAbsoluteGalois) :=
  (cmGenericTrivialE2H1MulEquivRatSquareClasses.symm
    (totalGlobalKummer P)).toAdd

@[simp] theorem cmRationalGenericKummerH1_squareClass
    (P : RationalProjectivePoint) :
    cmGenericTrivialE2H1MulEquivRatSquareClasses
        (Multiplicative.ofAdd (cmRationalGenericKummerH1 P)) =
      totalGlobalKummer P := by
  exact cmGenericTrivialE2H1MulEquivRatSquareClasses.apply_symm_apply
    (totalGlobalKummer P)

/-- Conditional only on the scalar p-adic Kummer equivalence/naturality, H¹
restriction of the selected global Kummer class evaluates to the literal
localized square-class pair. -/
theorem cmRationalGenericKummerH1_padic_squareClass
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p)
    (P : RationalProjectivePoint) :
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p)
          (cmRationalGenericKummerH1 P))) =
      localizeKummerPair p (totalGlobalKummer P) := by
  have hNat := padicH1SquareClassNaturality_paid p h
  have hP := hNat (cmRationalGenericKummerH1 P)
  simpa [rationalGenericTwoTorsionH1MulEquivSquareClassPair,
    cmGenericTrivialE2H1MulEquivRatSquareClasses,
    cmRationalGenericKummerH1] using hP

/-- Same theorem against the existing total p-adic x-T Kummer map.  This is
the exact rational-point local compatibility square requested by the roadmap. -/
theorem cmRationalGenericKummerH1_padic_eq_totalLocalKummer
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p)
    (P : RationalProjectivePoint) :
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p)
          (cmRationalGenericKummerH1 P))) =
      totalLocalKummer p (localizeRationalProjectivePoint p P) := by
  rw [cmRationalGenericKummerH1_padic_squareClass p h P]
  exact (totalGlobalKummer_localizes p P).symm

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head Lean certification:
* the full selected-curve global geometric Kummer theorem localizes to the
  literal `totalLocalKummer` on every rational point;
* generic H¹ restriction contributes no new hypothesis;
* all coefficient/square-class localization bookkeeping is closed.

THE REMAINING FINITE-PLACE ARITHMETIC THEOREM IS EXACTLY THE EXISTING SCALAR
OWNER:

  `PadicQuadraticKummerCompatibility p`

for every prime p.  To identify the *entire local Kummer image* (not merely
localized rational points), one must additionally prove the actual local
elliptic Kummer image/kernel theorem already named in
`MillenniumBSDLocalKummerCohomologyReduction`.  Those are genuine local-field
arithmetic facts, not missing global or H¹ architecture.
-/

end

end Synthesis.Millennium.BSD
