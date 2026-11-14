import Synthesis.MillenniumBSDCMRealNonexceptionalXTSignImageCompleteExact
import Synthesis.MillenniumBSDCMActualE2H1ExplicitImageWeldExact
import Synthesis.MillenniumBSDCMQ2ActualLocalImageParityExact
import Synthesis.MillenniumBSDCMOriginalRationalToPadicH1NaturalityExact
import Mathlib.Tactic

/-!
# BSD K1 actual original H¹(E[2]) + Q₂ local Kummer + explicit Selmer

NOT a new square-class model. Every object is selected from the
original Lean PR #107 source and the actual curve y²=x³−x.

Combines already-proved SOURCE-WRITTEN donors:
* cmActualE2H1ExplicitSelmerImage_eq_torsion — global E[2] H¹ image
  of explicit all-place Selmer equals four original rational torsion images;
* cmQ2LocalKummerImage_firstParity_zero — all actual E(Q₂) points
  have even first-coordinate valuation in the genuine Q₂ quotient;
* cmExplicitTwoSelmer_firstRationalV2Parity_zero — local-to-global
  original rational square-class parity;
* cmOriginalPoint_E2H1Restriction_eq_localXT — pointwise naturality
  conditional on PadicQuadraticKummerCompatibility p.

The missing full local quadratic Kummer equivalence, local-image
SURJECTIVITY into the H¹-condition, continuous Sha(E)[2] exactness and
odd Sha remain OPEN. The new source has no axioms/postulates/sorry.
Exact-head Lean kernel acceptance is still required.
-/

namespace Synthesis.Millennium.BSD

/-- Actual original explicit global H¹(E[2]) range is the same four
torsion images, while every original global selected Selmer class
satisfies the genuine local-Q₂ even-first valuation constraint. -/
theorem cmOriginalK1ActualE2H1TorsionAndQ2LocalCondition :
    Set.range explicitSelmerToGenericTwoTorsionH1 =
      {x | ∃ T : RationalTwoTorsionPoint,
        x = explicitSelmerToGenericTwoTorsionH1
          (cmTorsionCodeToOriginalExplicitSelmer T)}
    ∧
    (∀ s : explicitTwoSelmerSubgroup,
       cmQ2SquareClassValuationParity
         (localizeKummerPair 2
           (s : RatSquareClass × RatSquareClass)).1 = 0) := by
  exact ⟨cmActualE2H1ExplicitSelmerImage_eq_torsion,
    cmExplicitTwoSelmer_localQ2FirstParity_zero⟩

/-- No theorem claims a converse for every parity-zero Q₂ class:
actual local-image membership is strictly stronger than a necessary
valuation condition. This theorem records the correct direction. -/
theorem cmOriginalK1Q2ActualImage_toLocalNecessaryFirstParity
    (c : PadicSquareClass 2 × PadicSquareClass 2)
    (hc : c ∈ LocalKummerImage 2) :
    cmQ2SquareClassValuationParity c.1 = 0 :=
  cmQ2LocalKummerImage_firstParity_zero c hc


/-- Original real E(R) source image pays BOTH equal-sign cases,
rather than only an uninhabited necessary equality of sign bits.
This is on the actual affine point locus; classical H1(R,E[2])
and full local-Kummer cohomological equivalence remain separate. -/
theorem cmOriginalK1RealNonexceptionalSignImageComplete :
    cmOriginalRealNonexceptionalXTSignImage =
      {c : Bool × Bool | c.1 = c.2} :=
  cmOriginalRealNonexceptionalXTSignImage_eq

end Synthesis.Millennium.BSD
