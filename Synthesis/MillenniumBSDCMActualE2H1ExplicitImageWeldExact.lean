import Synthesis.MillenniumBSDCMOriginalExplicitCokernelZeroExact
import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Synthesis.MillenniumBSDCMQuarterPointBoundaryExact
import Mathlib.Tactic

/-!
# BSD: actual global H1(E[2]) image of original explicit two-Selmer

This is an UNCONDITIONAL (given the imported source lemmas) global
cohomological *image* join, not an assertion of full local Kummer
image equality. The imported rational square-class Kummer equivalence
is the actual H1 of the generic E[2] representation, not H1(E(Qbar)).

Source owners:
  BSDLocalKummerCohomologyReduction.explicitSelmerToGenericTwoTorsionH1
  BSDCMQuarterPointBoundaryExact.cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_paid
  BSDCMOriginalExplicitSelmerFourTorsionExact.cmTorsionCodeToOriginalExplicitSelmer_surjective

The image consists precisely of four original rational-torsion
classes. No implication to classical Sha(E)[2] is made.
K0 exact-head Lean kernel run remains pending.
-/

namespace Synthesis.Millennium.BSD

/-- The original explicit 2-Selmer injection into genuine global
continuous E[2]-valued H1 is injective. The proof uses the already
constructed global quadratic Kummer equivalence, not an abstract
cohomological comparison hypothesis. -/
theorem cmExplicitSelmerToActualE2H1_injective :
    Function.Injective explicitSelmerToGenericTwoTorsionH1 := by
  intro s t h
  have hcoords := congrArg
    (fun x =>
      rationalGenericTwoTorsionH1MulEquivSquareClassPair
        (Multiplicative.ofAdd x)) h
  have heq :
      (s : RatSquareClass × RatSquareClass) =
        (t : RatSquareClass × RatSquareClass) := by
    simpa only [explicitSelmerToGenericTwoTorsionH1_squareClass]
      using hcoords
  exact Subtype.ext heq

/-- Every class in the original explicit-Selmer global E[2]-H1 image
is the actual image of one of the four original rational torsion
constructors. This does NOT say all locally admissible H1 classes
lie in this image; that reverse local Kummer comparison is K1. -/
theorem cmActualE2H1ExplicitSelmerImage_eq_torsion :
    Set.range explicitSelmerToGenericTwoTorsionH1 =
      {x | ∃ T : RationalTwoTorsionPoint,
        x = explicitSelmerToGenericTwoTorsionH1
          (cmTorsionCodeToOriginalExplicitSelmer T)} := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨T, hT⟩ :=
      cmTorsionCodeToOriginalExplicitSelmer_surjective s
    refine ⟨T, ?_⟩
    rw [hT]
  · rintro ⟨T, rfl⟩
    exact ⟨cmTorsionCodeToOriginalExplicitSelmer T, rfl⟩

/-- The first *global* selected-curve Kummer comparison square is
source-written in the geometric quarter-point owner. Here we
transport it to the original explicit Selmer and genuine H1 map. -/
theorem cmGlobalGeometricXTKummer_toActualE2H1_square
    (P : RationalProjectivePoint) :
    rationalGenericTwoTorsionH1MulEquivSquareClassPair
      (Multiplicative.ofAdd
        (explicitSelmerToGenericTwoTorsionH1
          (globalKummerSelmerHom (Multiplicative.ofAdd P)))) =
      cmRationalCohomologicalKummerXTSquareClass P := by
  rw [explicitSelmerToGenericTwoTorsionH1_squareClass]
  rw [globalKummerSelmerHom_apply]
  exact (cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_paid P).symm

end Synthesis.Millennium.BSD
