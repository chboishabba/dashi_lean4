import Synthesis.MillenniumBSDCMOriginalE32LiteralReductionGeometryExact
import Synthesis.MillenniumBSDFrobeniusPointCount
import Integration.EisensteinJZeroBadPrimeTwoExact
import Integration.EisensteinJZeroBadPrimeThreeExact
import Integration.EisensteinJZeroInertPrimeEulerExact
import Mathlib.Tactic

/-!
# Original E32 ↔ Eisenstein j=0 exact source-lineage negative controls

This does NOT identify the curves or transfer their L-functions.
E32 = y²=x³-x, discriminant 64, original BSD / Gaussian CM;
J+  = y²=x³+1, discriminant -432, original Eisenstein/C₃ CM;
J-  = y²=x³-1, the minus-one twist used only as a finite control.

REUSE:
- the original E32 odd-prime IsElliptic and p=2 cusp owners;
- the original Eisenstein bad-prime 2 and 3 singular-point proofs;
- the original E32 Frobenius point-count owner;
- the original Eisenstein inert-prime Frobenius owner.

Same naive point count does NOT imply same reduction, isogeny, or
Euler factor. At p=3, E32 has good reduction, J+ has a singular
fibre, yet the naive projective counts happen to agree (=4).
At p=5, E32 a5=-2 but J+ a5=0. At p=7 the J+ and J- traces
differ by sign (-4 versus +4): a twist is not an identity.

No Mathlib p-adic minimal-model/prime-place weld is constructed here,
and no bad-prime Euler factor is inferred from naive singular counts.
Source-written; pinned Lean kernel NOT run.
-/

namespace Synthesis.Millennium.BSD

private theorem threePrime : Nat.Prime 3 := by norm_num
private theorem fivePrime : Nat.Prime 5 := by norm_num
private theorem sevenPrime : Nat.Prime 7 := by norm_num

/-- Original E32's literal fibre at three is smooth, whereas the
    already-owned Eisenstein J+ fibre at three is singular. -/
theorem e32_good_jPlus_singular_at_three :
    (cmOriginalLiteralModP 3).IsElliptic ∧
    Integration.EisensteinJZeroBadPrimeThreeExact.reducedCurveThreeEquation
      (2 : ZMod 3) 0 ∧
    Integration.EisensteinJZeroBadPrimeThreeExact.reducedCurveThreeDx
      (2 : ZMod 3) = 0 ∧
    Integration.EisensteinJZeroBadPrimeThreeExact.reducedCurveThreeDy
      (0 : ZMod 3) = 0 := by
  letI : Fact (Nat.Prime 3) := ⟨threePrime⟩
  exact ⟨
    cmOriginalLiteralModP_isElliptic 3 (by norm_num),
    Integration.EisensteinJZeroBadPrimeThreeExact.badReductionSingularPoint_on_curve,
    Integration.EisensteinJZeroBadPrimeThreeExact.badReductionSingularPoint_dx,
    Integration.EisensteinJZeroBadPrimeThreeExact.badReductionSingularPoint_dy⟩

/-- Same cardinality is the WRONG criterion for same local reduction:
    the original E32 good fibre and J+ singular fibre both have four
    naive projective F3 points. -/
theorem e32_jPlus_naive_projective_count_at_three :
    projectivePointCount 3 =
      Integration.EisensteinJZeroBadPrimeThreeExact.reducedCurveThreeProjectiveNaivePointCount := by
  letI : Fact (Nat.Prime 3) := ⟨threePrime⟩
  native_decide

/-- Reuse the existing J+ bad-prime-two theorem rather than proving
    another singular-reduction fact about the same Eisenstein source. -/
theorem jPlus_two_singular_source_reused :
    Integration.EisensteinJZeroBadPrimeTwoExact.reducedCurveTwoEquation
      (0 : ZMod 2) 1 ∧
    Integration.EisensteinJZeroBadPrimeTwoExact.reducedCurveTwoDx
      (0 : ZMod 2) = 0 ∧
    Integration.EisensteinJZeroBadPrimeTwoExact.reducedCurveTwoDy
      (1 : ZMod 2) = 0 :=
  ⟨Integration.EisensteinJZeroBadPrimeTwoExact.badReductionSingularPoint_on_curve,
   Integration.EisensteinJZeroBadPrimeTwoExact.badReductionSingularPoint_dx,
   Integration.EisensteinJZeroBadPrimeTwoExact.badReductionSingularPoint_dy⟩

/-- E32 is a different good-prime Frobenius source from Eisenstein J+:
    at prime five its trace is -2 rather than the J+ inert trace 0. -/
theorem e32_jPlus_frobenius_five_distinct :
    frobeniusCoefficient 5 ≠
      Dashi.EisensteinJZeroInertPrimeEulerExact.jZeroFrobeniusTrace 5 := by
  letI : Fact (Nat.Prime 5) := ⟨fivePrime⟩
  have hE : frobeniusCoefficient 5 = -2 := by native_decide
  have hJ :
      Dashi.EisensteinJZeroInertPrimeEulerExact.jZeroFrobeniusTrace 5 = 0 :=
    Dashi.EisensteinJZeroInertPrimeEulerExact.frobeniusTrace_inert 5
      (by norm_num)
  omega

/-- Finite negative-control ONLY for the recollected twist y²=x³-1.
    The actual Eisenstein source owns J+; do not retarget that proof. -/
def jMinusSevenNaiveAffineCount : Nat :=
  ((Finset.univ : Finset (ZMod 7 × ZMod 7)).filter
    fun xy => decide (xy.2 ^ 2 = xy.1 ^ 3 - 1)).card

theorem jMinusSevenNaiveAffineCount_eq_three :
    jMinusSevenNaiveAffineCount = 3 := by native_decide

theorem jPlusSevenTrace_eq_minus_four :
    Dashi.EisensteinJZeroInertPrimeEulerExact.jZeroFrobeniusTrace 7 = -4 := by
  letI : Fact (Nat.Prime 7) := ⟨sevenPrime⟩
  native_decide

/-- J- has four naive projective F7 points, hence trace +4,
    whereas the separate J+ point-count source gives trace -4. -/
theorem jMinusSevenTrace_eq_plus_four :
    ((7 : ℤ) + 1 - ((jMinusSevenNaiveAffineCount + 1 : Nat) : ℤ)) = 4 := by
  rw [jMinusSevenNaiveAffineCount_eq_three]
  norm_num

end Synthesis.Millennium.BSD
