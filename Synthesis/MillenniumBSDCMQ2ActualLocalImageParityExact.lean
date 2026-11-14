import Synthesis.MillenniumBSDCMQ2SquareClassValuationParityExact
import Synthesis.MillenniumBSDTotalLocalKummer
import Synthesis.MillenniumBSDExplicitSelmerSubgroup
import Mathlib.Tactic

/-!
# BSD: parity obstruction on the ORIGINAL local Kummer image at p=2

This owner advances the Q_2 lemma from arbitrary affine coordinates to the
repository's literal totalLocalKummer 2 and LocalKummerImage 2, with its
original PadicProjectivePoint 2 carrier. The selected curve is
y^2=x^3-x.

The total local map has three branches: infinity, x=0, x=1, and the
ordinary x-T branch (which includes x=-1). The ordinary branch is
proved without assuming y != 0 by treating x=-1 explicitly.

The theorem excludes every local Kummer class whose first square
coordinate has odd 2-adic valuation; it does not assert that every
class with even first-coordinate parity belongs to the local image.

The original global explicit Selmer subgroup is already defined as
the all-place intersection of these actual local ranges. Its
2-adic restriction therefore also obeys parity zero.

No new local-point carrier, Selmer group, or synthetic Kummer map.
A local kernel check on the exact current Lean/toolchain is required.
-/

namespace Synthesis.Millennium.BSD

/-- Even valuation of x for any ordinary local x-T coordinate,
including the y=0, x=-1 torsion point. -/
theorem cmQ2OrdinaryXValuationEven_all
    (P : OrdinaryPadicKummerPoint 2) :
    Even P.x.valuation := by
  by_cases hy : P.y = 0
  · have hf := cmQ2Affine_factorization P.x P.y P.onCurve
    have hprod : P.x * (P.x - 1) * (P.x + 1) = 0 := by
      calc
        P.x * (P.x - 1) * (P.x + 1) = P.y ^ 2 := hf.symm
        _ = 0 := by rw [hy]; ring
    have hxplus : P.x + 1 = 0 := by
      rcases mul_eq_zero.mp hprod with hleft | hright
      · rcases mul_eq_zero.mp hleft with hzero | hone
        · exact False.elim (P.x_ne_zero hzero)
        · exact False.elim (P.x_ne_one (sub_eq_zero.mp hone))
      · exact hright
    have hx : P.x = -1 := by
      calc
        P.x = (P.x + 1) - 1 := by ring
        _ = -1 := by rw [hxplus]; ring
    simp [hx, cmQ2Valuation_negOne]
  · exact cmQ2NonexceptionalXValuationEven
      P.x P.y P.onCurve hy

/-- Direct parity theorem for the original ordinary local
Kummer coordinates, with no y != 0 restriction. -/
theorem cmQ2OrdinaryPadicKummer_firstParity_zero
    (P : OrdinaryPadicKummerPoint 2) :
    cmQ2SquareClassValuationParity (ordinaryPadicKummer P).1 = 0 := by
  change cmQ2SquareClassValuationParity
    (padicSquareClassOf 2 (⟨P.x, P.x_ne_zero⟩ : NonzeroPadic 2)) = 0
  exact cmQ2SquareClassValuationParity_of_even
    (⟨P.x, P.x_ne_zero⟩ : NonzeroPadic 2)
    (cmQ2OrdinaryXValuationEven_all P)

/-- At infinity the first literal local Kummer coordinate is [1]. -/
theorem cmQ2LocalInfinity_firstParity_zero :
    cmQ2SquareClassValuationParity (localInfinityKummer 2).1 = 0 := by
  change cmQ2SquareClassValuationParity
    (localizeSquareClass 2 (squareClassOf oneNZ)) = 0
  rw [localizeSquareClass_mk, cmQ2SquareClassValuationParity_rep]
  simp [localizeNonzeroRat, oneNZ, Padic.valuation_one]

/-- At (0,0), the first literal local Kummer coordinate is [-1]. -/
theorem cmQ2LocalZero_firstParity_zero :
    cmQ2SquareClassValuationParity (localZeroKummer 2).1 = 0 := by
  change cmQ2SquareClassValuationParity
    (localizeSquareClass 2 (squareClassOf negOneNZ)) = 0
  rw [localizeSquareClass_mk, cmQ2SquareClassValuationParity_rep]
  simp [localizeNonzeroRat, negOneNZ, cmQ2Valuation_negOne]

/-- At (1,0), the first literal local Kummer coordinate is [1]. -/
theorem cmQ2LocalOne_firstParity_zero :
    cmQ2SquareClassValuationParity (localOneKummer 2).1 = 0 := by
  change cmQ2SquareClassValuationParity
    (localizeSquareClass 2 (squareClassOf oneNZ)) = 0
  exact cmQ2LocalInfinity_firstParity_zero

/-- The literal total Q_2 Kummer map has parity-zero first coordinate,
for EVERY point of the original local point carrier, including O,
(0,0), (1,0), and the ordinary branch containing (-1,0). -/
theorem cmQ2TotalLocalKummer_firstParity_zero
    (P : PadicProjectivePoint 2) :
    cmQ2SquareClassValuationParity (totalLocalKummer 2 P).1 = 0 := by
  cases P with
  | infinity =>
      exact cmQ2LocalInfinity_firstParity_zero
  | affine x y hcurve =>
      by_cases hxzero : x = 0
      · simpa [totalLocalKummer, hxzero] using
          cmQ2LocalZero_firstParity_zero
      · by_cases hxone : x = 1
        · simpa [totalLocalKummer, hxzero, hxone] using
            cmQ2LocalOne_firstParity_zero
        · let Q : OrdinaryPadicKummerPoint 2 :=
            { x := x, y := y, onCurve := hcurve
            , x_ne_zero := hxzero, x_ne_one := hxone }
          have h := cmQ2OrdinaryPadicKummer_firstParity_zero Q
          simpa [totalLocalKummer, hxzero, hxone, Q] using h

/-- The FIRST COORDINATE of every class in the existing local
Kummer image at 2 has even integer valuation on the actual
Q_2 square-class quotient. -/
theorem cmQ2LocalKummerImage_firstParity_zero
    (c : PadicSquareClass 2 × PadicSquareClass 2)
    (hc : c ∈ LocalKummerImage 2) :
    cmQ2SquareClassValuationParity c.1 = 0 := by
  rcases hc with ⟨P, rfl⟩
  exact cmQ2TotalLocalKummer_firstParity_zero P

/-- Same local-image obstruction as a literal set inclusion. -/
theorem cmQ2LocalKummerImage_subset_evenFirst :
    LocalKummerImage 2 ⊆
      {c : PadicSquareClass 2 × PadicSquareClass 2 |
        cmQ2SquareClassValuationParity c.1 = 0} := by
  intro c hc
  exact cmQ2LocalKummerImage_firstParity_zero c hc

/-- The ACTUAL all-place explicit Selmer subgroup inherits the
proved p=2 local-image obstruction. This is a theorem on the
original subgroup, not a finite candidate-code surrogate. -/
theorem cmExplicitTwoSelmer_localQ2FirstParity_zero
    (s : explicitTwoSelmerSubgroup) :
    cmQ2SquareClassValuationParity
      (localizeKummerPair 2 (s : RatSquareClass × RatSquareClass)).1 = 0 := by
  have hsel : (s : RatSquareClass × RatSquareClass) ∈
      ExplicitTwoSelmerIntersection := s.property
  have hloc := hsel.2 (⟨2, by norm_num⟩ : Nat.Primes)
  exact cmQ2LocalKummerImage_firstParity_zero
    (localizeKummerPair 2 (s : RatSquareClass × RatSquareClass)) hloc


/-- The integer valuation parity of the localization of an ORIGINAL
rational square class is its ORIGINAL global squareClassV2Parity.
This is the genuine rational-to-Q_2 commuting square on the
actual quotient objects, not on the finite 16-code approximation. -/
theorem cmQ2SquareClassParity_localize_rational
    (c : RatSquareClass) :
    ((cmQ2SquareClassValuationParity (localizeSquareClass 2 c) : ℤ) :
        ZMod 2) =
      squareClassV2Parity c := by
  refine Quotient.inductionOn c ?_
  intro a
  change
    (((((a : ℚ) : ℚ_[2]).valuation % 2 : ℤ) : ZMod 2) =
      (padicValRat 2 (a : ℚ) : ZMod 2)
  rw [Padic.valuation_ratCast]
  exact ZMod.intCast_mod _ _

/-- The original global explicit two-Selmer subgroup has even
first-coordinate rational 2-adic parity. This theorem uses the ACTUAL
all-place local Kummer image and the exact rational-to-Q_2 valuation
commuting square, not finite candidate enumeration. -/
theorem cmExplicitTwoSelmer_firstRationalV2Parity_zero
    (s : explicitTwoSelmerSubgroup) :
    squareClassV2Parity
      ((s : RatSquareClass × RatSquareClass).1) = 0 := by
  have hlocal := cmExplicitTwoSelmer_localQ2FirstParity_zero s
  change
    cmQ2SquareClassValuationParity
      (localizeSquareClass 2
        ((s : RatSquareClass × RatSquareClass).1)) = 0 at hlocal
  have hnat :=
    cmQ2SquareClassParity_localize_rational
      ((s : RatSquareClass × RatSquareClass).1)
  rw [hlocal] at hnat
  simpa using hnat.symm


/-- The combined maximum-cut necessary conditions hold on the ORIGINAL
global explicit two-Selmer subgroup (not the 16-code model):
the two actual rational square classes have equal real sign, and
the first has even rational 2-adic valuation. -/
theorem cmExplicitTwoSelmer_realSign_and_firstV2Parity_zero
    (s : explicitTwoSelmerSubgroup) :
    squareClassSignBit
      ((s : RatSquareClass × RatSquareClass).1) =
        squareClassSignBit
          ((s : RatSquareClass × RatSquareClass).2)
    ∧
    squareClassV2Parity
      ((s : RatSquareClass × RatSquareClass).1) = 0 := by
  have hreal :
      realKummerLocalization (s : RatSquareClass × RatSquareClass) ∈
        RealKummerImage := s.property.1
  change
    squareClassSignBit ((s : RatSquareClass × RatSquareClass).1) =
      squareClassSignBit ((s : RatSquareClass × RatSquareClass).2)
    at hreal
  exact ⟨hreal, cmExplicitTwoSelmer_firstRationalV2Parity_zero s⟩

end Synthesis.Millennium.BSD
