import Synthesis.MillenniumBSDTotalLocalKummer
import Mathlib.Tactic

/-!
# Literal all-place 2-Selmer intersection in square-class coordinates

For E : y² = x³ - x all rational 2-torsion is rational, so the standard
2-descent coordinates live in (Q*/Q*²)².  The finite local conditions are the
already-constructed literal ranges of the total Q_p Kummer maps.

This file adds the missing infinite place concretely.  Over R, an ordinary
point on y² = x(x-1)(x+1) has x and x-1 of the same sign: either x >= 1 or
-1 <= x < 0.  Hence its two square-class coordinates have equal sign bits.

We then define the literal all-place intersection:
  * equal-sign condition at infinity;
  * membership in LocalKummerImage p for every prime p.

Finally we prove that every ordinary rational Kummer point, and all four
rational 2-torsion classes, lie in that intersection.
-/

namespace Synthesis.Millennium.BSD

def realKummerLocalization :
    RatSquareClass × RatSquareClass →
      Bool × Bool :=
  fun c => (squareClassSignBit c.1, squareClassSignBit c.2)

def RealKummerImage : Set (Bool × Bool) :=
  {bits | bits.1 = bits.2}

theorem ordinaryKummer_real_local_condition
    (P : OrdinaryKummerPoint) :
    realKummerLocalization (ordinaryKummer P) ∈
      RealKummerImage := by
  change signBit P.x = signBit (P.x - 1)
  by_cases hxneg : P.x < 0
  · have hx1neg : P.x - 1 < 0 := by linarith
    simp [signBit, hxneg, hx1neg]
  · have hxnonneg : 0 ≤ P.x := le_of_not_gt hxneg
    have hxpos : 0 < P.x := by
      exact lt_of_le_of_ne hxnonneg (Ne.symm P.x_ne_zero)
    have hxge1 : 1 ≤ P.x := by
      by_contra h
      have hxlt1 : P.x < 1 := lt_of_not_ge h
      have hy2 : 0 ≤ P.y ^ 2 := sq_nonneg P.y
      nlinarith [P.onCurve]
    have hx1nonneg : ¬ P.x - 1 < 0 := by linarith
    simp [signBit, hxneg, hx1nonneg]

theorem torsionKummer_real_local_condition
    (P : RationalTwoTorsionPoint) :
    realKummerLocalization (torsionKummer P) ∈
      RealKummerImage := by
  cases P <;>
    simp [realKummerLocalization, RealKummerImage, torsionKummer,
      oneNZ, negOneNZ, twoNZ, negTwoNZ,
      signBit_one, signBit_neg_one]

structure ExplicitTwoSelmerClass where
  globalClass : RatSquareClass × RatSquareClass
  realCondition :
    realKummerLocalization globalClass ∈ RealKummerImage
  finiteCondition :
    ∀ p : Nat.Primes,
      letI : Fact p.1.Prime := ⟨p.2⟩
      localizeKummerPair p.1 globalClass ∈
        LocalKummerImage p.1

def ExplicitTwoSelmerIntersection :
    Set (RatSquareClass × RatSquareClass) :=
  {c |
    realKummerLocalization c ∈ RealKummerImage
    ∧ ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        localizeKummerPair p.1 c ∈
          LocalKummerImage p.1}

theorem explicitSelmerClass_iff_mem_intersection
    (c : ExplicitTwoSelmerClass) :
    c.globalClass ∈ ExplicitTwoSelmerIntersection := by
  exact ⟨c.realCondition, c.finiteCondition⟩

def ordinaryKummerSelmerClass
    (P : OrdinaryKummerPoint) :
    ExplicitTwoSelmerClass where
  globalClass := ordinaryKummer P
  realCondition := ordinaryKummer_real_local_condition P
  finiteCondition := by
    intro p
    letI : Fact p.1.Prime := ⟨p.2⟩
    exact localizedOrdinaryGlobalKummer_mem_localImage p.1 P

theorem ordinaryKummer_mem_explicitSelmer
    (P : OrdinaryKummerPoint) :
    ordinaryKummer P ∈ ExplicitTwoSelmerIntersection :=
  explicitSelmerClass_iff_mem_intersection
    (ordinaryKummerSelmerClass P)

theorem torsionKummer_finite_local_condition
    (P : RationalTwoTorsionPoint)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    localizeKummerPair p.1 (torsionKummer P) ∈
      LocalKummerImage p.1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  cases P with
  | infinity =>
      simpa [torsionKummer, localizeKummerPair,
        localInfinityKummer, localRationalClass]
        using localInfinity_mem_KummerImage p.1
  | zero =>
      simpa [torsionKummer, localizeKummerPair,
        localZeroKummer, localRationalClass]
        using localZero_mem_KummerImage p.1
  | one =>
      simpa [torsionKummer, localizeKummerPair,
        localOneKummer, localRationalClass]
        using localOne_mem_KummerImage p.1
  | negOne =>
      simpa [minusOne_ordinary_matches_torsion]
        using localizedOrdinaryGlobalKummer_mem_localImage
          p.1 minusOnePoint

def torsionKummerSelmerClass
    (P : RationalTwoTorsionPoint) :
    ExplicitTwoSelmerClass where
  globalClass := torsionKummer P
  realCondition := torsionKummer_real_local_condition P
  finiteCondition := torsionKummer_finite_local_condition P

theorem torsionKummer_mem_explicitSelmer
    (P : RationalTwoTorsionPoint) :
    torsionKummer P ∈ ExplicitTwoSelmerIntersection :=
  explicitSelmerClass_iff_mem_intersection
    (torsionKummerSelmerClass P)

end Synthesis.Millennium.BSD
