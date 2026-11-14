import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Finite-field trace compiler for the j=0 curve

For a finite field `F` of odd characteristic, consider

    E : y^2 = x^3 + 1.

Mathlib already proves:

* the number of square roots of `a` is `quadraticChar F a + 1`;
* the total quadratic-character sum over `F` is zero.

The first theorem below gives the general finite-field trace formula

    a_q = - sum_x chi_2(x^3+1).

If the cube map `x |-> x^3` is bijective, reindexing first by the cube map and
then by translation `t |-> t+1` makes that character sum vanish.  Therefore
`#E(F)=#F+1` and the trace is zero.

The arithmetic specialisation `p = 2 mod 3 -> cube map bijective on F_p` is a
separate bridge, so finite-field geometry is not allowed to infer prime
splitting by name.
-/

namespace Integration.EisensteinJZeroFiniteFieldTraceExact

open scoped BigOperators
open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Integer-valued affine point count for `y^2=x^3+1`. -/
def jZeroAffinePointCountInt : Int :=
  ∑ x : F, ({y : F | y ^ 2 = x ^ 3 + 1}.toFinset.card : Int)

/-- Projective point count obtained by adding the unique point at infinity. -/
def jZeroProjectivePointCountInt : Int :=
  jZeroAffinePointCountInt F + 1

/-- `q+1-#E(F_q)` for the concrete j=0 model. -/
def jZeroFrobeniusTraceInt : Int :=
  (Fintype.card F : Int) + 1 - jZeroProjectivePointCountInt F

/-- General odd-characteristic trace formula for the concrete j=0 equation. -/
theorem jZeroFrobeniusTrace_eq_neg_quadraticCharSum
    (hchar : ringChar F ≠ 2) :
    jZeroFrobeniusTraceInt F =
      - ∑ x : F, quadraticChar F (x ^ 3 + 1) := by
  have haff :
      jZeroAffinePointCountInt F =
        (Fintype.card F : Int) + ∑ x : F, quadraticChar F (x ^ 3 + 1) := by
    unfold jZeroAffinePointCountInt
    calc
      (∑ x : F, ({y : F | y ^ 2 = x ^ 3 + 1}.toFinset.card : Int))
          = ∑ x : F, (quadraticChar F (x ^ 3 + 1) + 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact quadraticChar_card_sqrts hchar (x ^ 3 + 1)
      _ = (∑ x : F, quadraticChar F (x ^ 3 + 1)) + ∑ _x : F, (1 : Int) := by
            rw [Finset.sum_add_distrib]
      _ = (Fintype.card F : Int) + ∑ x : F, quadraticChar F (x ^ 3 + 1) := by
            simp [add_comm]
  unfold jZeroFrobeniusTraceInt jZeroProjectivePointCountInt
  rw [haff]
  ring

private lemma translation_add_one_bijective :
    Function.Bijective (fun x : F => x + 1) := by
  constructor
  · intro x y h
    exact add_right_cancel h
  · intro y
    refine ⟨y - 1, ?_⟩
    ring

/-- Reindex the quadratic-character sum through cube and translation. -/
theorem quadraticChar_cubicShift_sum_zero
    (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    ∑ x : F, quadraticChar F (x ^ 3 + 1) = 0 := by
  calc
    (∑ x : F, quadraticChar F (x ^ 3 + 1))
        = ∑ t : F, quadraticChar F (t + 1) := by
          simpa using hcube.sum_comp (fun t : F => quadraticChar F (t + 1))
    _ = ∑ u : F, quadraticChar F u := by
          simpa using (translation_add_one_bijective F).sum_comp (quadraticChar F)
    _ = 0 := quadraticChar_sum_zero hchar

/-- Under cube bijectivity the affine j=0 equation has exactly `#F` points. -/
theorem jZeroAffinePointCount_eq_card
    (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    jZeroAffinePointCountInt F = (Fintype.card F : Int) := by
  unfold jZeroAffinePointCountInt
  calc
    (∑ x : F, ({y : F | y ^ 2 = x ^ 3 + 1}.toFinset.card : Int))
        = ∑ x : F, (quadraticChar F (x ^ 3 + 1) + 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact quadraticChar_card_sqrts hchar (x ^ 3 + 1)
    _ = (∑ x : F, quadraticChar F (x ^ 3 + 1)) + ∑ _x : F, (1 : Int) := by
          rw [Finset.sum_add_distrib]
    _ = (Fintype.card F : Int) := by
          rw [quadraticChar_cubicShift_sum_zero F hchar hcube]
          simp

/-- Under cube bijectivity the projective j=0 curve has `q+1` points. -/
theorem jZeroProjectivePointCount_eq_card_add_one
    (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    jZeroProjectivePointCountInt F = (Fintype.card F : Int) + 1 := by
  unfold jZeroProjectivePointCountInt
  rw [jZeroAffinePointCount_eq_card F hchar hcube]

/-- Same-curve local Frobenius trace is zero whenever the cube map is bijective. -/
theorem jZeroFrobeniusTrace_eq_zero_of_cube_bijective
    (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    jZeroFrobeniusTraceInt F = 0 := by
  rw [jZeroFrobeniusTrace_eq_neg_quadraticCharSum F hchar,
    quadraticChar_cubicShift_sum_zero F hchar hcube]
  simp

/-- The exact local Euler polynomial therefore has the trace-zero shape
`1 + q*T^2`; identifying a particular prime as satisfying cube bijectivity is
kept separate. -/
def traceZeroLocalEulerPolynomial (q : Int) (T : Int) : Int :=
  1 + q * T ^ 2

structure JZeroFiniteFieldTraceBoundary : Prop where
  quadraticCharacterSquareRootCountUsed : True
  generalQuadraticCharacterTraceFormulaPaid : True
  cubeReindexingUsed : True
  projectivePointAtInfinityAdded : True
  traceZeroFromCubeBijectionPaid : True
  primeModThreeImpliesCubeBijectionPaidHere : False
  splitPrimeTraceFormulaPaidHere : False
  heckeCharacterPaidHere : False

end Integration.EisensteinJZeroFiniteFieldTraceExact
