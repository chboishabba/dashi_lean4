import Integration.EisensteinJZeroFiniteFieldTraceExact
import Mathlib.FieldTheory.Finite.Basic

/-!
# q = 2 (mod 3) finite-field closure for the j=0 curve

For `q = #F = 3k+2`, the exponent `2k+1` is an explicit inverse to cubing:

    3(2k+1) = 2(q-1)+1.

Using Mathlib's finite-field theorem `x^(q-1)=1` for `x != 0`, this proves
that `x |-> x^3` is bijective on all of `F`.  Feeding that exact bijection into
`EisensteinJZeroFiniteFieldTraceExact` yields

    #E(F) = q+1
    a_q   = 0

for the concrete j=0 equation `y^2=x^3+1` in odd characteristic.

This is the local inert-pattern theorem at the finite-field cardinality level.
Connecting a rational prime's Eisenstein splitting class to this cardinality
condition remains a separately named arithmetic bridge; no Hecke character is
used or inferred here.
-/

namespace Integration.EisensteinJZeroInertFiniteFieldExact

open Integration.EisensteinJZeroFiniteFieldTraceExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def cubeInverseExponent (k : Nat) : Nat := 2 * k + 1

private theorem cubeExponent_identity (k : Nat)
    (hq : Fintype.card F = 3 * k + 2) :
    3 * cubeInverseExponent k = (Fintype.card F - 1) * 2 + 1 := by
  unfold cubeInverseExponent
  omega

private theorem inverseExponent_cube_identity (k : Nat)
    (hq : Fintype.card F = 3 * k + 2) :
    cubeInverseExponent k * 3 = (Fintype.card F - 1) * 2 + 1 := by
  rw [Nat.mul_comm]
  exact cubeExponent_identity (F := F) k hq

private theorem cube_then_inverse (k : Nat)
    (hq : Fintype.card F = 3 * k + 2) (x : F) :
    (x ^ 3) ^ cubeInverseExponent k = x := by
  by_cases hx : x = 0
  · simp [hx, cubeInverseExponent]
  · rw [← pow_mul, cubeExponent_identity (F := F) k hq]
    rw [pow_add, pow_mul]
    rw [FiniteField.pow_card_sub_one_eq_one x hx]
    simp

private theorem inverse_then_cube (k : Nat)
    (hq : Fintype.card F = 3 * k + 2) (x : F) :
    (x ^ cubeInverseExponent k) ^ 3 = x := by
  by_cases hx : x = 0
  · simp [hx, cubeInverseExponent]
  · rw [← pow_mul, inverseExponent_cube_identity (F := F) k hq]
    rw [pow_add, pow_mul]
    rw [FiniteField.pow_card_sub_one_eq_one x hx]
    simp

/-- If `#F = 3k+2`, cubing is a literal permutation of the finite field. -/
theorem cubeMap_bijective_of_card_eq_three_mul_add_two
    (k : Nat) (hq : Fintype.card F = 3 * k + 2) :
    Function.Bijective (fun x : F => x ^ 3) := by
  constructor
  · intro x y hxy
    calc
      x = (x ^ 3) ^ cubeInverseExponent k :=
        (cube_then_inverse (F := F) k hq x).symm
      _ = (y ^ 3) ^ cubeInverseExponent k := congrArg (fun z : F => z ^ cubeInverseExponent k) hxy
      _ = y := cube_then_inverse (F := F) k hq y
  · intro y
    refine ⟨y ^ cubeInverseExponent k, ?_⟩
    exact inverse_then_cube (F := F) k hq y

/-- The same j=0 curve has trace zero over every odd finite field of size `3k+2`. -/
theorem jZeroTrace_eq_zero_of_card_eq_three_mul_add_two
    (k : Nat) (hq : Fintype.card F = 3 * k + 2)
    (hchar : ringChar F ≠ 2) :
    jZeroFrobeniusTraceInt F = 0 :=
  jZeroFrobeniusTrace_eq_zero_of_cube_bijective F hchar
    (cubeMap_bijective_of_card_eq_three_mul_add_two (F := F) k hq)

/-- Local Euler polynomial in the trace-zero branch. -/
theorem jZeroTraceZeroLocalEulerPolynomial
    (k : Nat) (hq : Fintype.card F = 3 * k + 2)
    (hchar : ringChar F ≠ 2) (T : Int) :
    1 - jZeroFrobeniusTraceInt F * T + (Fintype.card F : Int) * T ^ 2
      = 1 + (Fintype.card F : Int) * T ^ 2 := by
  rw [jZeroTrace_eq_zero_of_card_eq_three_mul_add_two (F := F) k hq hchar]
  ring

structure JZeroInertFiniteFieldBoundary : Prop where
  explicitCubeInverseExponentPaid : True
  cubeBijectionForCardTwoModThreePaid : True
  traceZeroPaid : True
  localEulerTraceZeroShapePaid : True
  rationalPrimeToFiniteFieldCardBridgePaidHere : False
  splitPrimeTraceFormulaPaidHere : False
  heckeCharacterPaidHere : False

end Integration.EisensteinJZeroInertFiniteFieldExact
