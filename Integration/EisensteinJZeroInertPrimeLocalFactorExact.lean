import Integration.EisensteinCharacterLocalFactorsExact
import Integration.EisensteinJZeroInertFiniteFieldExact
import Mathlib.Data.ZMod.Basic

/-!
# Same-prime inert Eisenstein arithmetic -> j=0 local Euler factor

This is the first literal same-prime arithmetic/elliptic weld in the original
Eisenstein thread.

For a rational prime `p > 2` with `p % 3 = 2`:

* the repo's exact `chi_-3` arithmetic classifies the prime as inert by
  `chiMinus3Int p = -1`;
* `F_p = ZMod p` has cardinality `p = 3*(p/3)+2`;
* the generic finite-field j=0 theorem therefore gives
  `#E(F_p)=p+1` and Frobenius trace `a_p=0` for `E:y^2=x^3+1`;
* the local elliptic Euler polynomial has trace-zero shape `1+p*T^2`.

This does not yet produce the split-prime trace formula, a Hecke character, or
the global elliptic L-function.
-/

namespace Integration.EisensteinJZeroInertPrimeLocalFactorExact

open Dashi.EisensteinLatticeCounting
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroInertFiniteFieldExact

/-- Literal character value on the same rational prime. -/
theorem chiMinus3Int_eq_neg_one_of_mod_three_eq_two
    (p : Nat) (hp3 : p % 3 = 2) :
    chiMinus3Int p = -1 := by
  simp [chiMinus3Int, hp3]

private theorem prime_card_three_mul_add_two
    (p : Nat) (hp3 : p % 3 = 2) :
    Fintype.card (ZMod p) = 3 * (p / 3) + 2 := by
  rw [ZMod.card]
  have hdiv := Nat.mod_add_div p 3
  omega

private theorem prime_field_char_ne_two
    (p : Nat) (hp2 : 2 < p) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

/-- Every inert rational prime `p = 2 mod 3`, away from 2, gives trace zero on
`y^2=x^3+1` over `F_p`. -/
theorem jZeroInertPrime_trace_zero
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    jZeroFrobeniusTraceInt (ZMod p) = 0 := by
  exact jZeroTrace_eq_zero_of_card_eq_three_mul_add_two
    (F := ZMod p) (p / 3)
    (prime_card_three_mul_add_two p hp3)
    (prime_field_char_ne_two p hp2)

/-- Projective point count on the same inert prime field. -/
theorem jZeroInertPrime_pointCount
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    jZeroProjectivePointCountInt (ZMod p) = (p : Int) + 1 := by
  have hq := prime_card_three_mul_add_two p hp3
  have hchar := prime_field_char_ne_two p hp2
  rw [jZeroProjectivePointCount_eq_card_add_one (F := ZMod p) hchar
    (cubeMap_bijective_of_card_eq_three_mul_add_two (F := ZMod p) (p / 3) hq)]
  simp [ZMod.card]

/-- Same-prime local elliptic Euler polynomial on the inert branch. -/
theorem jZeroInertPrime_localEulerPolynomial
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) (T : Int) :
    1 - jZeroFrobeniusTraceInt (ZMod p) * T + (p : Int) * T ^ 2
      = 1 + (p : Int) * T ^ 2 := by
  rw [jZeroInertPrime_trace_zero p hp2 hp3]
  ring

/-- Same prime, two consumers: inert arithmetic character and trace-zero curve.
This is not a proof that the degree-one Dirichlet local factor is the degree-two
elliptic Euler factor. -/
structure InertPrimeArithmeticEllipticWeld (p : Nat) [Fact p.Prime] where
  greaterThanTwo : 2 < p
  modThree : p % 3 = 2
  arithmeticCharacter : chiMinus3Int p = -1
  ellipticTrace : jZeroFrobeniusTraceInt (ZMod p) = 0

/-- Canonical weld from the explicit same-prime hypotheses. -/
def inertPrimeArithmeticEllipticWeld
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    InertPrimeArithmeticEllipticWeld p where
  greaterThanTwo := hp2
  modThree := hp3
  arithmeticCharacter := chiMinus3Int_eq_neg_one_of_mod_three_eq_two p hp3
  ellipticTrace := jZeroInertPrime_trace_zero p hp2 hp3

structure InertPrimeLocalFactorBoundary : Prop where
  sameRationalPrimePaid : True
  chiMinus3InertClassificationPaid : True
  primeFieldCardinalityBridgePaid : True
  cubeBijectionPaid : True
  jZeroTraceZeroPaid : True
  inertEllipticEulerShapePaid : True
  dirichletLocalFactorIdentifiedWithEllipticFactor : False
  splitPrimeTraceFormulaPaid : False
  heckeCharacterPaid : False
  globalEllipticLFunctionPaid : False

end Integration.EisensteinJZeroInertPrimeLocalFactorExact
