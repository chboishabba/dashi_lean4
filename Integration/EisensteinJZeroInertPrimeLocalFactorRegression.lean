import Integration.EisensteinJZeroInertPrimeLocalFactorExact

/-!
RED-first regression for the first literal same-prime weld between the original
Eisenstein arithmetic lane and the j=0 elliptic curve.
-/

namespace Integration.EisensteinJZeroInertPrimeLocalFactorRegression

open Dashi.EisensteinLatticeCounting
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroInertPrimeLocalFactorExact

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    chiMinus3Int p = -1 :=
  chiMinus3Int_eq_neg_one_of_mod_three_eq_two p hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    jZeroFrobeniusTraceInt (ZMod p) = 0 :=
  jZeroInertPrime_trace_zero p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) (T : Int) :
    1 - jZeroFrobeniusTraceInt (ZMod p) * T + (p : Int) * T ^ 2
      = 1 + (p : Int) * T ^ 2 :=
  jZeroInertPrime_localEulerPolynomial p hp2 hp3 T

end Integration.EisensteinJZeroInertPrimeLocalFactorRegression
