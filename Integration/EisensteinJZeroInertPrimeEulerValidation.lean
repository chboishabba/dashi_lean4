import Integration.EisensteinJZeroInertPrimeEulerExact

namespace Dashi.EisensteinJZeroInertPrimeEulerValidation

open Dashi.EisensteinJZeroInertPrimeEulerExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) :=
  cubeMap_bijective p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    Fintype.card (JZeroAffinePoint p) = p :=
  affinePointCount_inert p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroProjectivePointCount p = p + 1 :=
  projectivePointCount_inert p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroFrobeniusTrace p = 0 :=
  frobeniusTrace_inert p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroLocalEulerPolynomial p = (1, 0, (p : Int)) :=
  localEulerPolynomial_inert p hmod

end Dashi.EisensteinJZeroInertPrimeEulerValidation
