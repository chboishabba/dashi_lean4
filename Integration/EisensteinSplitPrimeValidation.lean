import Integration.EisensteinSplitPrimeExact

namespace Dashi.EisensteinSplitPrimeValidation

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeExact

/-- Every prime in the split residue class has a literal Eisenstein norm-p
witness on the same standard quadratic-algebra carrier. -/
example (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ z : EisensteinQA, QuadraticAlgebra.norm z = p :=
  split_prime_has_norm_witness p hp hmod

/-- Coordinate version used by the geometric representation counter. -/
example (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : Int, eisensteinNorm a b = p :=
  split_prime_has_coordinate_witness p hp hmod

/-- Concrete split-prime smoke tests. -/
example : ∃ a b : Int, eisensteinNorm a b = 7 := by
  exact split_prime_has_coordinate_witness 7 (by norm_num) (by norm_num)

example : ∃ a b : Int, eisensteinNorm a b = 13 := by
  exact split_prime_has_coordinate_witness 13 (by norm_num) (by norm_num)

end Dashi.EisensteinSplitPrimeValidation
