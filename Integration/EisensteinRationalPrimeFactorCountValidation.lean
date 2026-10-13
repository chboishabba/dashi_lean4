import Integration.EisensteinRationalPrimeFactorCountExact

namespace Dashi.EisensteinRationalPrimeFactorCountValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRationalPrimeFactorCountExact

example (n p : Nat) (hn : 0 < n) (hp : p.Prime)
    (hirr : Irreducible (p : EisensteinQA)) :
    Associates.count (Associates.mk (p : EisensteinQA))
        (Associates.mk (n : EisensteinQA)).factors
      = n.factorization p :=
  rational_prime_count_eq_factorization n p hn hp hirr

end Dashi.EisensteinRationalPrimeFactorCountValidation
