import Integration.EisensteinConjugateFactorCountExact

namespace Dashi.EisensteinConjugateFactorCountValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinConjugateFactorCountExact

example (q z : EisensteinQA) (hq : Irreducible q) (hz : z ≠ 0) :
    Associates.count (Associates.mk q)
        (Associates.mk (star z)).factors
      = Associates.count (Associates.mk (star q))
        (Associates.mk z).factors :=
  conjugate_prime_count z hz q hq

example (a b : EisensteinQA) :
    star a ∣ star b ↔ a ∣ b :=
  star_dvd_star_iff a b

end Dashi.EisensteinConjugateFactorCountValidation
