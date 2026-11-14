import Integration.EisensteinSplitConjugateNonassociateExact

namespace Dashi.EisensteinSplitConjugateNonassociateValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitConjugateNonassociateExact

example (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    ¬ Associated z (star z) :=
  split_norm_prime_not_associated_star p hp hmod z hz

end Dashi.EisensteinSplitConjugateNonassociateValidation
