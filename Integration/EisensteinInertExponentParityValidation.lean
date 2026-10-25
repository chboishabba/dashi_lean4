import Integration.EisensteinInertExponentParityExact

namespace Dashi.EisensteinInertExponentParityValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinInertExponentParityExact

example (z : EisensteinQA) (n p : Nat)
    (hn : 0 < n) (hz : QuadraticAlgebra.norm z = n)
    (hp : p.Prime) (hmod : p % 3 = 2) :
    Even (n.factorization p) :=
  represented_norm_has_even_inert_exponent z n p hn hz hp hmod

end Dashi.EisensteinInertExponentParityValidation
