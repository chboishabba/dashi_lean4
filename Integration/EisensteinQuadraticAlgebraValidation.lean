import Integration.EisensteinQuadraticAlgebraExact

namespace Dashi.EisensteinQuadraticAlgebraValidation

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact

example : QuadraticAlgebra.norm (asQuadraticAlgebra 2 1) = 3 := by native_decide

example (a b : Int) :
    QuadraticAlgebra.norm (asQuadraticAlgebra a b) = eisensteinNorm a b :=
  norm_asQuadraticAlgebra a b

example (a b c d : Int) :
    QuadraticAlgebra.norm (asQuadraticAlgebra a b * asQuadraticAlgebra c d)
      = eisensteinNorm a b * eisensteinNorm c d :=
  norm_product_coordinates a b c d

end Dashi.EisensteinQuadraticAlgebraValidation
