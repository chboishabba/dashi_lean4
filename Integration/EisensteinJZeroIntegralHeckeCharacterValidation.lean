import Integration.EisensteinJZeroIntegralHeckeCharacterExact

namespace Integration.EisensteinJZeroIntegralHeckeCharacterValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroIntegralHeckeCharacterExact

example : integralHeckeCharacter (1 : HeckeIdealMonoid) = 1 := by
  exact MonoidHom.map_one integralHeckeCharacter

example (I J : HeckeIdealMonoid) :
    integralHeckeCharacter (I * J) =
      integralHeckeCharacter I * integralHeckeCharacter J := by
  exact MonoidHom.map_mul integralHeckeCharacter I J

example (I : HeckeIdealMonoid) :
    Ideal.span ({integralHeckeCharacter I} : Set EisensteinQA) = I.1 :=
  integralHeckeCharacter_spans I

example (I : HeckeIdealMonoid) :
    Integration.EisensteinJZeroHeckeConductorExact.CongruentModHeckeConductor
      (integralHeckeCharacter I) 1 :=
  integralHeckeCharacter_congruent_one I

end Integration.EisensteinJZeroIntegralHeckeCharacterValidation
