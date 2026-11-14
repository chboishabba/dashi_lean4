import Integration.EisensteinJZeroFiniteFieldTraceExact

/-!
RED-first regression for the first same-curve local Euler-factor payment.
-/

namespace Integration.EisensteinJZeroFiniteFieldTraceRegression

open Integration.EisensteinJZeroFiniteFieldTraceExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    jZeroFrobeniusTraceInt F = 0 :=
  jZeroFrobeniusTrace_eq_zero_of_cube_bijective hchar hcube

example (hchar : ringChar F ≠ 2)
    (hcube : Function.Bijective (fun x : F => x ^ 3)) :
    jZeroProjectivePointCountInt F = (Fintype.card F : Int) + 1 :=
  jZeroProjectivePointCount_eq_card_add_one hchar hcube

end Integration.EisensteinJZeroFiniteFieldTraceRegression
