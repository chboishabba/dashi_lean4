import Integration.EisensteinJZeroInertFiniteFieldExact

/-!
RED-first regression for the inert/cardinality-mod-3 finite-field closure.
-/

namespace Integration.EisensteinJZeroInertFiniteFieldRegression

open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroInertFiniteFieldExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (k : Nat) (hq : Fintype.card F = 3 * k + 2) :
    Function.Bijective (fun x : F => x ^ 3) :=
  cubeMap_bijective_of_card_eq_three_mul_add_two k hq

example (k : Nat) (hq : Fintype.card F = 3 * k + 2)
    (hchar : ringChar F ≠ 2) :
    jZeroFrobeniusTraceInt F = 0 :=
  jZeroTrace_eq_zero_of_card_eq_three_mul_add_two k hq hchar

end Integration.EisensteinJZeroInertFiniteFieldRegression
