import Integration.RationalOctonionDivisionNorm

namespace Integration.RationalOctonionDivisionNormRegression

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalCayleyDicksonOctonion.RationalOctonion

example (x : RationalOctonion) : normSq x = 0 ↔ x = 0 :=
  normSq_eq_zero_iff

example (x : RationalOctonion) (hx : x ≠ 0) : normSq x ≠ 0 :=
  normSq_ne_zero hx

example (x y : RationalOctonion) (hxy : x * y = 0) : x = 0 ∨ y = 0 :=
  mul_eq_zero hxy

example (x y : RationalOctonion) (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 :=
  mul_ne_zero hx hy

end Integration.RationalOctonionDivisionNormRegression
