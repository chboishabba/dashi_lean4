import Integration.AlbertScalarTraceless

namespace Integration.AlbertScalarTracelessRegression

open Integration.AlbertScalarTraceless

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

example (A : TraceUnitData J) : scalarCoeff A A.unit = 1 :=
  scalarCoeff_unit A

example (A : TraceUnitData J) (x : J) :
    A.trace (tracelessPart A x) = 0 :=
  trace_tracelessPart A x

example (A : TraceUnitData J) (x : J) :
    scalarPart A x + tracelessPart A x = x :=
  scalar_plus_traceless A x

example (A : TraceUnitData J) :
    J ≃ₗ[ℝ] ℝ × Traceless A :=
  scalarTracelessEquiv A

end Integration.AlbertScalarTracelessRegression
