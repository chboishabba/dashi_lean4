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

example [FiniteDimensional ℝ J]
    (A : TraceUnitData J)
    (hJ : Module.finrank ℝ J = 27) :
    Module.finrank ℝ (Traceless A) = 26 :=
  traceless_finrank_eq_26 A hJ

end Integration.AlbertScalarTracelessRegression
