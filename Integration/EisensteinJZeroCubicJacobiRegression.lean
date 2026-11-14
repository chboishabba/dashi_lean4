import Integration.EisensteinJZeroCubicJacobiExact

/-!
RED-first regression for the split-side finite-field compiler.

The certificate is deliberately finite-field/cubic-character data.  It is not
called a Hecke character and does not identify the resulting Jacobi sum with an
Eisenstein prime until a separate arithmetic producer is supplied.
-/

namespace Integration.EisensteinJZeroCubicJacobiRegression

open Integration.EisensteinJZeroCubicJacobiExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

example (hchar : ringChar F ≠ 2) (cert : CubicCharacterCertificate F) :
    ((Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt F : Int) : ℂ)
      = cubicJacobiTrace cert :=
  jZeroTrace_cast_eq_cubicJacobiTrace hchar cert

example (cert : CubicCharacterCertificate F) :
    finiteFieldCubicCharacterPaid cert = true := rfl

example (cert : CubicCharacterCertificate F) :
    heckeCharacterManufactured cert = false := rfl

end Integration.EisensteinJZeroCubicJacobiRegression
