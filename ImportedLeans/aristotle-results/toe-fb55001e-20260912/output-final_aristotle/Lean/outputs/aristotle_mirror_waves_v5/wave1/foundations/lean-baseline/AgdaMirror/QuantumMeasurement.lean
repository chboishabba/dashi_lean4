import AgdaMirror.OperatorTypes
import AgdaMirror.ProjectionVsInvertible

/-!
# Lean mirror of `DASHI/Algebra/Quantum/Measurement.agda` (genuine theorem)

Faithful transcription of the genuine quantum-measurement fact: a *measurement*
is a nontrivial projection (it genuinely collapses something), and therefore it
cannot be invertible.  The proof reuses the already-mirrored theorem that a
projection which is also invertible must be the identity
(`AgdaMirror.ProjectionVsInvertible.projection_invertible_identity`).
No `sorry`, axiom-clean.
-/

namespace AgdaMirror.QuantumMeasurement

open AgdaMirror.OperatorTypes
open AgdaMirror.ProjectionVsInvertible

variable {S : Type} {P : S → S}

/-- A measurement: a nontrivial projection (Agda `record Measurement`). -/
structure Measurement (P : S → S) where
  proj : Projection P
  nontrivial : Nontrivial P

/-- A genuine measurement cannot be invertible (Agda
`measurement-not-invertible`). -/
theorem measurement_not_invertible
    (M : Measurement P) : AgdaMirror.OperatorTypes.Invertible P → False := by
  intro hinv
  exact M.nontrivial (projection_invertible_identity M.proj hinv)

end AgdaMirror.QuantumMeasurement
