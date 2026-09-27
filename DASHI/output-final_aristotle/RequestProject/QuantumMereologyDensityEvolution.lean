import RequestProject.QuantumMereologyReducedState
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Finite unitary density-matrix evolution

For a finite matrix state rho and a unitary matrix U, evolve by

  rho' = U * rho * Uᴴ.

This is standard finite-dimensional quantum mechanics. The unitary-group and
matrix positivity/trace facts are mathlib theorem sources. DASHI owns only the
packaging and transport theorems below.

No source paper is credited with these local matrix theorems unless explicitly
named in an attribution receipt.
-/

namespace QuantumMereology

namespace DensityEvolution

variable
  {I : Type*}
  [Fintype I] [DecidableEq I]

def evolveMatrix
    (U : Matrix I I ℂ)
    (rho : Matrix I I ℂ) :
    Matrix I I ℂ :=
  U * rho * Uᴴ

theorem isHermitian_evolveMatrix
    {U : Matrix I I ℂ}
    {rho : Matrix I I ℂ}
    (hRho : rho.IsHermitian) :
    (evolveMatrix U rho).IsHermitian := by
  simpa [evolveMatrix] using
    Matrix.isHermitian_mul_mul_conjTranspose U hRho

theorem posSemidef_evolveMatrix
    {U : Matrix I I ℂ}
    {rho : Matrix I I ℂ}
    (hRho : rho.PosSemidef) :
    (evolveMatrix U rho).PosSemidef := by
  simpa [evolveMatrix] using
    hRho.mul_mul_conjTranspose_same U

theorem trace_evolveMatrix_of_unitary
    {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (rho : Matrix I I ℂ) :
    Matrix.trace (evolveMatrix U rho) =
      Matrix.trace rho := by
  calc
    Matrix.trace (evolveMatrix U rho)
        = Matrix.trace (Uᴴ * U * rho) := by
            simpa [evolveMatrix, Matrix.mul_assoc] using
              Matrix.trace_mul_cycle U rho Uᴴ
    _ = Matrix.trace (1 * rho) := by
          rw [(Matrix.mem_unitaryGroup_iff'.mp hU)]
    _ = Matrix.trace rho := by simp

def evolveDensity
    (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (rho : ReducedState.DensityMatrix I) :
    ReducedState.DensityMatrix I where
  matrix := evolveMatrix U rho.matrix
  positive := posSemidef_evolveMatrix rho.positive
  traceOne := by
    rw [trace_evolveMatrix_of_unitary hU rho.matrix]
    exact rho.traceOne

theorem evolveDensity_matrix
    (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (rho : ReducedState.DensityMatrix I) :
    (evolveDensity U hU rho).matrix =
      evolveMatrix U rho.matrix :=
  rfl

structure Boundary where
  arbitraryMatrixEvolutionIsUnitary : Bool := false
  unitaryConjugationCreatesPhysicalTimeParameter : Bool := false
  oneUnitaryStepCreatesHamiltonianGenerator : Bool := false
  densityEvolutionCreatesMeasurementAuthority : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem arbitrary_matrix_not_promoted_to_unitary :
    canonicalBoundary.arbitraryMatrixEvolutionIsUnitary = false := rfl

theorem unitary_step_does_not_create_time_parameter :
    canonicalBoundary.unitaryConjugationCreatesPhysicalTimeParameter = false := rfl

end DensityEvolution

def mathlibUnitaryDensityEvolutionSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Matrix.unitaryGroup / Matrix.PosSemidef / Matrix.trace_mul_cycle"
  claim := "Supplies unitary-matrix identities, positivity under conjugation, Hermitian transport, and cyclic trace identities used by the finite density-evolution owner."

def dashiUnitaryDensityEvolutionReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "Packages rho -> U rho U^† as a finite density-matrix endomorphism preserving positivity and trace for a supplied unitary U; no physical time law or Hamiltonian generator is inferred."

end QuantumMereology
