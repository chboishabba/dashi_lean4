import RequestProject.QuantumMereologyEntropyAcceleration
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Hermitian Hamiltonian exponential path

This owner makes one explicit analytic choice: the finite matrix algebra uses
mathlib's L2-operator C*-norm. With that pinned norm, a Hermitian matrix H
generates the unitary path

  U_H(t) = exp((-i t) H).

Mathlib owns the normed-star algebra and theorem
exp_mem_unitary_of_mem_skewAdjoint. DASHI owns the specialization to the
finite quantum-mereology path.

This does not yet derive dU/dt = -i H U, the von Neumann equation, or the
Carroll--Singh entropy accelerations from H.
-/

namespace QuantumMereology

open scoped Matrix.Norms.L2Operator

namespace HamiltonianExponential

variable
  {I : Type*}
  [Fintype I] [DecidableEq I]

def generator
    (H : Matrix I I ℂ)
    (t : ℝ) :
    Matrix I I ℂ :=
  ((-(t : ℂ)) * Complex.I) • H

theorem generator_mem_skewAdjoint
    {H : Matrix I I ℂ}
    (hH : H.IsHermitian)
    (t : ℝ) :
    generator H t ∈ skewAdjoint (Matrix I I ℂ) := by
  apply hH.isSelfAdjoint.smul_mem_skewAdjoint
  simp [generator, skewAdjoint.mem_iff, mul_comm, mul_left_comm, mul_assoc]

noncomputable def U
    (H : Matrix I I ℂ)
    (t : ℝ) :
    Matrix I I ℂ :=
  NormedSpace.exp (generator H t)

theorem U_mem_unitary
    {H : Matrix I I ℂ}
    (hH : H.IsHermitian)
    (t : ℝ) :
    U H t ∈ Matrix.unitaryGroup I ℂ := by
  exact exp_mem_unitary_of_mem_skewAdjoint
    (generator_mem_skewAdjoint hH t)

@[simp] theorem U_zero
    (H : Matrix I I ℂ) :
    U H 0 = 1 := by
  simp [U, generator]

noncomputable def unitaryPath
    (H : Matrix (I × I) (I × I) ℂ)
    (hH : H.IsHermitian) :
    EntropyAcceleration.UnitaryPath (A := I) (B := I) where
  U := U H
  unitary := U_mem_unitary hH

structure Boundary where
  exponentialPathProvesSchrodingerDerivative : Bool := false
  exponentialPathProvesVonNeumannEquation : Bool := false
  exponentialPathComputesEntropyAcceleration : Bool := false
  hermitianMatrixIsEmpiricallyMeasuredHamiltonian : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem exponential_path_does_not_compute_entropy_acceleration :
    canonicalBoundary.exponentialPathComputesEntropyAcceleration = false := rfl

theorem hermitian_matrix_not_empirical_hamiltonian_authority :
    canonicalBoundary.hermitianMatrixIsEmpiricallyMeasuredHamiltonian = false := rfl

end HamiltonianExponential

def mathlibHamiltonianExponentialSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Matrix.Norms.L2Operator / exp_mem_unitary_of_mem_skewAdjoint"
  claim := "Supplies the pinned finite matrix C*-norm and the theorem that exponentials of skew-adjoint elements are unitary."

def dashiHamiltonianExponentialReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "Specialises the skew-adjoint exponential theorem to (-i t) times a Hermitian finite matrix and packages the resulting unitary path without deriving time derivatives, entropy accelerations, or empirical Hamiltonian authority."

end QuantumMereology
