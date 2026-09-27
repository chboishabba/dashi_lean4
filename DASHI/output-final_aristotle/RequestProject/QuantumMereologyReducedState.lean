import RequestProject.QuantumMereologySchwingerObjective
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite bipartite reduced density matrices

This begins paying the analytic producer behind Carroll--Singh linear entropy.

For finite subsystem index types A and B, define the partial trace over B by

  (Tr_B rho) i j = sum_b rho (i,b) (j,b).

DASHI proves trace preservation and Hermitian preservation directly. Positive
semidefinite preservation is intentionally left as an explicit authority leaf
rather than being smuggled into the definition.

The resulting linear entropy is the source formula 1 - Tr(rho_A^2).
-/

namespace QuantumMereology

open scoped BigOperators

namespace ReducedState

variable
  {A B : Type*}
  [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def partialTraceRight
    (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix A A ℂ :=
  fun i j => ∑ b : B, rho (i, b) (j, b)

theorem trace_partialTraceRight
    (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight rho) =
      Matrix.trace rho := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

theorem isHermitian_partialTraceRight
    {rho : Matrix (A × B) (A × B) ℂ}
    (h : rho.IsHermitian) :
    (partialTraceRight rho).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [partialTraceRight, map_sum, h.apply]


def rightBlock
    (rho : Matrix (A × B) (A × B) ℂ)
    (b : B) :
    Matrix A A ℂ :=
  rho.submatrix (fun i => (i, b)) (fun j => (j, b))

theorem partialTraceRight_eq_sum_rightBlock
    (rho : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight rho =
      ∑ b : B, rightBlock rho b := by
  ext i j
  simp [partialTraceRight, rightBlock]

theorem finset_sum_posSemidef
    {s : Finset B}
    {M : B → Matrix A A ℂ}
    (hM : ∀ b ∈ s, (M b).PosSemidef) :
    (∑ b ∈ s, M b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.not_mem_empty, Finset.sum_empty]
      exact Matrix.PosSemidef.zero
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb]
      exact (hM b (by simp)).add
        (ih (fun x hx => hM x (by simp [hx])))

theorem posSemidef_partialTraceRight
    {rho : Matrix (A × B) (A × B) ℂ}
    (h : rho.PosSemidef) :
    (partialTraceRight rho).PosSemidef := by
  rw [partialTraceRight_eq_sum_rightBlock]
  simpa only [Finset.sum_univ] using
    finset_sum_posSemidef
      (s := Finset.univ)
      (M := rightBlock rho)
      (fun b _ => h.submatrix (fun i => (i, b)))

/-- Finite density-matrix payload. Positivity and trace-one are actual
mathematical conditions, not status labels. -/
structure DensityMatrix (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : Matrix I I ℂ
  positive : matrix.PosSemidef
  traceOne : Matrix.trace matrix = 1

namespace DensityMatrix

theorem isHermitian
    {I : Type*} [Fintype I] [DecidableEq I]
    (rho : DensityMatrix I) :
    rho.matrix.IsHermitian :=
  rho.positive.isHermitian

end DensityMatrix

/-- A reduced density candidate whose only unpaid density-matrix law is
positive-semidefinite preservation of the partial trace. -/
def partialTraceDensityRight
    (rho : DensityMatrix (A × B)) :
    DensityMatrix A where
  matrix := partialTraceRight rho.matrix
  positive := posSemidef_partialTraceRight rho.positive
  traceOne := by
    rw [trace_partialTraceRight]
    exact rho.traceOne

/-- Source linear entropy on a finite reduced density matrix. For a genuine
density matrix the trace is real; this definition takes the real part explicitly
at the matrix-computation boundary. -/
def linearEntropy
    {I : Type*} [Fintype I] [DecidableEq I]
    (rho : DensityMatrix I) : ℝ :=
  1 - Complex.re (Matrix.trace (rho.matrix * rho.matrix))

theorem linearEntropy_eq_source_formula
    {I : Type*} [Fintype I] [DecidableEq I]
    (rho : DensityMatrix I) :
    linearEntropy rho =
      1 - Complex.re (Matrix.trace (rho.matrix * rho.matrix)) :=
  rfl

structure Boundary where
  partialTraceDefinitionProvesPositivity : Bool := true
  reducedDensityCreatesTimeEvolution : Bool := false
  linearEntropyFormulaCreatesSecondDerivative : Bool := false
  finiteDensityMatrixIsEmpiricalQuantumState : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem partial_trace_positivity_is_paid :
    canonicalBoundary.partialTraceDefinitionProvesPositivity = true := rfl

theorem entropy_formula_does_not_create_time_derivative :
    canonicalBoundary.linearEntropyFormulaCreatesSecondDerivative = false := rfl

end ReducedState

def mathlibReducedStateTheoremSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0 finite Matrix trace/Hermitian/PosSemidef infrastructure"
  claim := "Supplies Matrix.trace, Matrix.IsHermitian, Matrix.PosSemidef and finite-sum infrastructure consumed by the DASHI partial-trace construction."

def dashiFinitePartialTraceTheoremReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "Defines finite bipartite partial trace and proves trace, Hermitian, and positive-semidefinite preservation, yielding a concrete reduced density matrix."

end QuantumMereology
