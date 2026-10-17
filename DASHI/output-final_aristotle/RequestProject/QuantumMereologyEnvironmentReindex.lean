import RequestProject.QuantumMereologyFiniteNChartedAtlas

/-!
# Environment-reindex invariance of finite partial trace

Partial trace should not depend on how the discarded environment basis is
labelled.  This module proves that exact finite statement: reindexing only the
environment coordinate along an equivalence `B ≃ C` leaves the retained `A`
reduced matrix unchanged.

This is a real chart-independence payment, but a deliberately narrow one.  It
does not prove invariance under arbitrary charts that also alter the retained
subsystem coordinates or mix retained/environment factors.
-/

namespace QuantumMereology
namespace EnvironmentReindex

variable
  {A B C : Type*}
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Reindex only the environment coordinate. -/
def environmentEquiv (e : B ≃ C) : (A × B) ≃ (A × C) where
  toFun x := (x.1, e x.2)
  invFun x := (x.1, e.symm x.2)
  left_inv x := by rcases x with ⟨a, b⟩; simp
  right_inv x := by rcases x with ⟨a, c⟩; simp

/-- Exact finite theorem: tracing the environment is invariant under an exact
relabeling of that environment. -/
theorem partialTraceRight_reindex_environment
    (e : B ≃ C)
    (rho : Matrix (A × B) (A × B) ℂ) :
    ReducedState.partialTraceRight
      (Matrix.reindex (environmentEquiv e) (environmentEquiv e) rho) =
    ReducedState.partialTraceRight rho := by
  classical
  ext i j
  simp only [ReducedState.partialTraceRight, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simpa [environmentEquiv] using
    e.symm.sum_comp (fun b : B => rho (i, b) (j, b))

/-- Density-matrix wrapper around environment relabeling. -/
noncomputable def reindexEnvironmentDensity
    (e : B ≃ C)
    (rho : ReducedState.DensityMatrix (A × B)) :
    ReducedState.DensityMatrix (A × C) :=
  FiniteNChartedAtlas.reindexDensity (environmentEquiv e) rho

/-- The reduced density-matrix payload is unchanged by environment relabeling. -/
theorem partialTraceDensityRight_reindex_environment_matrix
    (e : B ≃ C)
    (rho : ReducedState.DensityMatrix (A × B)) :
    (ReducedState.partialTraceDensityRight
      (reindexEnvironmentDensity e rho)).matrix =
    (ReducedState.partialTraceDensityRight rho).matrix := by
  exact partialTraceRight_reindex_environment e rho.matrix

structure Boundary where
  environmentRelabelingInvariancePaid : Bool := true
  densityReductionEnvironmentRelabelingPaid : Bool := true
  arbitraryRetainedCoordinateChartIndependencePaid : Bool := false
  retainedEnvironmentMixingChartIndependencePaid : Bool := false
  physicalTPSChartIndependencePaid : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem environment_relabeling_invariance_paid :
    canonicalBoundary.environmentRelabelingInvariancePaid = true := rfl

theorem arbitrary_retained_chart_independence_open :
    canonicalBoundary.arbitraryRetainedCoordinateChartIndependencePaid = false := rfl

/-- DASHI theorem receipt. -/
def dashiEnvironmentReindexReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Proves that exact finite partial trace is invariant under any equivalence that only relabels the discarded environment coordinate, and lifts the statement to density-matrix reductions. This does not establish arbitrary retained-coordinate or retained/environment-mixing chart independence, nor physical TPS identification."

end EnvironmentReindex
end QuantumMereology
