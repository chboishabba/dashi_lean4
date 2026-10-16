import RequestProject.QuantumMereologyVonNeumannInformation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Charted finite-N same-global-state information atlas

The tripartite owner proves a literal three-factor atlas on `(A × B) × C`.
This module advances the finite-N direction without pretending that the current
repo already owns a heterogeneous selected-TPS tensor compiler.

For a homogeneous finite carrier `(Fin n → Fin d)`, a `PairChart i j` is an
explicit equivalence

  global basis ≃ (selected pair basis) × environment basis

whose first two coordinates are proved to be the declared factors `i,j`.
Given a family of such charts and one global density matrix, DASHI reindexes
that SAME density matrix, traces only the chart environment, and obtains a
genuine density matrix for every declared ordered pair.  Mutual-information
weights are therefore derived from one global state, not independently supplied
pair states.

The chart family is explicit proof data.  This owner does not claim that an
arbitrary heterogeneous physical TPS supplies such charts automatically, nor
does it prove chart-independence/overlap coherence for unrelated chart choices.
Those remain the next selected-TPS attachment/coherence payments.
-/

namespace QuantumMereology
namespace FiniteNChartedAtlas

open scoped BigOperators

abbrev GlobalIndex (n d : ℕ) := Fin n → Fin d
abbrev PairIndex (d : ℕ) := Fin d × Fin d

/-- Reindex a finite density matrix along an exact basis equivalence. -/
noncomputable def reindexDensity
    {I J : Type*}
    [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (e : I ≃ J)
    (rho : ReducedState.DensityMatrix I) :
    ReducedState.DensityMatrix J where
  matrix := Matrix.reindex e e rho.matrix
  positive := by
    rw [Matrix.reindex_apply]
    exact rho.positive.submatrix e.symm
  traceOne := by
    have htrace :
        Matrix.trace (Matrix.reindex e e rho.matrix) =
          Matrix.trace rho.matrix := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply]
      simpa using e.symm.sum_comp (fun i => rho.matrix i i)
    rw [htrace]
    exact rho.traceOne

/-- Exact finite basis chart exposing one ordered factor pair and an environment.
The coordinate laws prevent a merely cardinality-matched equivalence from being
mislabelled as the requested physical/subsystem pair. -/
structure PairChart (n d : ℕ) (i j : Fin n) where
  Env : Type
  envFintype : Fintype Env
  envDecidableEq : DecidableEq Env
  split : GlobalIndex n d ≃ (PairIndex d × Env)
  leftCoordinate : ∀ x, (split x).1.1 = x i
  rightCoordinate : ∀ x, (split x).1.2 = x j

/-- One same global finite density state plus a chart for every distinct ordered
factor pair. -/
structure Atlas (n d : ℕ) where
  global : ReducedState.DensityMatrix (GlobalIndex n d)
  chart : ∀ i j : Fin n, i ≠ j → PairChart n d i j

namespace Atlas

/-- Reindex the SAME global density matrix into the selected pair/environment
chart. -/
noncomputable def chartedGlobal
    {n d : ℕ}
    (X : Atlas n d)
    (i j : Fin n)
    (hij : i ≠ j) :
    ReducedState.DensityMatrix
      (PairIndex d × (X.chart i j hij).Env) := by
  classical
  let C := X.chart i j hij
  letI : Fintype C.Env := C.envFintype
  letI : DecidableEq C.Env := C.envDecidableEq
  exact reindexDensity C.split X.global

/-- Pair density matrix obtained by tracing only the environment coordinate of
the selected exact chart.  Positivity and trace-one are inherited from the
existing finite partial-trace theorem. -/
noncomputable def pairMarginal
    {n d : ℕ}
    (X : Atlas n d)
    (i j : Fin n)
    (hij : i ≠ j) :
    ReducedState.DensityMatrix (PairIndex d) := by
  classical
  let C := X.chart i j hij
  letI : Fintype C.Env := C.envFintype
  letI : DecidableEq C.Env := C.envDecidableEq
  exact ReducedState.partialTraceDensityRight (X.chartedGlobal i j hij)

/-- Same-global-state pair mutual information for every charted distinct pair. -/
noncomputable def mutualInformation
    {n d : ℕ}
    (X : Atlas n d)
    (i j : Fin n)
    (hij : i ≠ j) : ℝ :=
  VonNeumannInformation.mutualInformation (X.pairMarginal i j hij)

/-- Every charted pair is a genuine finite density matrix by construction. -/
theorem pairMarginal_traceOne
    {n d : ℕ}
    (X : Atlas n d)
    (i j : Fin n)
    (hij : i ≠ j) :
    Matrix.trace (X.pairMarginal i j hij).matrix = 1 :=
  (X.pairMarginal i j hij).traceOne

/-- Every charted pair is positive semidefinite by construction. -/
theorem pairMarginal_posSemidef
    {n d : ℕ}
    (X : Atlas n d)
    (i j : Fin n)
    (hij : i ≠ j) :
    (X.pairMarginal i j hij).matrix.PosSemidef :=
  (X.pairMarginal i j hij).positive

end Atlas

structure Boundary where
  chartedFiniteNPairExtractionPaid : Bool := true
  chartedPairMarginalIsDensityMatrix : Bool := true
  everyPairWeightComesFromSameDeclaredGlobalState : Bool := true
  chartFamilyAutomaticallyExistsForPhysicalSelectedTPS : Bool := false
  chartIndependenceAndOverlapCoherencePaid : Bool := false
  chartedAtlasCreatesHeterogeneousSelectedTPSAtlas : Bool := false
  chartedAtlasCreatesMetric : Bool := false
  chartedAtlasCreatesSpatialRealization : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem charted_finite_n_pair_extraction_paid :
    canonicalBoundary.chartedFiniteNPairExtractionPaid = true := rfl

theorem charted_pair_marginal_is_density_matrix :
    canonicalBoundary.chartedPairMarginalIsDensityMatrix = true := rfl

theorem charted_atlas_does_not_create_heterogeneous_selected_tps_atlas :
    canonicalBoundary.chartedAtlasCreatesHeterogeneousSelectedTPSAtlas = false := rfl

/-- Imported theorem-source receipt for matrix reindexing and the previously
merged finite partial-trace density preservation theorem. -/
def finiteNAtlasFormalSourceReceipt : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib Matrix.reindex + DASHI ReducedState.partialTraceDensityRight"
  claim := "Exact basis reindexing and finite partial trace preserve the structure needed by the DASHI density-matrix carrier; the current module composes those theorem sources over an explicit pair/environment chart."

/-- New DASHI compiler theorem receipt. -/
def dashiFiniteNChartedAtlasReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Given one finite density state on the homogeneous global carrier (Fin n -> Fin d) and an exact coordinate-faithful pair/environment chart for every distinct ordered factor pair, reindexes the SAME state and traces the environment to produce a genuine density matrix and mutual-information weight for every pair. It does not manufacture the chart family for a heterogeneous physical selected TPS, chart-independence/overlap coherence, a metric, MDS realization, curvature or spacetime."

end FiniteNChartedAtlas
end QuantumMereology
