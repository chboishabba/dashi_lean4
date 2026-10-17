import RequestProject.QuantumMereologyReducedState
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite von Neumann entropy and mutual information

This module supplies the concrete finite information producer that was previously
missing from the quantum-mereology -> geometry lane.

For a finite PSD trace-one density matrix, mathlib's Hermitian spectral theorem
provides real eigenvalues and positivity provides nonnegativity. DASHI defines
the finite spectral von Neumann entropy with the standard `0 log 0 = 0`
convention and constructs both bipartite reduced density matrices by explicit
partial trace. Mutual information is then the same-object quantity

  I(A:B) = S(A) + S(B) - S(AB).

External attribution is kept separate below. In particular, Cao--Carroll--
Michalakis use mutual information as graph edge weight and then introduce a
separate system-dependent decreasing distance ansatz. This module does not
promote mutual information by itself to a metric, an MDS embedding, curvature,
or spacetime.
-/

namespace QuantumMereology
namespace VonNeumannInformation

open scoped BigOperators

/-- Continuous-extension convention for the spectral entropy summand:
`0 log 0` is represented by zero. -/
def entropyContribution (x : ℝ) : ℝ :=
  if x = 0 then 0 else -x * Real.log x

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Real eigenvalue of a finite density matrix, using its PSD-supplied
Hermitian witness. -/
noncomputable def densityEigenvalue
    (rho : ReducedState.DensityMatrix I) (i : I) : ℝ :=
  rho.positive.isHermitian.eigenvalues i

/-- PSD pays nonnegativity of every density-matrix eigenvalue. -/
theorem densityEigenvalue_nonnegative
    (rho : ReducedState.DensityMatrix I) (i : I) :
    0 ≤ densityEigenvalue rho i := by
  simpa [densityEigenvalue] using rho.positive.eigenvalues_nonneg i

/-- Trace one is exactly the statement that the spectral eigenvalues sum to one
(after coercion to the complex scalar field). -/
theorem densityEigenvalue_sum_eq_one_complex
    (rho : ReducedState.DensityMatrix I) :
    (∑ i : I, (densityEigenvalue rho i : ℂ)) = 1 := by
  calc
    (∑ i : I, (densityEigenvalue rho i : ℂ)) = Matrix.trace rho.matrix := by
      symm
      simpa [densityEigenvalue] using
        rho.positive.isHermitian.trace_eq_sum_eigenvalues
    _ = 1 := rho.traceOne

/-- The same normalization statement on the real spectral probabilities. -/
theorem densityEigenvalue_sum_eq_one
    (rho : ReducedState.DensityMatrix I) :
    (∑ i : I, densityEigenvalue rho i) = 1 := by
  have h := congrArg Complex.re (densityEigenvalue_sum_eq_one_complex rho)
  simpa using h

/-- Every density eigenvalue lies in the unit interval. -/
theorem densityEigenvalue_le_one
    (rho : ReducedState.DensityMatrix I) (i : I) :
    densityEigenvalue rho i ≤ 1 := by
  calc
    densityEigenvalue rho i ≤ ∑ j : I, densityEigenvalue rho j := by
      exact Finset.single_le_sum
        (fun j _ => densityEigenvalue_nonnegative rho j)
        (Finset.mem_univ i)
    _ = 1 := densityEigenvalue_sum_eq_one rho

/-- The entropy summand is nonnegative on a genuine density eigenvalue. -/
theorem entropyContribution_densityEigenvalue_nonnegative
    (rho : ReducedState.DensityMatrix I) (i : I) :
    0 ≤ entropyContribution (densityEigenvalue rho i) := by
  by_cases hzero : densityEigenvalue rho i = 0
  · simp [entropyContribution, hzero]
  · rw [entropyContribution, if_neg hzero]
    have hnonneg := densityEigenvalue_nonnegative rho i
    have hle := densityEigenvalue_le_one rho i
    have hlog : Real.log (densityEigenvalue rho i) ≤ 0 :=
      Real.log_nonpos hnonneg hle
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hnonneg) hlog

/-- Finite spectral von Neumann entropy `-sum_i lambda_i log lambda_i`, with
`0 log 0 = 0`. -/
noncomputable def vonNeumannEntropy
    (rho : ReducedState.DensityMatrix I) : ℝ :=
  ∑ i : I, entropyContribution (densityEigenvalue rho i)

theorem vonNeumannEntropy_eq_spectral_sum
    (rho : ReducedState.DensityMatrix I) :
    vonNeumannEntropy rho =
      ∑ i : I, entropyContribution (densityEigenvalue rho i) :=
  rfl

/-- Finite von Neumann entropy is nonnegative for the concrete density carrier. -/
theorem vonNeumannEntropy_nonnegative
    (rho : ReducedState.DensityMatrix I) :
    0 ≤ vonNeumannEntropy rho := by
  exact Finset.sum_nonneg fun i _ =>
    entropyContribution_densityEigenvalue_nonnegative rho i

/-! ## The other bipartite partial trace

`QuantumMereologyReducedState` already owns tracing out the right factor. The
same finite matrix argument gives tracing out the left factor, so both marginals
needed by mutual information are now concrete density matrices.
-/

variable
  {A B : Type*}
  [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Trace out the left factor. -/
def partialTraceLeft
    (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix B B ℂ :=
  fun i j => ∑ a : A, rho (a, i) (a, j)

theorem trace_partialTraceLeft
    (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceLeft rho) = Matrix.trace rho := by
  classical
  simp [partialTraceLeft, Matrix.trace, Fintype.sum_prod_type,
    Finset.sum_comm]

theorem isHermitian_partialTraceLeft
    {rho : Matrix (A × B) (A × B) ℂ}
    (h : rho.IsHermitian) :
    (partialTraceLeft rho).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [partialTraceLeft, map_sum, h.apply]

/-- Fixed-left principal block. -/
def leftBlock
    (rho : Matrix (A × B) (A × B) ℂ)
    (a : A) :
    Matrix B B ℂ :=
  rho.submatrix (fun b => (a, b)) (fun d => (a, d))

theorem partialTraceLeft_eq_sum_leftBlock
    (rho : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft rho = ∑ a : A, leftBlock rho a := by
  ext i j
  simp [partialTraceLeft, leftBlock]

theorem posSemidef_partialTraceLeft
    {rho : Matrix (A × B) (A × B) ℂ}
    (h : rho.PosSemidef) :
    (partialTraceLeft rho).PosSemidef := by
  rw [partialTraceLeft_eq_sum_leftBlock]
  simpa only [Finset.sum_univ] using
    ReducedState.finset_sum_posSemidef
      (s := Finset.univ)
      (M := leftBlock rho)
      (fun a _ => h.submatrix (fun b => (a, b)))

/-- The right-factor reduced density matrix. -/
def partialTraceDensityLeft
    (rho : ReducedState.DensityMatrix (A × B)) :
    ReducedState.DensityMatrix B where
  matrix := partialTraceLeft rho.matrix
  positive := posSemidef_partialTraceLeft rho.positive
  traceOne := by
    rw [trace_partialTraceLeft]
    exact rho.traceOne

/-- The already-merged right trace gives the left-factor marginal. -/
def leftMarginal
    (rho : ReducedState.DensityMatrix (A × B)) :
    ReducedState.DensityMatrix A :=
  ReducedState.partialTraceDensityRight rho

/-- The new left trace gives the right-factor marginal. -/
def rightMarginal
    (rho : ReducedState.DensityMatrix (A × B)) :
    ReducedState.DensityMatrix B :=
  partialTraceDensityLeft rho

/-- Finite bipartite quantum mutual information. -/
noncomputable def mutualInformation
    (rho : ReducedState.DensityMatrix (A × B)) : ℝ :=
  vonNeumannEntropy (leftMarginal rho) +
    vonNeumannEntropy (rightMarginal rho) -
    vonNeumannEntropy rho

theorem mutualInformation_eq_entropy_formula
    (rho : ReducedState.DensityMatrix (A × B)) :
    mutualInformation rho =
      vonNeumannEntropy (leftMarginal rho) +
      vonNeumannEntropy (rightMarginal rho) -
      vonNeumannEntropy rho :=
  rfl

/-! ## Cao--Carroll--Michalakis distance-ansatz boundary

The source uses mutual information to weight a graph, then separately chooses a
nonnegative decreasing function Phi of normalized mutual information. Zero
mutual information means no edge. We encode that separation explicitly rather
than claiming the mutual-information scalar is itself a metric.
-/

structure CCMDistanceAnsatz where
  informationScale : ℝ
  lengthScale : ℝ
  phi : ℝ → ℝ
  informationScalePositive : 0 < informationScale
  lengthScaleNonnegative : 0 ≤ lengthScale
  phiOne : phi 1 = 0
  phiNonnegativeOnUnit : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ phi x
  phiAntitoneOnUnit :
    ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 → phi y ≤ phi x

/-- Source-shaped distance transform on one already-produced information scalar.
`none` records the CCM convention that zero mutual information supplies no edge. -/
noncomputable def ccmDistanceFromInformation
    (D : CCMDistanceAnsatz) (information : ℝ) : Option ℝ :=
  if information = 0 then none
  else some (D.lengthScale * D.phi (information / D.informationScale))

/-- On the declared normalized-information domain, every present CCM edge has a
nonnegative length. This is not a triangle-inequality theorem. -/
theorem ccmDistanceFromInformation_nonnegative
    (D : CCMDistanceAnsatz) {information : ℝ}
    (hInfo : information ≠ 0)
    (h0 : 0 ≤ information / D.informationScale)
    (h1 : information / D.informationScale ≤ 1) :
    ∃ distance : ℝ,
      ccmDistanceFromInformation D information = some distance ∧
      0 ≤ distance := by
  refine ⟨D.lengthScale * D.phi (information / D.informationScale), ?_, ?_⟩
  · simp [ccmDistanceFromInformation, hInfo]
  · exact mul_nonneg D.lengthScaleNonnegative
      (D.phiNonnegativeOnUnit _ h0 h1)

/-- Normalized pair information for the source distance ansatz. -/
noncomputable def normalizedMutualInformation
    (D : CCMDistanceAnsatz)
    (rho : ReducedState.DensityMatrix (A × B)) : ℝ :=
  mutualInformation rho / D.informationScale

/-- Source-shaped edge-distance output for the concrete bipartite state. -/
noncomputable def ccmEdgeDistance
    (D : CCMDistanceAnsatz)
    (rho : ReducedState.DensityMatrix (A × B)) : Option ℝ :=
  ccmDistanceFromInformation D (mutualInformation rho)

structure Boundary where
  finiteVonNeumannEntropyDefined : Bool := true
  finiteVonNeumannEntropyNonnegativePaid : Bool := true
  bothBipartiteMarginalsAreDensityMatrices : Bool := true
  bipartiteMutualInformationDefined : Bool := true
  ccmDistanceAnsatzKeptSeparate : Bool := true
  normalizedCCMEdgeLengthNonnegativePaid : Bool := true
  mutualInformationAutomaticallyCreatesMetric : Bool := false
  mutualInformationAutomaticallyCreatesSpatialEmbedding : Bool := false
  bipartiteMutualInformationAutomaticallyCreatesNFactorGraph : Bool := false
  mutualInformationCreatesSpacetimeOrEinsteinDynamics : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem finite_von_neumann_entropy_defined :
    canonicalBoundary.finiteVonNeumannEntropyDefined = true := rfl

theorem bipartite_mutual_information_defined :
    canonicalBoundary.bipartiteMutualInformationDefined = true := rfl

theorem ccm_distance_ansatz_kept_separate :
    canonicalBoundary.ccmDistanceAnsatzKeptSeparate = true := rfl

theorem mutual_information_does_not_automatically_create_metric :
    canonicalBoundary.mutualInformationAutomaticallyCreatesMetric = false := rfl

/-- Formal theorem-source attribution. -/
def mathlibFiniteSpectralEntropySource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Matrix.IsHermitian spectral theorem / Matrix.PosSemidef.eigenvalues_nonneg / Matrix.trace / Real.log_nonpos"
  claim := "Supplies finite Hermitian eigenvalues, PSD eigenvalue nonnegativity, the spectral trace identity, and logarithm sign facts used by DASHI's finite von Neumann entropy producer."

/-- External physics/source attribution, kept distinct from local implementation. -/
def caoCarrollMichalakisMutualInformationClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "ChunJun Cao; Sean M. Carroll; Spyridon Michalakis, Phys. Rev. D 95, 024031 (2017), arXiv:1606.08444"
  claim := "Uses I(A:B)=S(A)+S(B)-S(AB) as edge weight on a factor graph and introduces a separate distance ansatz w(p,q)=ell_RC Phi(I/I0) for nonzero mutual information, with Phi nonnegative and decreasing on the normalized interval."

/-- DASHI-owned finite information compiler. -/
def dashiFiniteVonNeumannInformationReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Defines finite spectral von Neumann entropy, proves density eigenvalues form a nonnegative normalized finite spectrum and hence entropy is nonnegative, constructs both bipartite density-matrix marginals by explicit partial trace, defines same-object mutual information, and proves nonnegative CCM edge length on the declared normalized domain. It does not prove mutual-information nonnegativity/subadditivity, global N-factor marginal consistency, metric axioms, MDS realization, curvature, or Einstein dynamics."

end VonNeumannInformation
end QuantumMereology
