import RequestProject.QuantumMereologyVonNeumannInformation

/-!
# Same-global-state tripartite information atlas

The bipartite mutual-information producer is not by itself a multi-factor graph:
independently supplied pair states need not be marginals of one global state.
This module pays the first nontrivial same-object consistency cut.

Starting from one finite density matrix on `(A × B) × C`, DASHI constructs all
three pair density matrices `AB`, `AC`, and `BC` by explicit partial traces,
proves that each remains PSD and trace one, and proves that the overlapping
single-factor marginals agree.  Hence the three mutual-information edge weights
are genuinely derived from one and the same global quantum state.

This is a concrete three-factor atlas, not a general N-factor recursion, and it
does not create a metric, spatial realization, holographic dictionary, or
preferred TPS by itself.
-/

namespace QuantumMereology
namespace TripartiteInformationAtlas

open scoped BigOperators

variable
  {A B C : Type*}
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

abbrev GlobalIndex := (A × B) × C

/-- Trace out the middle factor `B`, retaining `A × C`. -/
def partialTraceMiddle
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  fun i j => ∑ b : B, rho ((i.1, b), i.2) ((j.1, b), j.2)

/-- Fixed-middle principal block. -/
def middleBlock
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ)
    (b : B) : Matrix (A × C) (A × C) ℂ :=
  rho.submatrix
    (fun i => ((i.1, b), i.2))
    (fun j => ((j.1, b), j.2))

theorem partialTraceMiddle_eq_sum_middleBlock
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    partialTraceMiddle rho = ∑ b : B, middleBlock rho b := by
  ext i j
  simp [partialTraceMiddle, middleBlock]

theorem trace_partialTraceMiddle
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    Matrix.trace (partialTraceMiddle rho) = Matrix.trace rho := by
  classical
  simp [partialTraceMiddle, Matrix.trace, Fintype.sum_prod_type,
    Finset.sum_comm]

theorem posSemidef_partialTraceMiddle
    {rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ}
    (h : rho.PosSemidef) :
    (partialTraceMiddle rho).PosSemidef := by
  rw [partialTraceMiddle_eq_sum_middleBlock]
  simpa only [Finset.sum_univ] using
    ReducedState.finset_sum_posSemidef
      (s := Finset.univ)
      (M := middleBlock rho)
      (fun b _ => h.submatrix (fun i => ((i.1, b), i.2)))

/-- Trace out the first factor `A`, retaining `B × C`. -/
def partialTraceFirst
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    Matrix (B × C) (B × C) ℂ :=
  fun i j => ∑ a : A, rho ((a, i.1), i.2) ((a, j.1), j.2)

/-- Fixed-first principal block. -/
def firstBlock
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ)
    (a : A) : Matrix (B × C) (B × C) ℂ :=
  rho.submatrix
    (fun i => ((a, i.1), i.2))
    (fun j => ((a, j.1), j.2))

theorem partialTraceFirst_eq_sum_firstBlock
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    partialTraceFirst rho = ∑ a : A, firstBlock rho a := by
  ext i j
  simp [partialTraceFirst, firstBlock]

theorem trace_partialTraceFirst
    (rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ) :
    Matrix.trace (partialTraceFirst rho) = Matrix.trace rho := by
  classical
  simp [partialTraceFirst, Matrix.trace, Fintype.sum_prod_type,
    Finset.sum_comm]

theorem posSemidef_partialTraceFirst
    {rho : Matrix (GlobalIndex (A := A) (B := B) (C := C))
                  (GlobalIndex (A := A) (B := B) (C := C)) ℂ}
    (h : rho.PosSemidef) :
    (partialTraceFirst rho).PosSemidef := by
  rw [partialTraceFirst_eq_sum_firstBlock]
  simpa only [Finset.sum_univ] using
    ReducedState.finset_sum_posSemidef
      (s := Finset.univ)
      (M := firstBlock rho)
      (fun a _ => h.submatrix (fun i => ((a, i.1), i.2)))

/-- All pair marginals from one declared global density matrix. -/
structure Atlas where
  global : ReducedState.DensityMatrix
    (GlobalIndex (A := A) (B := B) (C := C))

namespace Atlas

/-- `AB` marginal, tracing out `C`. -/
def pairAB (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix (A × B) :=
  ReducedState.partialTraceDensityRight X.global

/-- `AC` marginal, tracing out `B`. -/
def pairAC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix (A × C) where
  matrix := partialTraceMiddle X.global.matrix
  positive := posSemidef_partialTraceMiddle X.global.positive
  traceOne := by
    rw [trace_partialTraceMiddle]
    exact X.global.traceOne

/-- `BC` marginal, tracing out `A`. -/
def pairBC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix (B × C) where
  matrix := partialTraceFirst X.global.matrix
  positive := posSemidef_partialTraceFirst X.global.positive
  traceOne := by
    rw [trace_partialTraceFirst]
    exact X.global.traceOne

/-- The `A` marginal computed through `AB`. -/
def factorAFromAB (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix A :=
  ReducedState.partialTraceDensityRight X.pairAB

/-- The `A` marginal computed through `AC`. -/
def factorAFromAC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix A :=
  ReducedState.partialTraceDensityRight X.pairAC

/-- The `B` marginal computed through `AB`. -/
def factorBFromAB (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix B :=
  VonNeumannInformation.partialTraceDensityLeft X.pairAB

/-- The `B` marginal computed through `BC`. -/
def factorBFromBC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix B :=
  ReducedState.partialTraceDensityRight X.pairBC

/-- The `C` marginal computed through `AC`. -/
def factorCFromAC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix C :=
  VonNeumannInformation.partialTraceDensityLeft X.pairAC

/-- The `C` marginal computed through `BC`. -/
def factorCFromBC (X : Atlas (A := A) (B := B) (C := C)) :
    ReducedState.DensityMatrix C :=
  VonNeumannInformation.partialTraceDensityLeft X.pairBC

/-- Overlap consistency for factor `A`: tracing `C` then `B` agrees with
tracing `B` then `C`, on the same global matrix. -/
theorem factorA_matrix_consistent
    (X : Atlas (A := A) (B := B) (C := C)) :
    X.factorAFromAB.matrix = X.factorAFromAC.matrix := by
  ext i j
  simp [factorAFromAB, factorAFromAC, pairAB, pairAC,
    ReducedState.partialTraceDensityRight,
    ReducedState.partialTraceRight, partialTraceMiddle,
    Finset.sum_comm]

/-- Overlap consistency for factor `B`. -/
theorem factorB_matrix_consistent
    (X : Atlas (A := A) (B := B) (C := C)) :
    X.factorBFromAB.matrix = X.factorBFromBC.matrix := by
  ext i j
  simp [factorBFromAB, factorBFromBC, pairAB, pairBC,
    VonNeumannInformation.partialTraceDensityLeft,
    VonNeumannInformation.partialTraceLeft,
    ReducedState.partialTraceDensityRight,
    ReducedState.partialTraceRight, partialTraceFirst,
    Finset.sum_comm]

/-- Overlap consistency for factor `C`. -/
theorem factorC_matrix_consistent
    (X : Atlas (A := A) (B := B) (C := C)) :
    X.factorCFromAC.matrix = X.factorCFromBC.matrix := by
  ext i j
  simp [factorCFromAC, factorCFromBC, pairAC, pairBC,
    VonNeumannInformation.partialTraceDensityLeft,
    VonNeumannInformation.partialTraceLeft,
    partialTraceMiddle, partialTraceFirst,
    Finset.sum_comm]

/-- Same-global-state mutual-information edge `AB`. -/
noncomputable def mutualInformationAB
    (X : Atlas (A := A) (B := B) (C := C)) : ℝ :=
  VonNeumannInformation.mutualInformation X.pairAB

/-- Same-global-state mutual-information edge `AC`. -/
noncomputable def mutualInformationAC
    (X : Atlas (A := A) (B := B) (C := C)) : ℝ :=
  VonNeumannInformation.mutualInformation X.pairAC

/-- Same-global-state mutual-information edge `BC`. -/
noncomputable def mutualInformationBC
    (X : Atlas (A := A) (B := B) (C := C)) : ℝ :=
  VonNeumannInformation.mutualInformation X.pairBC

end Atlas

structure Boundary where
  sameGlobalStateThreePairMarginalsPaid : Bool := true
  overlappingOneFactorMarginalsAgree : Bool := true
  threeSameObjectMutualInformationEdgesDefined : Bool := true
  tripartiteAtlasCreatesGeneralNFactorAtlas : Bool := false
  tripartiteAtlasCreatesMetric : Bool := false
  tripartiteAtlasCreatesSpatialRealization : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem same_global_state_three_pair_marginals_paid :
    canonicalBoundary.sameGlobalStateThreePairMarginalsPaid = true := rfl

theorem overlapping_one_factor_marginals_agree :
    canonicalBoundary.overlappingOneFactorMarginalsAgree = true := rfl

theorem tripartite_atlas_does_not_create_general_n_factor_atlas :
    canonicalBoundary.tripartiteAtlasCreatesGeneralNFactorAtlas = false := rfl

/-- DASHI theorem receipt. No external paper is credited with this local finite
same-object marginal-consistency compiler. -/
def dashiTripartiteInformationAtlasReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "From one finite PSD trace-one state on (A×B)×C, constructs AB, AC and BC pair density matrices by explicit partial traces, proves overlap consistency of the A/B/C one-factor marginals, and defines the three same-global-state mutual-information edge weights. It does not create a general N-factor marginal atlas, metric, MDS realization, curvature or spacetime."

end TripartiteInformationAtlas
end QuantumMereology
