import RequestProject.QuantumMereologyFiniteNChartedAtlas

/-!
# Canonical heterogeneous finite-factor information atlas

The preceding finite-N owner accepted one explicit pair/environment chart for
each requested pair.  This module pays that chart-construction obligation for a
concrete finite coordinate factor family with possibly different factor sizes.

For a finite index type `I` and dimensions `d : I -> Nat`, the global basis is

  (k : I) -> Fin (d k).

For distinct `i,j`, the environment is the dependent product over every index
except `i,j`.  The pair/environment equivalence is constructed directly from
function restriction and reinsertion, so no independently supplied cardinality
matching is involved.

This is still a coordinate finite model.  It does not identify an arbitrary
Hilbert-space TPS, operator-algebra g-TPS, or physical subsystem decomposition
with this dependent coordinate family.  Nor does it yet construct the full
subset-indexed marginal presheaf/coherence theorem.  Those remain separate
same-object transport and coherence obligations.
-/

namespace QuantumMereology
namespace HeterogeneousFiniteAtlas

open scoped BigOperators

abbrev GlobalIndex (I : Type*) (d : I -> Nat) := (k : I) -> Fin (d k)
abbrev PairIndex {I : Type*} (d : I -> Nat) (i j : I) := Fin (d i) × Fin (d j)

def EnvIndex {I : Type*} (i j : I) := { k : I // k ≠ i ∧ k ≠ j }
abbrev EnvState {I : Type*} (d : I -> Nat) (i j : I) :=
  (k : EnvIndex i j) -> Fin (d k.1)

/-- Canonical split of a heterogeneous dependent coordinate family into one
ordered pair and the complementary environment. -/
noncomputable def canonicalSplit
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : I -> Nat) (i j : I) (hij : i ≠ j) :
    GlobalIndex I d ≃ (PairIndex d i j × EnvState d i j) where
  toFun x := ((x i, x j), fun k => x k.1)
  invFun y := fun k =>
    dite (k = i)
      (fun hki => hki ▸ y.1.1)
      (fun hki =>
        dite (k = j)
          (fun hkj => hkj ▸ y.1.2)
          (fun hkj => y.2 ⟨k, hki, hkj⟩))
  left_inv x := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hki, hij]
      · simp [hki, hkj]
  right_inv y := by
    have hji : j ≠ i := Ne.symm hij
    apply Prod.ext
    · apply Prod.ext
      · simp [canonicalSplit]
      · simp [canonicalSplit, hji]
    · funext k
      simp [canonicalSplit, k.property.1, k.property.2]

@[simp] theorem canonicalSplit_leftCoordinate
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : I -> Nat) (i j : I) (hij : i ≠ j)
    (x : GlobalIndex I d) :
    ((canonicalSplit d i j hij x).1.1) = x i := rfl

@[simp] theorem canonicalSplit_rightCoordinate
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : I -> Nat) (i j : I) (hij : i ≠ j)
    (x : GlobalIndex I d) :
    ((canonicalSplit d i j hij x).1.2) = x j := rfl

/-- One density matrix on the complete heterogeneous coordinate product. -/
structure Atlas (I : Type*) [Fintype I] [DecidableEq I] (d : I -> Nat) where
  global : ReducedState.DensityMatrix (GlobalIndex I d)

namespace Atlas

/-- Reindex the SAME global state along the canonical pair/environment split. -/
noncomputable def chartedGlobal
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (i j : I) (hij : i ≠ j) :
    ReducedState.DensityMatrix (PairIndex d i j × EnvState d i j) := by
  classical
  exact FiniteNChartedAtlas.reindexDensity (canonicalSplit d i j hij) X.global

/-- Canonical pair marginal obtained by tracing exactly the complementary
finite factor family. -/
noncomputable def pairMarginal
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (i j : I) (hij : i ≠ j) :
    ReducedState.DensityMatrix (PairIndex d i j) := by
  classical
  exact ReducedState.partialTraceDensityRight (X.chartedGlobal i j hij)

/-- Same-global-state mutual information on every distinct ordered pair. -/
noncomputable def mutualInformation
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (i j : I) (hij : i ≠ j) : Real :=
  VonNeumannInformation.mutualInformation (X.pairMarginal i j hij)

 theorem pairMarginal_traceOne
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (i j : I) (hij : i ≠ j) :
    Matrix.trace (X.pairMarginal i j hij).matrix = 1 :=
  (X.pairMarginal i j hij).traceOne

 theorem pairMarginal_posSemidef
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (i j : I) (hij : i ≠ j) :
    (X.pairMarginal i j hij).matrix.PosSemidef :=
  (X.pairMarginal i j hij).positive

end Atlas

structure Boundary where
  heterogeneousCoordinateCarrierPaid : Bool := true
  canonicalPairChartExists : Bool := true
  everyPairMarginalComesFromSameGlobalState : Bool := true
  pairDensityPreservationPaid : Bool := true
  arbitraryHilbertTPSAutomaticallyCoordinates : Bool := false
  arbitraryGTPSAutomaticallyCoordinates : Bool := false
  fullSubsetMarginalPresheafPaid : Bool := false
  chartIndependentPhysicalTPSAttachmentPaid : Bool := false
  mutualInformationAutomaticallyCreatesMetric : Bool := false
  spatialRealizationPaid : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem canonical_pair_chart_exists :
    canonicalBoundary.canonicalPairChartExists = true := rfl

theorem every_pair_marginal_comes_from_same_global_state :
    canonicalBoundary.everyPairMarginalComesFromSameGlobalState = true := rfl

theorem arbitrary_hilbert_tps_does_not_automatically_coordinate :
    canonicalBoundary.arbitraryHilbertTPSAutomaticallyCoordinates = false := rfl

theorem full_subset_marginal_presheaf_not_yet_paid :
    canonicalBoundary.fullSubsetMarginalPresheafPaid = false := rfl

/-- Imported theorem-source receipt: density preservation under exact reindexing
and finite partial trace is inherited from the already-audited formal owners. -/
def heterogeneousAtlasFormalSourceReceipt : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "DASHI FiniteNChartedAtlas + ReducedState over pinned mathlib v4.28"
  claim := "Exact finite basis reindexing and finite partial trace preserve the DASHI density-matrix carrier."

/-- DASHI-owned finite compiler. -/
def dashiHeterogeneousFiniteAtlasReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "For any finite index family with factor dimensions d : I -> Nat, constructs the pair/environment equivalence canonically from the dependent coordinate product and derives every distinct-pair density matrix and mutual-information weight from one global density state. This does not identify an arbitrary Hilbert/operator-algebra TPS with the coordinate carrier, prove the full subset marginal presheaf, metricity, MDS geometry, curvature, spacetime or physical subsystem authority."

end HeterogeneousFiniteAtlas
end QuantumMereology
