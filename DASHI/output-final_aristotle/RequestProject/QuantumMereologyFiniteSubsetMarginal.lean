import RequestProject.QuantumMereologyHeterogeneousFiniteAtlas
import Mathlib.Data.Finset.Basic

/-!
# Canonical finite-subset marginals from one heterogeneous global state

This module strengthens pair extraction to arbitrary finite subsystem subsets.
For a finite factor index `I`, heterogeneous factor dimensions `d : I -> Nat`,
and a finite selected subset `S : Finset I`, the global coordinate basis splits
canonically into the selected coordinates and their complement.

Reindexing the SAME global density matrix along that exact equivalence and
tracing the complement produces `rho_S` for every finite subset `S`.

The module deliberately stops before the presheaf/coherence theorem for nested
subsets.  It does not yet prove that for `T ⊆ S`, tracing `rho_S` over `S \ T`
agrees with `rho_T`; nor does it identify an arbitrary Hilbert/operator-algebra
TPS with this coordinate family.
-/

namespace QuantumMereology
namespace FiniteSubsetMarginal

abbrev GlobalIndex (I : Type*) (d : I -> Nat) :=
  HeterogeneousFiniteAtlas.GlobalIndex I d

def SelectedIndex {I : Type*} [DecidableEq I] (S : Finset I) :=
  { k : I // k ∈ S }

def ComplementIndex {I : Type*} [DecidableEq I] (S : Finset I) :=
  { k : I // k ∉ S }

abbrev SelectedState
    {I : Type*} [DecidableEq I]
    (d : I -> Nat) (S : Finset I) :=
  (k : SelectedIndex S) -> Fin (d k.1)

abbrev ComplementState
    {I : Type*} [DecidableEq I]
    (d : I -> Nat) (S : Finset I) :=
  (k : ComplementIndex S) -> Fin (d k.1)

/-- Canonical restriction/complement equivalence for an arbitrary finite subset
of heterogeneous coordinate factors. -/
noncomputable def canonicalSubsetSplit
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : I -> Nat) (S : Finset I) :
    GlobalIndex I d ≃ (SelectedState d S × ComplementState d S) where
  toFun x :=
    (fun k => x k.1,
     fun k => x k.1)
  invFun y := fun k =>
    if hk : k ∈ S then
      y.1 ⟨k, hk⟩
    else
      y.2 ⟨k, hk⟩
  left_inv x := by
    funext k
    by_cases hk : k ∈ S
    · simp [hk]
    · simp [hk]
  right_inv y := by
    apply Prod.ext
    · funext k
      simp [k.property]
    · funext k
      simp [k.property]

/-- One heterogeneous global density state, reused for every subsystem subset. -/
structure Atlas (I : Type*) [Fintype I] [DecidableEq I] (d : I -> Nat) where
  global : ReducedState.DensityMatrix (GlobalIndex I d)

namespace Atlas

/-- Reindex the same global state into selected-subset × complement coordinates. -/
noncomputable def chartedGlobal
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (S : Finset I) :
    ReducedState.DensityMatrix (SelectedState d S × ComplementState d S) := by
  classical
  exact FiniteNChartedAtlas.reindexDensity (canonicalSubsetSplit d S) X.global

/-- Density matrix of an arbitrary finite selected subset, obtained by tracing
its exact complement. -/
noncomputable def marginal
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (S : Finset I) :
    ReducedState.DensityMatrix (SelectedState d S) := by
  classical
  exact ReducedState.partialTraceDensityRight (X.chartedGlobal S)

 theorem marginal_traceOne
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (S : Finset I) :
    Matrix.trace (X.marginal S).matrix = 1 :=
  (X.marginal S).traceOne

 theorem marginal_posSemidef
    {I : Type*} [Fintype I] [DecidableEq I]
    {d : I -> Nat}
    (X : Atlas I d) (S : Finset I) :
    (X.marginal S).matrix.PosSemidef :=
  (X.marginal S).positive

end Atlas

structure Boundary where
  canonicalSubsetSplitPaid : Bool := true
  everyFiniteSubsetMarginalComesFromSameGlobalState : Bool := true
  arbitrarySubsetDensityPreservationPaid : Bool := true
  nestedRestrictionCoherencePaid : Bool := false
  subsetMarginalsAutomaticallyAttachToArbitraryHilbertTPS : Bool := false
  subsetMarginalsAutomaticallyAttachToArbitraryGTPS : Bool := false
  subsetMarginalsCreateSpatialGeometry : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem canonical_subset_split_paid :
    canonicalBoundary.canonicalSubsetSplitPaid = true := rfl

theorem every_subset_marginal_same_global_state :
    canonicalBoundary.everyFiniteSubsetMarginalComesFromSameGlobalState = true := rfl

theorem nested_restriction_coherence_not_yet_paid :
    canonicalBoundary.nestedRestrictionCoherencePaid = false := rfl

/-- Formal source receipt. -/
def subsetMarginalFormalSourceReceipt : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "DASHI FiniteNChartedAtlas.reindexDensity + ReducedState.partialTraceDensityRight over pinned mathlib v4.28"
  claim := "Exact finite basis reindexing and finite partial trace preserve the DASHI density-matrix carrier."

/-- DASHI-owned arbitrary-subset compiler. -/
def dashiFiniteSubsetMarginalReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "For a finite heterogeneous dependent coordinate factor family and one global density state, constructs the selected-subset/complement basis equivalence canonically for every Finset of factors and derives every subset density matrix from the same global state. It does not yet prove nested-subset marginal coherence, arbitrary physical TPS attachment, information geometry, holography or spacetime."

end FiniteSubsetMarginal
end QuantumMereology
