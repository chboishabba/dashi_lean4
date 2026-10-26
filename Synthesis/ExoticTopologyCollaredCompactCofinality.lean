import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Compact

/-!
# SAME-OBJECT COLLAR EXHAUSTION ADAPTER — original Mathlib owns compactness

Maximal prior-art reuse found in the **actual locked v4.28.0**:
  Mathlib/Topology/Compactness/SigmaCompact.lean
  structure CompactExhaustion (X)
  theorem CompactExhaustion.exists_superset_of_isCompact
  theorem CompactExhaustion.exists_mem_nhds.

ORIGINAL formal implementation authors, not DASHI:
Johannes Hölzl, Mario Carneiro, Yury Kudryashov
(copyright Johannes Hölzl 2017, Mathlib open-source license).

Actual Hatcher horned #1244 independently uses the original
Mathlib IsCompact.elim_directed_cover for OPEN directed exteriors.
This module deliberately does not implement another compactness
theorem or another notion of exhaustion.

The source-specific remaining mathematical obligations for a
selected infinite oriented pants/handle surface are to construct
the ACTUAL topological X and ACTUAL compact K_n with
  (i) IsCompact (K n),
  (ii) K n ⊆ interior (K (n+1)),
  (iii) ⋃ n, K n = univ.
Then the EXISTING Mathlib CompactExhaustion provides all
compact-cofinality and neighbourhood-exhaustion results.

Do not identify finite PL tests with construction of that X,
or a symbolic Cantor-stream homeomorphism with its Richards
ideal-boundary topology. Source-written kernel-check pending.

Source roots:
  Richards 1963 — classified noncompact SURFACE ends;
  Hölzl/Carneiro/Kudryashov — Mathlib CompactExhaustion API;
  DASHI — only this source-specific adapter and consumers.
-/

namespace Synthesis.ExoticTopology

variable {X : Type*} [TopologicalSpace X]

/-- Convert a verified actual nested collared sequence into the
ORIGINAL Mathlib compact-exhaustion structure, not a new record. -/
def sourceCollaredCompactExhaustion
    (K : ℕ → Set X)
    (hcompact : ∀ n, IsCompact (K n))
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : (⋃ n, K n) = Set.univ) :
    CompactExhaustion X where
  toFun := K
  isCompact' := hcompact
  subset_interior_succ' := hcollar
  iUnion_eq' := hcover

/-- The actual needed compact cofinality is ALREADY Mathlib's theorem.
This is merely a source-specific adapter with concrete collar inputs.
No new mathematical proof of directed-cover compactness is claimed. -/
theorem compactAbsorbedByNestedCollaredExhaustion
    (K : ℕ → Set X)
    (hcompact : ∀ n, IsCompact (K n))
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : (⋃ n, K n) = Set.univ)
    (C : Set X) (hC : IsCompact C) :
    ∃ n, C ⊆ K n := by
  exact (sourceCollaredCompactExhaustion
    K hcompact hcollar hcover).exists_superset_of_isCompact hC

/-- For all actual x in the realised infinite PL surface, one
verified source compact stage is a NEIGHBORHOOD of x. This too
is an already-owned Mathlib `CompactExhaustion` result. -/
theorem sourceCollaredExhaustion_hasNeighbourhood
    (K : ℕ → Set X)
    (hcompact : ∀ n, IsCompact (K n))
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : (⋃ n, K n) = Set.univ)
    (x : X) :
    ∃ n, K n ∈ 𝓝 x := by
  exact (sourceCollaredCompactExhaustion
    K hcompact hcollar hcover).exists_mem_nhds x

/-- Continuous images from compact source spaces, including the
interval and square, lie in one SOURCE stage as an automatic
application of ORIGINAL Mathlib cofinality. This asserts no
particular null-homotopy or wild-group identification. -/
theorem compactMapAbsorbedByNestedCollaredExhaustion
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (K : ℕ → Set X)
    (hcompact : ∀ n, IsCompact (K n))
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : (⋃ n, K n) = Set.univ) :
    ∃ n, ∀ t, f t ∈ K n := by
  have hrange : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using
      ((isCompact_univ : IsCompact (Set.univ : Set T)).image f.continuous)
  obtain ⟨n, hn⟩ :=
    compactAbsorbedByNestedCollaredExhaustion
      K hcompact hcollar hcover (Set.range f) hrange
  exact ⟨n, fun t => hn (Set.mem_range_self t)⟩

end Synthesis.ExoticTopology
