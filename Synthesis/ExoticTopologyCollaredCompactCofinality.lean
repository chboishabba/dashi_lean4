import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
# Exhausting by actual collars implies compact cofinality

SOURCE REUSE:
* Mathlib v4.28.0: IsCompact.elim_directed_cover,
  IsOpen (interior K), monotonicity of interior.
* DASHI Agda #1244 HatcherOpenExhaustionCompactAbsorption.lean
  already owns the generic compact absorption theorem for monotone
  open exteriors. This module does NOT copy its proof or silently
  import a differently pinned horned-sphere project.
* DASHI Agda #1254 finite oriented PL collars/stable-star checks
  are currently BOUNDED; no actual infinite PL space is imported.
* Richards (1963) uses compact-cofinality to obtain genuine
  escaping nested end regions and their topology.

Math: for an increasing exhaustive sequence of subsets K_n of an
ACTUAL topological space X, if every K_n is contained in the
interior of K_(n+1), then EVERY compact subset of X is contained
in some K_N. The proof is not merely an assumption named
'compact cofinality'; it constructs the increasing directed OPEN
cover by interiors and uses Mathlib compact absorption.

The missing same-object geometry is an actual X and a
collared K_n sequence with the required coverage/inclusions.
No surface, actual end-space homeomorphism or genus is
manufactured here from stage arithmetic or finite fixtures.
Source-written Lean; exact pinned kernel check pending.
-/

namespace Synthesis.ExoticTopology

variable {X : Type*} [TopologicalSpace X]

/-- A monotone exhausted topological carrier, with every old compact
stage placed strictly inside the next stage's interior. We DO NOT
assume K_n compact in this lemma, since compactness of the subset
C we are trying to absorb is the decisive requirement. -/
theorem compactAbsorbedByNestedCollaredExhaustion
    (K : ℕ → Set X)
    (hmono : Monotone K)
    (hcover : (⋃ n, K n) = Set.univ)
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1)))
    (C : Set X) (hcompact : IsCompact C) :
    ∃ n, C ⊆ K n := by
  have hopen : ∀ n, IsOpen (interior (K n)) :=
    fun _ => isOpen_interior
  have hinteriorMono : Monotone (fun n => interior (K n)) := by
    intro i j hij
    exact interior_mono (hmono hij)
  have hcovered : C ⊆ ⋃ n, interior (K n) := by
    intro x hx
    have hxcover : x ∈ ⋃ n, K n := by
      rw [hcover]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxcover
    exact Set.mem_iUnion.mpr ⟨n + 1, hcollar n hn⟩
  obtain ⟨n, hn⟩ :=
    hcompact.elim_directed_cover
      (fun n => interior (K n)) hopen hcovered
      (fun i j => ⟨max i j,
        hinteriorMono (le_max_left i j),
        hinteriorMono (le_max_right i j)⟩)
  exact ⟨n, hn.trans interior_subset⟩

/-- In particular, ANY compact loop image, square homotopy image,
or other compactly parametrised observation is already entirely
contained in one genuine collar stage. This does not imply
the map is null-homotopic in that stage. -/
theorem compactMapAbsorbedByNestedCollaredExhaustion
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, X))
    (K : ℕ → Set X)
    (hmono : Monotone K)
    (hcover : (⋃ n, K n) = Set.univ)
    (hcollar : ∀ n, K n ⊆ interior (K (n + 1))) :
    ∃ n, ∀ t, f t ∈ K n := by
  have hK : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using
      ((isCompact_univ : IsCompact (Set.univ : Set T)).image f.continuous)
  obtain ⟨n, hn⟩ :=
    compactAbsorbedByNestedCollaredExhaustion
      K hmono hcover hcollar (Set.range f) hK
  exact ⟨n, fun t => hn (Set.mem_range_self t)⟩

end Synthesis.ExoticTopology
