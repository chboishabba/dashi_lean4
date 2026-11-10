import Mathlib

/-!
# Exact Kakeya needle and tube transport under an original metric map

Original Kakeya mathematical sources: H. Wang and J. Zahl (2025),
arXiv:2502.17655; L. Guth, H. Wang and J. Zahl (2026),
arXiv:2601.14411. DASHI's result here is only the generic
metric/needle transport, NOT a new geometric Kakeya estimate.

A Lipschitz or bi-Lipschitz map does not automatically preserve
Euclidean straight segments. This file requires EXACT selected
needle-parameter preservation. A map that is not surjective only
provides an inclusion into the corresponding target tube.
-/

namespace DashiKakeya

universe u v w

variable {X : Type u} {Y : Type v} {Direction : Type w}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Closed metric radius-r neighbourhood of a parametrised unit needle. -/
def inNeedleTube (needle : ℝ → X) (radius : ℝ) (point : X) : Prop :=
  ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist point (needle t) ≤ radius

/-- Reusing the same curve parameter makes the tube distance exact. -/
theorem needleTube_iff_of_same_metric
    (F : X → Y)
    (src : ℝ → X) (dst : ℝ → Y)
    (radius : ℝ) (point : X)
    (distancePreserving : ∀ x z, dist (F x) (F z) = dist x z)
    (needlePreserving : ∀ t, F (src t) = dst t) :
    inNeedleTube src radius point ↔
      inNeedleTube dst radius (F point) := by
  constructor
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, ?_⟩
    rw [← needlePreserving t, distancePreserving]
    exact hd
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, ?_⟩
    rw [← needlePreserving t, distancePreserving] at hd
    exact hd

/-- Exact tube set equality if the map is also onto. -/
theorem needleTube_image_of_surjective
    (F : X → Y)
    (src : ℝ → X) (dst : ℝ → Y)
    (radius : ℝ)
    (distancePreserving : ∀ x z, dist (F x) (F z) = dist x z)
    (needlePreserving : ∀ t, F (src t) = dst t)
    (onto : Function.Surjective F) :
    F '' {x : X | inNeedleTube src radius x} =
      {y : Y | inNeedleTube dst radius y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (needleTube_iff_of_same_metric
      F src dst radius x distancePreserving needlePreserving).mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := onto y
    exact ⟨x, (needleTube_iff_of_same_metric
      F src dst radius x distancePreserving needlePreserving).mpr hy, rfl⟩

/-- Every direction is transported using that SAME metric map. -/
theorem allDirectionalTubes_iff
    (F : X → Y)
    (src : Direction → ℝ → X)
    (dst : Direction → ℝ → Y)
    (radius : ℝ) (point : X)
    (distancePreserving : ∀ x z, dist (F x) (F z) = dist x z)
    (needlePreserving : ∀ d t, F (src d t) = dst d t) :
    (∀ d, inNeedleTube (src d) radius point) ↔
      (∀ d, inNeedleTube (dst d) radius (F point)) := by
  constructor
  · intro h d
    exact (needleTube_iff_of_same_metric F (src d) (dst d)
      radius point distancePreserving (needlePreserving d)).mp (h d)
  · intro h d
    exact (needleTube_iff_of_same_metric F (src d) (dst d)
      radius point distancePreserving (needlePreserving d)).mpr (h d)

/-- All-direction tube set equality, with one onto isometry. -/
theorem allDirectionalTubeImage
    (F : X → Y)
    (src : Direction → ℝ → X)
    (dst : Direction → ℝ → Y)
    (radius : ℝ)
    (distancePreserving : ∀ x z, dist (F x) (F z) = dist x z)
    (needlePreserving : ∀ d t, F (src d t) = dst d t)
    (onto : Function.Surjective F) :
    F '' {x : X | ∀ d, inNeedleTube (src d) radius x} =
      {y : Y | ∀ d, inNeedleTube (dst d) radius y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (allDirectionalTubes_iff F src dst radius x
      distancePreserving needlePreserving).mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := onto y
    exact ⟨x, (allDirectionalTubes_iff F src dst radius x
      distancePreserving needlePreserving).mpr hy, rfl⟩

/-!
The very strong "forall d, point lies in every tube" predicate
is NOT a Kakeya-set definition; it is a convenient all-direction
test of the transport theorem. For actual Kakeya sets one uses
a union of needles indexed by all projective directions and proves
that each needle is contained in the set. Neither that selection,
nor Hausdorff-dimension transport, is asserted in this module.
-/

end DashiKakeya
