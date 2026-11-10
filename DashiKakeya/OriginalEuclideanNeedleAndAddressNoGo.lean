import DashiKakeya.NeedleTubeTransport
import DashiKakeya.LorentzSpatialSlice

/-!
# Original Euclidean needles and finite-address no-go

This module closes two mathematical leaves *for explicitly selected
objects* without treating a physical correspondence as an axiomless
derived fact:

1. Translation of genuine affine unit line segments and their entire
   direction-indexed families is exact; the corresponding metric
   tubular neighbourhoods transport exactly.
2. A strictly positive global lower metric-comparison constant forces
   an address projection to be injective. If a finite refinement
   identifies any distinct pair, no such bound can hold at that scale.
   Therefore a global all-scale multiplicative bound cannot follow
   merely from finite-prefix/p-adic coding.

Original Kakeya mathematics: Wang--Zahl (2025, arXiv:2502.17655);
Guth--Wang--Zahl (2026, arXiv:2601.14411). These lemmas are
DASHI integrations, not new Kakeya estimates. This module says
nothing about whether a real observer or a KK-reduced physical metric
is Euclidean: that requires independent physical evidence.
-/

namespace DashiKakeya

universe u v

/-- A genuine affine segment in the same Euclidean R³ used by Kakeya. -/
def straightNeedle (base direction : Spatial3) (t : ℝ) : Spatial3 :=
  base + t • direction

def spatialTranslation (shift x : Spatial3) : Spatial3 := x + shift

theorem straightNeedle_translation (base direction shift : Spatial3)
    (t : ℝ) :
    spatialTranslation shift (straightNeedle base direction t) =
      straightNeedle (base + shift) direction t := by
  simp [spatialTranslation, straightNeedle, add_assoc, add_comm, add_left_comm]

theorem spatialTranslation_distance (shift x y : Spatial3) :
    dist (spatialTranslation shift x) (spatialTranslation shift y) =
      dist x y := by
  simpa [spatialTranslation] using dist_add_right x y shift

theorem spatialTranslation_surjective (shift : Spatial3) :
    Function.Surjective (spatialTranslation shift) := by
  intro y
  refine ⟨y - shift, ?_⟩
  simp [spatialTranslation]

/-- This is an actual source/target straight-segment tube equivalence. -/
theorem straightNeedleTube_translation (base direction shift : Spatial3)
    (radius : ℝ) (point : Spatial3) :
    inNeedleTube (straightNeedle base direction) radius point ↔
      inNeedleTube (straightNeedle (base + shift) direction)
        radius (spatialTranslation shift point) := by
  exact needleTube_iff_of_same_metric
    (spatialTranslation shift)
    (straightNeedle base direction)
    (straightNeedle (base + shift) direction)
    radius point
    (spatialTranslation_distance shift)
    (straightNeedle_translation base direction shift)

/-- Every direction's *actual* segment is transported, not just its label. -/
theorem straightNeedles_translation
    {Direction : Type u} (base direction : Direction → Spatial3)
    (shift : Spatial3) (K : Set Spatial3)
    (h : containsDirectionalNeedles K
      (fun d => straightNeedle (base d) (direction d))) :
    containsDirectionalNeedles
      ((spatialTranslation shift) '' K)
      (fun d => straightNeedle (base d + shift) (direction d)) := by
  exact needleContainment_image
    (spatialTranslation shift) K
    (fun d => straightNeedle (base d) (direction d))
    (fun d => straightNeedle (base d + shift) (direction d))
    (by intro d t; exact straightNeedle_translation (base d) (direction d) shift t)
    h

/-- The union of all selected genuine segment tubes translates exactly. -/
theorem straightNeedleTubeUnion_translation
    {Direction : Type u} (base direction : Direction → Spatial3)
    (shift : Spatial3) (radius : ℝ) :
    spatialTranslation shift ''
      {x : Spatial3 | ∃ d,
        inNeedleTube (straightNeedle (base d) (direction d))
          radius x} =
      {y : Spatial3 | ∃ d,
        inNeedleTube (straightNeedle (base d + shift) (direction d))
          radius y} := by
  exact directionalTubeUnion_image
    (spatialTranslation shift)
    (fun d => straightNeedle (base d) (direction d))
    (fun d => straightNeedle (base d + shift) (direction d))
    radius
    (spatialTranslation_distance shift)
    (by intro d t; exact straightNeedle_translation (base d) (direction d) shift t)
    (spatialTranslation_surjective shift)

/-- A positive comparison against an exact address-code distance forces
    injectivity; this is a *mathematical* constraint on any physical model. -/
theorem lowerMetricComparison_forces_injective
    {X : Type u} {Code : Type v}
    [MetricSpace X] [PseudoMetricSpace Code]
    (encode : X → Code) (lower upperScale : ℝ)
    (lowerPositive : 0 < lower)
    (comparison : ∀ x y, lower * dist x y ≤
      upperScale * dist (encode x) (encode y)) :
    Function.Injective encode := by
  intro x y hxy
  have h := comparison x y
  have hcode : dist (encode x) (encode y) = 0 := by
    rw [hxy, dist_self]
  rw [hcode, mul_zero] at h
  by_contra hne
  have hdist : 0 < dist x y := (dist_pos).2 hne
  have hpositive : 0 < lower * dist x y := mul_pos lowerPositive hdist
  exact (not_lt_of_ge h) hpositive

/-- Any collision at a selected finite level rules out a strictly
    positive lower bound at that level. -/
theorem addressCollision_blocks_positiveComparison
    {X : Type u} {Code : Type v}
    [MetricSpace X] [PseudoMetricSpace Code]
    (encode : X → Code)
    (x y : X) (different : x ≠ y) (collision : encode x = encode y)
    (lower upperScale : ℝ) (lowerPositive : 0 < lower) :
    ¬ (∀ a b, lower * dist a b ≤
        upperScale * dist (encode a) (encode b)) := by
  intro comparison
  exact different
    ((lowerMetricComparison_forces_injective
      encode lower upperScale lowerPositive comparison) collision)

/-- In particular, a purported bound at ALL scales fails as soon as
    one original selected refinement scale aliases different states. -/
theorem allScaleComparison_obstructedByAnyCollision
    {X : Type u} {Code : Type v}
    [MetricSpace X] [PseudoMetricSpace Code]
    (encode : ℕ → X → Code)
    (lower : ℝ) (lowerPositive : 0 < lower) (scales : ℕ → ℝ)
    (n : ℕ) (x y : X) (different : x ≠ y)
    (collision : encode n x = encode n y) :
    ¬ (∀ k a b, lower * dist a b ≤
        scales k * dist (encode k a) (encode k b)) := by
  intro comparisons
  exact addressCollision_blocks_positiveComparison
    (encode n) x y different collision
    lower (scales n) lowerPositive (comparisons n)


/-- No ultrametric can be surjectively isometric to the ordinary real
line: three collinear points at distances 1, 1, and 2 violate the
ultrametric inequality. This is an exact metric obstruction, not a
claim about a particular physical system or ultrametric observation. -/
theorem no_surjective_ultrametric_isometry_to_real
    {X : Type u} [PseudoMetricSpace X]
    (ultra : ∀ x y z : X,
      dist x z ≤ max (dist x y) (dist y z))
    (F : X → ℝ)
    (onto : Function.Surjective F)
    (preserves : ∀ x y, dist (F x) (F y) = dist x y) :
    False := by
  obtain ⟨x, hx⟩ := onto (0 : ℝ)
  obtain ⟨y, hy⟩ := onto (1 : ℝ)
  obtain ⟨z, hz⟩ := onto (2 : ℝ)
  have h := ultra x y z
  rw [← preserves x z, ← preserves x y, ← preserves y z] at h
  rw [hx, hy, hz] at h
  norm_num [Real.dist_eq] at h

end DashiKakeya
