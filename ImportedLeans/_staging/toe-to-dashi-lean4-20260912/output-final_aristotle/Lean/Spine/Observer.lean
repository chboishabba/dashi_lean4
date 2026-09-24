/-
# Observers: "the X of Y" as an instance, with a nondegeneracy obligation

To say "the *X* of *Y*" one must supply five things: a carrier, a structure, an
explicit map from `Y`'s data into that structure, the theorem one wants, and its
hypotheses — *verified*.  This file packages the version of that discipline that
the spine supports.

A `Spine.MeanObserver D n` consists of:

* a domain `D` (the thing being observed);
* a *reading* `read : D → EuclideanSpace ℝ (Fin n)` (the map);
* a *channel* `channel : D → EuclideanSpace ℝ (Fin n)` (a second direction);
* two **nondegeneracy witnesses**: the reading has a nonzero constant mode, and
  the channel has a nonzero transverse (mean-zero) part.

The inherited theorem is `Spine.MeanObserver.transverse_area_pos`: the observed
pair spans a genuine plane, with the explicit floor
`n · avg(read d)² · ‖fluct (channel d)‖²` from the spine's coercivity theorem.
The two witnesses are exactly the hypotheses that theorem needs — remove either
and the conclusion fails, as `Spine.degenerate_observer_area_zero` records.

Two instances are given, and they inherit the *same* theorem:

* `Spine.monster_five_transverse_planes` — five modes, each with a nonzero
  constant part and a nonzero ternary transverse part, give five genuine
  transverse planes.  This is what upgrades a `5 × 2` cardinality into five
  planes; without the witnesses it is ten labels.
* `Spine.Cuisine.taste_plane_pos` — the taste vector of a `SensoryProfile`
  (the carrier mirrored in `Cuisine.SensoryCore` from the Agda cuisine lane)
  splits into overall intensity (fixed) and balance (transverse); a dish with
  nonzero total intensity and a second dish with a non-flat balance span a
  genuine plane.  The companion `Spine.Cuisine.flat_profile_degenerate` is the
  honest negative: a flat profile has zero transverse part and the inherited
  theorem then says nothing.

Nothing here is an empirical claim about food or about the Monster: the carriers
are a finite-dimensional real vector space and a finite record of natural
numbers, and every statement is about those.
-/
import Mathlib
import Spine.MeanSplit
import Cuisine.SensoryCore

open Matrix RealInnerProductSpace

namespace Spine

/-- The transverse (squared) area swept by two vectors. -/
noncomputable def area2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) : ℝ :=
  ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2

theorem area2_eq_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    area2 a b = (Matrix.gram ℝ ![a, b]).det := (det_gram_pair a b).symm

/-- An observer: a domain, a reading into a structured carrier, a transverse
channel, and the two nondegeneracy witnesses the inherited theorem needs. -/
structure MeanObserver (D : Type*) (n : ℕ) [NeZero n] where
  /-- The map from the domain's data into the structured carrier. -/
  read : D → EuclideanSpace ℝ (Fin n)
  /-- A second reading, used as the transverse channel. -/
  channel : D → EuclideanSpace ℝ (Fin n)
  /-- Nondegeneracy witness 1: the reading has a nonzero constant mode. -/
  mean_ne_zero : ∀ d, MeanSplit.avg (read d) ≠ 0
  /-- Nondegeneracy witness 2: the channel is not constant. -/
  fluct_ne_zero : ∀ d, MeanSplit.fluct (channel d) ≠ 0

namespace MeanObserver

variable {D : Type*} {n : ℕ} [NeZero n] (O : MeanObserver D n)

/-- The observable: the squared transverse area of the observed pair. -/
noncomputable def observedArea (d : D) : ℝ :=
  area2 (O.read d) (MeanSplit.fluct (O.channel d))

/-- **The inherited theorem.**  Both witnesses discharged, the observed pair
spans a genuine plane, with an explicit positive floor. -/
theorem transverse_area_pos (d : D) : 0 < O.observedArea d := by
  have hfloor := MeanSplit.anchored_plane_area (O.read d) (O.channel d)
  have hn : (0 : ℝ) < n := by
    have := NeZero.ne n
    positivity
  have h1 : 0 < MeanSplit.avg (O.read d) ^ 2 := by
    have := O.mean_ne_zero d; positivity
  have h2 : 0 < ‖MeanSplit.fluct (O.channel d)‖ ^ 2 := by
    have := O.fluct_ne_zero d
    have : ‖MeanSplit.fluct (O.channel d)‖ ≠ 0 := norm_ne_zero_iff.mpr this
    positivity
  have : 0 < (n : ℝ) * MeanSplit.avg (O.read d) ^ 2 * ‖MeanSplit.fluct (O.channel d)‖ ^ 2 := by
    positivity
  simp only [observedArea, area2]
  linarith

/-- The observed pair is in particular linearly independent. -/
theorem read_channel_independent (d : D) :
    LinearIndependent ℝ ![O.read d, MeanSplit.fluct (O.channel d)] := by
  have hpos : 0 < (Matrix.gram ℝ ![O.read d, MeanSplit.fluct (O.channel d)]).det := by
    rw [← area2_eq_det_gram]; exact O.transverse_area_pos d
  by_contra hdep
  have hdet : (Matrix.gram ℝ ![O.read d, MeanSplit.fluct (O.channel d)]).det = 0 := by
    by_contra hne
    refine hdep (Matrix.linearIndependent_of_posDef_gram ?_)
    rw [(Matrix.posSemidef_gram ℝ _).posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hne
  exact absurd hdet (ne_of_gt hpos)

end MeanObserver

/-- **The degeneracy control.**  An observer whose channel is constant (in
particular, a map sending all of its data to zero) has zero observed area: it
satisfies the algebra and says nothing. -/
theorem degenerate_observer_area_zero {n : ℕ} [NeZero n] (x y : EuclideanSpace ℝ (Fin n))
    (hy : ∀ i j, y i = y j) : area2 x (MeanSplit.fluct y) = 0 := by
  rw [(MeanSplit.fluct_eq_zero_iff y).mpr hy]
  simp [area2]

/-! ## Instance 1: five modes, five genuine transverse planes -/

/-- Five modes each carrying a nonzero constant part and a nonzero ternary
transverse part give **five genuine transverse planes**, each with a positive
exterior area — not merely ten labels. -/
theorem monster_five_transverse_planes
    (a t : Fin 5 → EuclideanSpace ℝ (Fin 3))
    (ha : ∀ i, MeanSplit.avg (a i) ≠ 0)
    (ht : ∀ i, MeanSplit.fluct (t i) ≠ 0) :
    ∀ i, 0 < area2 (a i) (MeanSplit.fluct (t i)) := by
  intro i
  exact (MeanObserver.transverse_area_pos
    ⟨a, t, ha, ht⟩ i)

/-! ## Instance 2: the cuisine taste carrier -/

namespace Cuisine

open Cuisine.SensoryCore

/-- The five taste dimensions, indexed. -/
def tasteIndex : Fin 5 → TasteDimension
  | 0 => TasteDimension.sweet
  | 1 => TasteDimension.salty
  | 2 => TasteDimension.sour
  | 3 => TasteDimension.bitter
  | 4 => TasteDimension.umami

theorem tasteIndex_injective : Function.Injective tasteIndex := by decide

/-- The map from cuisine data into the structured carrier: a sensory profile's
taste intensities as a real vector. -/
noncomputable def tasteVec (p : SensoryProfile) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fun i => (p.tasteIntensity (tasteIndex i) : ℝ))

@[simp] theorem tasteVec_apply (p : SensoryProfile) (i : Fin 5) :
    tasteVec p i = (p.tasteIntensity (tasteIndex i) : ℝ) := rfl

/-- The fixed component of a taste reading is its overall intensity. -/
theorem avg_tasteVec (p : SensoryProfile) :
    MeanSplit.avg (tasteVec p) = (∑ i, (p.tasteIntensity (tasteIndex i) : ℝ)) / 5 := by
  simp [MeanSplit.avg]

/-- A profile with some nonzero taste intensity has a nonzero constant mode. -/
theorem avg_ne_zero_of_pos {p : SensoryProfile} {d : TasteDimension}
    (hd : 0 < p.tasteIntensity d) (hmem : ∃ i, tasteIndex i = d) :
    MeanSplit.avg (tasteVec p) ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := hmem
  rw [avg_tasteVec]
  have hpos : 0 < ∑ i, (p.tasteIntensity (tasteIndex i) : ℝ) := by
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, ?_⟩
    rw [hi₀]; exact_mod_cast hd
  positivity

/-- A profile whose taste intensities are not all equal has a nonzero transverse
part: its *balance* is real information. -/
theorem fluct_ne_zero_of_ne {q : SensoryProfile} {i j : Fin 5}
    (hij : q.tasteIntensity (tasteIndex i) ≠ q.tasteIntensity (tasteIndex j)) :
    MeanSplit.fluct (tasteVec q) ≠ 0 := by
  intro h
  have := (MeanSplit.fluct_eq_zero_iff (tasteVec q)).mp h i j
  simp only [tasteVec_apply] at this
  exact hij (by exact_mod_cast this)

/-- **The cuisine instance of the spine theorem.**  A dish with nonzero overall
taste intensity, together with the balance direction of a dish whose taste
intensities are not all equal, spans a genuine plane: the pair is not two names
for one line. -/
theorem taste_plane_pos {p q : SensoryProfile} {d : TasteDimension} {i j : Fin 5}
    (hd : 0 < p.tasteIntensity d) (hmem : ∃ k, tasteIndex k = d)
    (hij : q.tasteIntensity (tasteIndex i) ≠ q.tasteIntensity (tasteIndex j)) :
    0 < area2 (tasteVec p) (MeanSplit.fluct (tasteVec q)) := by
  exact MeanObserver.transverse_area_pos
    (D := Unit) ⟨fun _ => tasteVec p, fun _ => tasteVec q,
      fun _ => avg_ne_zero_of_pos hd hmem, fun _ => fluct_ne_zero_of_ne hij⟩ ()

/-- **The honest negative.**  A flat profile — every taste dimension at the same
intensity — has zero transverse part, so the inherited theorem is vacuous for it.
Structure transfers only with a nondegeneracy witness. -/
theorem flat_profile_degenerate (p q : SensoryProfile)
    (hflat : ∀ d d', q.tasteIntensity d = q.tasteIntensity d') :
    area2 (tasteVec p) (MeanSplit.fluct (tasteVec q)) = 0 :=
  degenerate_observer_area_zero _ _ (fun i j => by
    simp only [tasteVec_apply]
    exact_mod_cast hflat (tasteIndex i) (tasteIndex j))

end Cuisine

end Spine
