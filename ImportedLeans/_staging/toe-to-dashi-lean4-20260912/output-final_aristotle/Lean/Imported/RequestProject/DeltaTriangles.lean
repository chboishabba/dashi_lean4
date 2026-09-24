import Mathlib
import RequestProject.ArchimedesDelta

/-!
# Triangles: cutting each frame of the spinning polygon into nine, and reading `Δ` on the parts

This file is the theory behind the animated plate `paper/delta_triangles_spin.svg` and its
static companion `paper/delta_triangles.svg`.

The construction is the one the plate draws, in three steps.

1. **From polygon to triangles.** Each frame of the spinning `n`-gon of
   `RequestProject/ArchimedesDelta.lean` is cut into `n` triangles by the fan from the centre:
   `fanTri n t k` has vertices `0`, `v_n(t,k)`, `v_n(t,k+1)`.
2. **Euclid on a triangle.** A triangle is cut into **nine** by trisecting each of its sides:
   six that point the same way as the parent and three that point the other way (`child`,
   `shape_eq_iUnion_child`). Iterating a word `w` of length `d` in the nine children
   (`desc`) gives `9 ^ d` parts (`card_words`) whose union is the parent
   (`shape_eq_iUnion_desc`) and whose size is the parent's divided by `3 ^ d`
   (`size_desc`) — the exact ternary analogue of the square dissection of
   `RequestProject/DeltaDissection.lean`.
3. **The reading.** Each part is painted with `reading T = ‖Δ‖` at its centroid
   (`centroid_mem_shape`), and the parts of a frame are sorted by that colour
   (`sortedReadings`).

What is proved.

* `shape_eq_iUnion_child`, `shape_eq_iUnion_desc`, `card_words`, `size_desc`,
  `dist_le_size` — the dissection is a genuine cover by `9 ^ d` parts that shrink to points.
* `child_mapTri`, `desc_mapTri`, `shape_mapTri` — the dissection commutes with every complex
  affine map, so *the parts of frame `t` are the parts of frame `0`, rotated*
  (`desc_fanTri_rot`): one dissection serves the whole animation.
* `child_conjTri`, `reading_conjTri` — the dissection also commutes with the vertical mirror
  `z ↦ −z̄`, under which the reading is unchanged (`DeltaModular.Delta_neg_conj`).
* `readings_rot`, `sortedReadings_rot` — the colour-sorted list of all `n · 9 ^ d` readings of a
  frame is unchanged after a rotation by `2π/n`: the sorted palette of the animation has the
  same loop as the animation itself.
* `dist_circle_spinVertexSet_le` — how the polygons approximate the curve they are inscribed
  in: every point of the arc `|z| = 1` is within `π/n` of a vertex of the `n`-gon, at every
  instant, so the frames converge to the circle as `n → ∞` (`tendsto_dist_circle`), while their
  perimeters converge to `2π` (`Archimedes369.tendsto_lower`).
-/

noncomputable section

open Complex Real

open scoped Real BigOperators

namespace DeltaTriangles

/-! ### Triangles and their barycentric parametrisation -/

/-- A triangle, as its ordered triple of vertices. -/
abbrev Tri : Type := ℂ × ℂ × ℂ

/-- The standard parameter triangle `{(x,y) : x, y ≥ 0, x + y ≤ 1}`. -/
def stdTri : Set (ℝ × ℝ) := {u | 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ 1}

/-- The barycentric parametrisation of a triangle. -/
def para (T : Tri) (u : ℝ × ℝ) : ℂ :=
  T.1 + (u.1 : ℂ) * (T.2.1 - T.1) + (u.2 : ℂ) * (T.2.2 - T.1)

/-- The filled triangle: the image of the standard parameter triangle. -/
def shape (T : Tri) : Set ℂ := para T '' stdTri

@[simp] lemma para_zero (T : Tri) : para T (0, 0) = T.1 := by simp [para]

lemma para_one_zero (T : Tri) : para T (1, 0) = T.2.1 := by simp [para]

lemma para_zero_one (T : Tri) : para T (0, 1) = T.2.2 := by simp [para]

/-! ### The affine substitutions that cut a triangle into nine -/

/-- The affine substitution `u ↦ (α + s·u₁, β + s·u₂)` of the parameter triangle. -/
def aff (α β s : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (α + s * u.1, β + s * u.2)

/-- The triangle whose parametrisation is `para T ∘ aff α β s`. -/
def affTri (α β s : ℝ) (T : Tri) : Tri :=
  (para T (α, β), para T (α + s, β), para T (α, β + s))

lemma para_aff (α β s : ℝ) (T : Tri) (u : ℝ × ℝ) :
    para T (aff α β s u) = para (affTri α β s T) u := by
  simp only [para, aff, affTri]
  push_cast
  ring

/-- The nine children of Euclid's ternary cut, as parameters `(α, β, s)`: six upward parts with
`s = 1/3` and three downward parts with `s = −1/3`. -/
def childP : Fin 9 → ℝ × ℝ × ℝ :=
  ![(0, 0, 1/3), (1/3, 0, 1/3), (2/3, 0, 1/3), (0, 1/3, 1/3), (1/3, 1/3, 1/3),
    (0, 2/3, 1/3), (1/3, 1/3, -(1/3)), (2/3, 1/3, -(1/3)), (1/3, 2/3, -(1/3))]

/-- The `n`-th child substitution on parameters. -/
def childMap (n : Fin 9) : ℝ × ℝ → ℝ × ℝ := aff (childP n).1 (childP n).2.1 (childP n).2.2

/-- The `n`-th of the nine parts of `T`. -/
def child (n : Fin 9) (T : Tri) : Tri := affTri (childP n).1 (childP n).2.1 (childP n).2.2 T

lemma para_childMap (n : Fin 9) (T : Tri) (u : ℝ × ℝ) :
    para T (childMap n u) = para (child n T) u := para_aff _ _ _ T u

/-- Every child substitution maps the parameter triangle into itself. -/
theorem childMap_mapsTo (n : Fin 9) : Set.MapsTo (childMap n) stdTri stdTri := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := hu
  fin_cases n <;>
    refine ⟨by simp [childMap, aff, childP]; linarith,
      by simp [childMap, aff, childP]; linarith,
      by simp [childMap, aff, childP]; linarith⟩

/-- **Euclid's ternary cut of the parameter triangle.** Every point of it lies in one of the
nine parts. -/
theorem stdTri_subset_iUnion_childMap :
    stdTri ⊆ ⋃ n : Fin 9, childMap n '' stdTri := by
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  simp only [Set.mem_iUnion, Set.mem_image]
  have key : ∃ (n : Fin 9) (v : ℝ × ℝ), v ∈ stdTri ∧ childMap n v = (x, y) := by
    rcases le_or_gt (3 * x) 1 with hx1 | hx1
    · rcases le_or_gt (3 * y) 1 with hy1 | hy1
      · rcases le_or_gt (3 * x + 3 * y) 1 with hs | hs
        · exact ⟨0, (3 * x, 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
            refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
        · exact ⟨6, (1 - 3 * x, 1 - 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
            refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
      · rcases le_or_gt (3 * y) 2 with hy2 | hy2
        · rcases le_or_gt (3 * x + 3 * y) 2 with hs | hs
          · exact ⟨3, (3 * x, 3 * y - 1), ⟨by linarith, by linarith, by linarith⟩, by
              refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
          · exact ⟨8, (1 - 3 * x, 2 - 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
              refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
        · exact ⟨5, (3 * x, 3 * y - 2), ⟨by linarith, by linarith, by linarith⟩, by
            refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
    · rcases le_or_gt (3 * y) 1 with hy1 | hy1
      · rcases le_or_gt (3 * x) 2 with hx2 | hx2
        · rcases le_or_gt (3 * x + 3 * y) 2 with hs | hs
          · exact ⟨1, (3 * x - 1, 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
              refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
          · exact ⟨7, (2 - 3 * x, 1 - 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
              refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
        · exact ⟨2, (3 * x - 2, 3 * y), ⟨by linarith, by linarith, by linarith⟩, by
            refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
      · exact ⟨4, (3 * x - 1, 3 * y - 1), ⟨by linarith, by linarith, by linarith⟩, by
          refine Prod.ext ?_ ?_ <;> (simp [childMap, aff, childP]; try ring)⟩
  obtain ⟨n, v, hv, hvxy⟩ := key
  exact ⟨n, v, hv, hvxy⟩

/-- **The nine parts of a triangle.** Cutting the sides in three cuts the triangle into nine. -/
theorem shape_eq_iUnion_child (T : Tri) : shape T = ⋃ n : Fin 9, shape (child n T) := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    obtain ⟨s, ⟨n, rfl⟩, v, hv, rfl⟩ := stdTri_subset_iUnion_childMap hu
    exact Set.mem_iUnion.2 ⟨n, ⟨v, hv, (para_childMap n T v).symm⟩⟩
  · refine Set.iUnion_subset fun n => ?_
    rintro z ⟨v, hv, rfl⟩
    exact ⟨childMap n v, childMap_mapsTo n hv, para_childMap n T v⟩

/-! ### Size, and the shrinking of the parts -/

/-- A size for a triangle: the sum of the two side vectors from the first vertex. It bounds the
diameter (`dist_le_size`) and is divided by three by each cut (`size_child`). -/
def size (T : Tri) : ℝ := ‖T.2.1 - T.1‖ + ‖T.2.2 - T.1‖

theorem size_nonneg (T : Tri) : 0 ≤ size T := add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Any two points of a triangle are at distance at most its size. -/
theorem dist_le_size {T : Tri} {z w : ℂ} (hz : z ∈ shape T) (hw : w ∈ shape T) :
    ‖z - w‖ ≤ size T := by
  obtain ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩ := hz
  obtain ⟨v, ⟨hv1, hv2, hv3⟩, rfl⟩ := hw
  have hdiff : para T u - para T v
      = ((u.1 - v.1 : ℝ) : ℂ) * (T.2.1 - T.1) + ((u.2 - v.2 : ℝ) : ℂ) * (T.2.2 - T.1) := by
    simp only [para]; push_cast; ring
  have h1 : |u.1 - v.1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2 : |u.2 - v.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have e1 : ‖((u.1 - v.1 : ℝ) : ℂ) * (T.2.1 - T.1)‖ ≤ 1 * ‖T.2.1 - T.1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have e2 : ‖((u.2 - v.2 : ℝ) : ℂ) * (T.2.2 - T.1)‖ ≤ 1 * ‖T.2.2 - T.1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  calc ‖para T u - para T v‖
      ≤ ‖((u.1 - v.1 : ℝ) : ℂ) * (T.2.1 - T.1)‖ + ‖((u.2 - v.2 : ℝ) : ℂ) * (T.2.2 - T.1)‖ := by
        rw [hdiff]; exact norm_add_le _ _
    _ ≤ 1 * ‖T.2.1 - T.1‖ + 1 * ‖T.2.2 - T.1‖ := add_le_add e1 e2
    _ = size T := by simp [size]

/-- Each of the nine parts has exactly a third of the size of the parent. -/
theorem size_child (n : Fin 9) (T : Tri) : size (child n T) = size T / 3 := by
  have hs : |(childP n).2.2| = 1/3 := by fin_cases n <;> norm_num [childP]
  have h1 : (child n T).2.1 - (child n T).1
      = (((childP n).2.2 : ℝ) : ℂ) * (T.2.1 - T.1) := by
    simp only [child, affTri, para]; push_cast; ring
  have h2 : (child n T).2.2 - (child n T).1
      = (((childP n).2.2 : ℝ) : ℂ) * (T.2.2 - T.1) := by
    simp only [child, affTri, para]; push_cast; ring
  rw [size, h1, h2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hs, size]
  ring

/-! ### Words: the parts `d` levels down -/

/-- The part of `T` addressed by the word `w` in the nine children. -/
def desc (w : List (Fin 9)) (T : Tri) : Tri := w.foldl (fun S n => child n S) T

@[simp] lemma desc_nil (T : Tri) : desc [] T = T := rfl

@[simp] lemma desc_cons (n : Fin 9) (w : List (Fin 9)) (T : Tri) :
    desc (n :: w) T = desc w (child n T) := rfl

/-- The parts `d` levels down have size `3⁻ᵈ` times the parent's. -/
theorem size_desc (w : List (Fin 9)) (T : Tri) : size (desc w T) = size T / 3 ^ w.length := by
  induction w generalizing T with
  | nil => simp
  | cons n w ih => rw [desc_cons, ih, size_child]; simp [pow_succ]; ring

/-- **The dissection `d` levels down.** The parts addressed by the words of length `d` cover the
triangle. -/
theorem shape_eq_iUnion_desc (d : ℕ) (T : Tri) :
    shape T = ⋃ w ∈ {w : List (Fin 9) | w.length = d}, shape (desc w T) := by
  induction d generalizing T with
  | zero =>
      apply Set.Subset.antisymm
      · intro z hz
        exact Set.mem_biUnion (by simp : ([] : List (Fin 9)) ∈ {w : List (Fin 9) | w.length = 0})
          (by simpa using hz)
      · refine Set.iUnion₂_subset fun w hw => ?_
        have : w = [] := List.length_eq_zero_iff.mp hw
        subst this
        simp
  | succ d ih =>
      rw [shape_eq_iUnion_child T]
      apply Set.Subset.antisymm
      · refine Set.iUnion_subset fun n => ?_
        rw [ih (child n T)]
        refine Set.iUnion₂_subset fun w hw => ?_
        have hmem : (n :: w) ∈ {w : List (Fin 9) | w.length = d + 1} := by
          simp only [Set.mem_setOf_eq, List.length_cons] at hw ⊢
          omega
        have heq : shape (desc w (child n T)) = shape (desc (n :: w) T) := rfl
        rw [heq]
        exact Set.subset_biUnion_of_mem (u := fun w => shape (desc w T)) hmem
      · refine Set.iUnion₂_subset fun w hw => ?_
        simp only [Set.mem_setOf_eq] at hw
        obtain ⟨n, v, rfl, hv⟩ : ∃ (n : Fin 9) (v : List (Fin 9)), w = n :: v ∧ v.length = d := by
          cases w with
          | nil => simp at hw
          | cons n v => exact ⟨n, v, rfl, by simpa using hw⟩
        refine Set.subset_iUnion_of_subset n ?_
        rw [ih (child n T)]
        exact Set.subset_biUnion_of_mem (u := fun w => shape (desc w (child n T)))
          (by simpa using hv)

/-- There are exactly `9 ^ d` parts `d` levels down. -/
theorem card_words (d : ℕ) : Fintype.card (Fin d → Fin 9) = 9 ^ d := by
  simp

/-! ### The dissection commutes with the motions of the plate -/

/-- A complex affine map applied to a triangle. -/
def mapTri (a b : ℂ) (T : Tri) : Tri := (a * T.1 + b, a * T.2.1 + b, a * T.2.2 + b)

lemma para_mapTri (a b : ℂ) (T : Tri) (u : ℝ × ℝ) :
    para (mapTri a b T) u = a * para T u + b := by
  simp only [para, mapTri]; ring

/-- Cutting commutes with every complex affine map. -/
theorem child_mapTri (n : Fin 9) (a b : ℂ) (T : Tri) :
    child n (mapTri a b T) = mapTri a b (child n T) := by
  simp only [child, affTri, mapTri, para]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- Hence so does the whole dissection, at every depth. -/
theorem desc_mapTri (w : List (Fin 9)) (a b : ℂ) (T : Tri) :
    desc w (mapTri a b T) = mapTri a b (desc w T) := by
  induction w generalizing T with
  | nil => rfl
  | cons n w ih => rw [desc_cons, child_mapTri, ih, desc_cons]

theorem shape_mapTri (a b : ℂ) (T : Tri) :
    shape (mapTri a b T) = (fun z => a * z + b) '' shape T := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨para T u, ⟨u, hu, rfl⟩, (para_mapTri a b T u).symm⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, para_mapTri a b T u⟩

/-- The vertical mirror `z ↦ −z̄` applied to a triangle. -/
def conjTri (T : Tri) : Tri := (-(starRingEnd ℂ) T.1, -(starRingEnd ℂ) T.2.1,
  -(starRingEnd ℂ) T.2.2)

lemma para_conjTri (T : Tri) (u : ℝ × ℝ) :
    para (conjTri T) u = -(starRingEnd ℂ) (para T u) := by
  simp only [para, conjTri, map_add, map_mul, map_sub, Complex.conj_ofReal]
  ring

/-- The dissection commutes with the vertical mirror too, child by child. -/
theorem child_conjTri (n : Fin 9) (T : Tri) : child n (conjTri T) = conjTri (child n T) := by
  simp only [child, affTri, conjTri, para, map_add, map_mul, map_sub, Complex.conj_ofReal]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> push_cast <;> ring

theorem desc_conjTri (w : List (Fin 9)) (T : Tri) : desc w (conjTri T) = conjTri (desc w T) := by
  induction w generalizing T with
  | nil => rfl
  | cons n w ih => rw [desc_cons, child_conjTri, ih, desc_cons]

/-! ### The fan triangulation of a frame -/

/-- The `k`-th triangle of the fan from the centre of the spinning `n`-gon at time `t`. -/
def fanTri (n : ℕ) (t : ℝ) (k : ℤ) : Tri :=
  (0, ArchimedesDelta.spinVertex n t k, ArchimedesDelta.spinVertex n t (k + 1))

/-- Turning the frame turns the fan: `fanTri n t k` is `fanTri n 0 k` rotated by `t`. -/
theorem fanTri_rot (n : ℕ) (t : ℝ) (k : ℤ) :
    fanTri n t k = mapTri (Complex.exp ((t : ℂ) * Complex.I)) 0 (fanTri n 0 k) := by
  have h : ∀ j : ℤ, ArchimedesDelta.spinVertex n t j
      = Complex.exp ((t : ℂ) * Complex.I) * ArchimedesDelta.spinVertex n 0 j := by
    intro j
    unfold ArchimedesDelta.spinVertex
    rw [← Complex.exp_add]
    congr 1
    rw [ArchimedesDelta.spinAngle_def, ArchimedesDelta.spinAngle_def]
    push_cast
    ring
  simp only [fanTri, mapTri, h]
  norm_num

/-- **One dissection serves the whole animation.** Every part of every frame is the
corresponding part of the frame `t = 0`, rotated by `t`. -/
theorem desc_fanTri_rot (w : List (Fin 9)) (n : ℕ) (t : ℝ) (k : ℤ) :
    desc w (fanTri n t k)
      = mapTri (Complex.exp ((t : ℂ) * Complex.I)) 0 (desc w (fanTri n 0 k)) := by
  rw [fanTri_rot, desc_mapTri]

/-- Each fan triangle has size `2`: two unit radii. -/
theorem size_fanTri (n : ℕ) (t : ℝ) (k : ℤ) : size (fanTri n t k) = 2 := by
  simp only [size, fanTri, sub_zero, ArchimedesDelta.norm_spinVertex]
  norm_num

/-- So the parts `d` levels down of any frame have size `2/3ᵈ`. -/
theorem size_desc_fanTri (w : List (Fin 9)) (n : ℕ) (t : ℝ) (k : ℤ) :
    size (desc w (fanTri n t k)) = 2 / 3 ^ w.length := by
  rw [size_desc, size_fanTri]

/-! ### The reading, and the sorted palette of a frame -/

/-- The centroid of a triangle. -/
def centroidT (T : Tri) : ℂ := (T.1 + T.2.1 + T.2.2) / 3

theorem centroid_mem_shape (T : Tri) : centroidT T ∈ shape T := by
  refine ⟨(1/3, 1/3), ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  simp only [para, centroidT]
  push_cast
  ring

/-- The colour of a part: `‖Δ‖` at its centroid. -/
def reading (T : Tri) : ℝ := ‖DeltaModular.Delta (centroidT T)‖

lemma centroidT_conjTri (T : Tri) : centroidT (conjTri T) = -(starRingEnd ℂ) (centroidT T) := by
  simp only [centroidT, conjTri, map_add, map_div₀, map_ofNat]
  ring

/-- The mirror `z ↦ −z̄` leaves the colour of a part unchanged. -/
theorem reading_conjTri {T : Tri} (h : 0 < (centroidT T).im) :
    reading (conjTri T) = reading T := by
  rw [reading, centroidT_conjTri, DeltaModular.Delta_neg_conj h, reading, RCLike.norm_conj]

/-- The colours of the `9 ^ d` parts of one triangle of the fan. -/
def frameReadings (n : ℕ) (t : ℝ) (d : ℕ) (k : ℤ) : Multiset ℝ :=
  (Finset.univ : Finset (Fin d → Fin 9)).val.map fun v =>
    reading (desc (List.ofFn v) (fanTri n t k))

/-- The multiset of all `n · 9 ^ d` colours of a frame. -/
def readings (n : ℕ) (t : ℝ) (d : ℕ) : Multiset ℝ :=
  ∑ k ∈ Finset.range n, frameReadings n t d (k : ℤ)

@[simp] theorem card_frameReadings (n : ℕ) (t : ℝ) (d : ℕ) (k : ℤ) :
    Multiset.card (frameReadings n t d k) = 9 ^ d := by
  simp [frameReadings]

/-- A frame carries exactly `n · 9 ^ d` coloured parts. -/
theorem card_readings (n : ℕ) (t : ℝ) (d : ℕ) :
    Multiset.card (readings n t d) = n * 9 ^ d := by
  simp [readings, Multiset.card_sum]

/-- Shifting the vertex index by `n` does not move the vertex. -/
lemma spinVertex_add_nat (n : ℕ) (hn : 0 < n) (t : ℝ) (k : ℤ) :
    ArchimedesDelta.spinVertex n t (k + n) = ArchimedesDelta.spinVertex n t k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hang : ArchimedesDelta.spinAngle n t (k + n)
      = ArchimedesDelta.spinAngle n t k + 2 * π := by
    rw [ArchimedesDelta.spinAngle_def, ArchimedesDelta.spinAngle_def]
    have key : 2 * π * (((k + n : ℤ)) : ℝ) / n = 2 * π * ((k : ℤ) : ℝ) / n + 2 * π := by
      push_cast
      field_simp
    rw [key]
    ring
  unfold ArchimedesDelta.spinVertex
  rw [hang]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Rotating the frame by `2π/n` shifts the fan by one triangle. -/
theorem fanTri_shift (n : ℕ) (hn : 0 < n) (t : ℝ) (k : ℤ) :
    fanTri n (t + 2 * π / n) k = fanTri n t (k + 1) := by
  have h : t + 2 * π / n = t + 2 * π * ((1 : ℤ) : ℝ) / n := by norm_num
  simp only [fanTri, h, ArchimedesDelta.spinVertex_shift hn t k 1,
    ArchimedesDelta.spinVertex_shift hn t (k + 1) 1]

/-- A cyclic shift of a sum over `range (m+1)`, when the function wraps around. -/
lemma sum_range_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ)
    (h : f (m + 1) = f 0) :
    ∑ k ∈ Finset.range (m + 1), f (k + 1) = ∑ k ∈ Finset.range (m + 1), f k := by
  rw [Finset.sum_range_succ, h, ← Finset.sum_range_succ' f m]

/-- **The palette loops with the animation.** After a rotation by `2π/n` the frame shows exactly
the same multiset of colours. -/
theorem readings_rot (n : ℕ) (hn : 0 < n) (t : ℝ) (d : ℕ) :
    readings n (t + 2 * π / n) d = readings n t d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hstep : ∀ k : ℕ, frameReadings (m + 1) (t + 2 * π / ((m + 1 : ℕ) : ℝ)) d (k : ℤ)
      = frameReadings (m + 1) t d (((k + 1 : ℕ)) : ℤ) := by
    intro k
    have h : fanTri (m + 1) (t + 2 * π / ((m + 1 : ℕ) : ℝ)) (k : ℤ)
        = fanTri (m + 1) t ((k : ℤ) + 1) := fanTri_shift (m + 1) hn t (k : ℤ)
    have hc : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    simp only [frameReadings, h, hc]
  have hwrap : frameReadings (m + 1) t d ((m + 1 : ℕ) : ℤ) = frameReadings (m + 1) t d ((0 : ℕ) : ℤ) := by
    simp only [frameReadings, fanTri]
    have h1 : ArchimedesDelta.spinVertex (m + 1) t ((m + 1 : ℕ) : ℤ)
        = ArchimedesDelta.spinVertex (m + 1) t ((0 : ℕ) : ℤ) := by
      have h := spinVertex_add_nat (m + 1) hn t 0
      simpa using h
    have h2 : ArchimedesDelta.spinVertex (m + 1) t (((m + 1 : ℕ) : ℤ) + 1)
        = ArchimedesDelta.spinVertex (m + 1) t (((0 : ℕ) : ℤ) + 1) := by
      have h := spinVertex_add_nat (m + 1) hn t 1
      have hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 := by ring
      rw [hc] at h
      simpa using h
    rw [h1, h2]
  have key := sum_range_shift (fun k : ℕ => frameReadings (m + 1) t d (k : ℤ)) m hwrap
  calc readings (m + 1) (t + 2 * π / ((m + 1 : ℕ) : ℝ)) d
      = ∑ k ∈ Finset.range (m + 1), frameReadings (m + 1) t d (((k + 1 : ℕ)) : ℤ) :=
        Finset.sum_congr rfl fun k _ => hstep k
    _ = ∑ k ∈ Finset.range (m + 1), frameReadings (m + 1) t d ((k : ℕ) : ℤ) := key
    _ = readings (m + 1) t d := rfl

/-- The colours of a frame, sorted. -/
def sortedReadings (n : ℕ) (t : ℝ) (d : ℕ) : List ℝ := (readings n t d).sort (· ≤ ·)

/-- Sorting a frame by colour gives a list that is unchanged by the loop of the animation. -/
theorem sortedReadings_rot (n : ℕ) (hn : 0 < n) (t : ℝ) (d : ℕ) :
    sortedReadings n (t + 2 * π / n) d = sortedReadings n t d := by
  rw [sortedReadings, sortedReadings, readings_rot n hn t d]

/-! ### How the polygons approximate the curve -/

/-- Chords are shorter than arcs: `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
theorem norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  set c : ℝ := a - b with hc
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp ((c : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, hc]
    push_cast
    ring_nf
  have hb : ‖Complex.exp ((b : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hsq : ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos c := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq c]
  have hcos : 2 - 2 * Real.cos c ≤ c ^ 2 := by
    rcases eq_or_ne c 0 with h | h
    · simp [h]
    · have := Real.one_sub_sq_div_two_lt_cos h
      linarith
  have hle : ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ ≤ |c| := by
    have h0 : (0 : ℝ) ≤ ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ := norm_nonneg _
    nlinarith [sq_abs c, abs_nonneg c]
  rw [hfac, norm_mul, hb, one_mul]
  exact hle

/-- **Polygons approximate the circle.** At every instant, every point of the arc `|z| = 1` is
within `π/n` of a vertex of the spinning `n`-gon. -/
theorem dist_circle_spinVertexSet_le (n : ℕ) (hn : 0 < n) (t : ℝ) (θ : ℝ) :
    ∃ k : ℤ, ‖Complex.exp ((θ : ℂ) * Complex.I) - ArchimedesDelta.spinVertex n t k‖ ≤ π / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set c : ℝ := π / 2 + t with hcdef
  set x : ℝ := (θ - c) * n / (2 * π) with hxdef
  refine ⟨round x, ?_⟩
  have hangle : ArchimedesDelta.spinAngle n t (round x) = c + 2 * π * (round x : ℝ) / n := by
    rw [ArchimedesDelta.spinAngle_def, hcdef]
  have hdiff : θ - ArchimedesDelta.spinAngle n t (round x)
      = (2 * π / n) * (x - (round x : ℝ)) := by
    rw [hangle, hxdef]
    field_simp
    ring
  have hbound : |θ - ArchimedesDelta.spinAngle n t (round x)| ≤ π / n := by
    rw [hdiff, abs_mul]
    have h1 : |2 * π / n| = 2 * π / n := abs_of_nonneg (by positivity)
    have h2 : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    calc |2 * π / n| * |x - (round x : ℝ)| = (2 * π / n) * |x - (round x : ℝ)| := by rw [h1]
      _ ≤ (2 * π / n) * (1 / 2) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = π / n := by ring
  calc ‖Complex.exp ((θ : ℂ) * Complex.I) - ArchimedesDelta.spinVertex n t (round x)‖
      = ‖Complex.exp ((θ : ℂ) * Complex.I)
          - Complex.exp (((ArchimedesDelta.spinAngle n t (round x) : ℝ) : ℂ) * Complex.I)‖ := rfl
    _ ≤ |θ - ArchimedesDelta.spinAngle n t (round x)| := norm_exp_sub_exp_le _ _
    _ ≤ π / n := hbound

/-- Hence the frames converge to the circle they are inscribed in. -/
theorem tendsto_dist_circle :
    Filter.Tendsto (fun n : ℕ => π / n) Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat π

end DeltaTriangles
