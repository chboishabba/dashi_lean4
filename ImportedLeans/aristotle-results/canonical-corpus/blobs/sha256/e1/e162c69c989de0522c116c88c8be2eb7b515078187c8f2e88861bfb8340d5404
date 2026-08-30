import Mathlib
import RequestProject.DeltaTriangles

/-!
# Filling the whole plane with Euclid's triangles

`RequestProject/DeltaTriangles.lean` cut each frame of the spinning `n`-gon into `n` fan
triangles and cut each of those, Euclid's way, into nine similar parts, iterated to depth `d`.
That construction only fills the *inside* of the polygon. This file subdivides all the other
space in the same way, so that the triangles fill the plane.

The device is a ladder of rings. Ring `j` is the fan of the regular `n`-gon of circumradius
`3 ^ j` — the frame of `DeltaTriangles` blown up by the same factor three that Euclid's cut
divides by — and each of its `n` triangles is cut to depth `d` exactly as before
(`tile`). Because the inradius of the `n`-gon of circumradius `R` is `R cos (π/n) ≥ R/2` for
`n ≥ 3`, ring `j` already covers the disc of radius `3 ^ j / 2`, which contains ring `j − 1`
entirely; letting `j` run over `ℕ` therefore exhausts the plane.

What is proved.

* `mem_shape_fanTri` — the fan of the unit `n`-gon covers the disc of radius `cos (π/n)`:
  the explicit barycentric coordinates of a point in its sector.
* `half_le_cos_pi_div` — `cos (π/n) ≥ 1/2` for `n ≥ 3`, so each ring swallows the previous one.
* `closedBall_subset_ring`, `iUnion_ring_eq_univ` — the rings fill the plane.
* `exists_tile`, `iUnion_tiles_eq_univ` — *the depth-`d` triangles fill the plane*: every point
  of `ℂ` lies in one of the parts `desc w (ringTri n t j k)` with `w.length = d`.
* `size_tile` — the tile of ring `j` at depth `d` has size `2 · 3 ^ j / 3 ^ d`, so along the
  diagonal `j = d` the whole plane is filled by triangles of one fixed size, and for `d > j`
  the tiles of every fixed ring shrink to points.
* `card_tiles` — a ladder of `N` rings cut to depth `d` has exactly `N · n · 9 ^ d` tiles.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Complex Real

open scoped Real BigOperators

namespace EuclidTiling

open DeltaTriangles

/-! ### The ring ladder -/

/-- The `k`-th triangle of the fan of ring `j`: the frame of `DeltaTriangles.fanTri` blown up by
`3 ^ j`. -/
def ringTri (n : ℕ) (t : ℝ) (j : ℕ) (k : ℤ) : Tri := mapTri ((3 : ℂ) ^ j) 0 (fanTri n t k)

/-- A tile of the filling: the part of ring `j`, sector `k`, addressed by the word `w`. -/
def tile (n : ℕ) (t : ℝ) (j : ℕ) (k : ℤ) (w : List (Fin 9)) : Tri := desc w (ringTri n t j k)

@[simp] lemma ringTri_zero_level (n : ℕ) (t : ℝ) (k : ℤ) : ringTri n t 0 k = fanTri n t k := by
  simp [ringTri, mapTri, fanTri]

/-- Scaling a triangle scales its size. -/
theorem size_mapTri (a b : ℂ) (T : Tri) : size (mapTri a b T) = ‖a‖ * size T := by
  have h1 : (mapTri a b T).2.1 - (mapTri a b T).1 = a * (T.2.1 - T.1) := by
    simp [mapTri]; ring
  have h2 : (mapTri a b T).2.2 - (mapTri a b T).1 = a * (T.2.2 - T.1) := by
    simp [mapTri]; ring
  rw [size, h1, h2, norm_mul, norm_mul, size]
  ring

/-- Every triangle of ring `j` has size `2 · 3 ^ j`. -/
theorem size_ringTri (n : ℕ) (t : ℝ) (j : ℕ) (k : ℤ) :
    size (ringTri n t j k) = 2 * 3 ^ j := by
  have h3 : ‖(3 : ℂ) ^ j‖ = 3 ^ j := by rw [norm_pow]; norm_num
  rw [ringTri, size_mapTri, size_fanTri, h3]
  ring

/-- **The size of a tile.** Ring `j` cut to depth `d` consists of triangles of size
`2 · 3 ^ j / 3 ^ d`. -/
theorem size_tile (n : ℕ) (t : ℝ) (j : ℕ) (k : ℤ) (w : List (Fin 9)) :
    size (tile n t j k w) = 2 * 3 ^ j / 3 ^ w.length := by
  rw [tile, size_desc, size_ringTri]

/-- Along the diagonal `j = d` the plane is filled by tiles all of the same size `2`. -/
theorem size_tile_diag (n : ℕ) (t : ℝ) (j : ℕ) (k : ℤ) (w : List (Fin 9))
    (h : w.length = j) : size (tile n t j k w) = 2 := by
  rw [size_tile, h]
  have : (3 : ℝ) ^ j ≠ 0 := by positivity
  field_simp

/-- A ladder of `N` rings, each of `n` sectors cut to depth `d`, carries exactly `N · n · 9 ^ d`
tiles. -/
theorem card_tiles (N n d : ℕ) :
    Fintype.card (Fin N × Fin n × (Fin d → Fin 9)) = N * n * 9 ^ d := by
  simp [mul_assoc]

/-! ### The fan of the unit polygon covers a disc -/

/-- For `n ≥ 3` the inradius of the unit `n`-gon is at least a half. -/
theorem half_le_cos_pi_div {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) / 2 ≤ Real.cos (π / n) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 0 < π := Real.pi_pos
  have hle : π / n ≤ π / 3 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) hn3
  have h0 : 0 ≤ π / n := by positivity
  have hpi3 : π / 3 ≤ π := by linarith
  have := Real.cos_le_cos_of_nonneg_of_le_pi h0 hpi3 hle
  rwa [Real.cos_pi_div_three] at this

/-- **The fan covers a disc.** For `n ≥ 3`, every point of the disc of radius `cos (π/n)` lies
in one of the `n` triangles of the fan of the unit `n`-gon, at every instant of the spin. -/
theorem mem_shape_fanTri (n : ℕ) (hn : 3 ≤ n) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ Real.cos (π / n)) :
    ∃ k : ℤ, z ∈ shape (fanTri n t k) := by
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpi : 0 < π := Real.pi_pos
  set g : ℝ := 2 * π / n with hgdef
  have hg0 : 0 < g := by rw [hgdef]; positivity
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hgle : g ≤ 2 * π / 3 := by
    rw [hgdef]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hn3
  have hghalf : g / 2 = π / n := by rw [hgdef]; ring
  have hcos_half : 0 < Real.cos (g / 2) := by
    rw [hghalf]
    have : (1 : ℝ) / 2 ≤ Real.cos (π / n) := half_le_cos_pi_div hn
    linarith
  have hsin_half : 0 < Real.sin (g / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_g : Real.sin g = 2 * Real.sin (g / 2) * Real.cos (g / 2) := by
    have h := Real.sin_two_mul (g / 2)
    rw [show 2 * (g / 2) = g by ring] at h
    exact h
  have hsing : 0 < Real.sin g := by rw [hsin_g]; positivity
  -- the sector containing `z`
  set c : ℝ := π / 2 + t with hcdef
  set θ : ℝ := Complex.arg z with hθdef
  set k : ℤ := ⌊(θ - c) / g⌋ with hkdef
  set φ : ℝ := θ - c - g * k with hφdef
  have hφ0 : 0 ≤ φ := by
    have h := Int.sub_floor_div_mul_nonneg (θ - c) hg0
    rw [hφdef, hkdef]
    linarith
  have hφg : φ < g := by
    have h := Int.sub_floor_div_mul_lt (θ - c) hg0
    rw [hφdef, hkdef]
    linarith
  -- barycentric coordinates
  set r : ℝ := ‖z‖ with hrdef
  set a : ℝ := r * Real.sin (g - φ) / Real.sin g with hadef
  set b : ℝ := r * Real.sin φ / Real.sin g with hbdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsinφ : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith)
  have hsingφ : 0 ≤ Real.sin (g - φ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  -- the sum bound: the two coordinates add up to at most one inside the inball
  have hsum : Real.sin (g - φ) + Real.sin φ = 2 * Real.sin (g / 2) * Real.cos (g / 2 - φ) := by
    have h1 : Real.sin (g - φ)
        = Real.sin (g / 2) * Real.cos (g / 2 - φ) + Real.cos (g / 2) * Real.sin (g / 2 - φ) := by
      rw [← Real.sin_add]; congr 1; ring
    have h2 : Real.sin φ
        = Real.sin (g / 2) * Real.cos (g / 2 - φ) - Real.cos (g / 2) * Real.sin (g / 2 - φ) := by
      rw [← Real.sin_sub]; congr 1; ring
    linarith
  have hab : a + b ≤ 1 := by
    have hcosle : Real.cos (g / 2 - φ) ≤ 1 := Real.cos_le_one _
    have hkey : a + b = r * Real.cos (g / 2 - φ) / Real.cos (g / 2) := by
      rw [hadef, hbdef, ← add_div, hsin_g]
      rw [show r * Real.sin (g - φ) + r * Real.sin φ = r * (Real.sin (g - φ) + Real.sin φ) by ring,
        hsum]
      field_simp
    have hzc : r ≤ Real.cos (g / 2) := by rw [hghalf]; exact hz
    rw [hkey, div_le_one hcos_half]
    nlinarith
  refine ⟨k, ⟨(a, b), ⟨ha0, hb0, hab⟩, ?_⟩⟩
  -- the barycentric identity
  have hangk : ArchimedesDelta.spinAngle n t k = c + g * k := by
    rw [ArchimedesDelta.spinAngle_def, hcdef, hgdef]
    ring
  have hangk1 : ArchimedesDelta.spinAngle n t (k + 1) = c + g * k + g := by
    rw [ArchimedesDelta.spinAngle_def, hcdef, hgdef]
    push_cast
    field_simp
    ring
  have hz_eq : z = (r : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) := by
    rw [hrdef, hθdef]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hbs : b * Real.sin g = r * Real.sin φ := by
    rw [hbdef]; field_simp
  have has : a + b * Real.cos g = r * Real.cos φ := by
    have hexp : Real.sin (g - φ) + Real.sin φ * Real.cos g = Real.sin g * Real.cos φ := by
      rw [Real.sin_sub]; ring
    rw [hadef, hbdef]
    field_simp
    linear_combination r * hexp
  have hexpr : ∀ x : ℝ, Complex.exp ((x : ℝ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hcore : (a : ℂ) + (b : ℂ) * Complex.exp ((g : ℝ) * Complex.I)
      = (r : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) := by
    calc (a : ℂ) + (b : ℂ) * Complex.exp ((g : ℝ) * Complex.I)
        = ((a + b * Real.cos g : ℝ) : ℂ) + ((b * Real.sin g : ℝ) : ℂ) * Complex.I := by
          rw [hexpr g]; push_cast; ring
      _ = ((r * Real.cos φ : ℝ) : ℂ) + ((r * Real.sin φ : ℝ) : ℂ) * Complex.I := by
          rw [has, hbs]
      _ = (r : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) := by
          rw [hexpr φ]; push_cast; ring
  have hθsplit : (θ : ℝ) = (c + g * k) + φ := by rw [hφdef]; ring
  simp only [para, fanTri, sub_zero, ArchimedesDelta.spinVertex, hangk, hangk1]
  rw [hz_eq, hθsplit]
  have hsplit : ((c + g * (k : ℝ) + φ : ℝ) : ℂ) * Complex.I
      = ((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I + ((φ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hsplit2 : ((c + g * (k : ℝ) + g : ℝ) : ℂ) * Complex.I
      = ((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I + ((g : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, hsplit2, Complex.exp_add, Complex.exp_add]
  calc (0 : ℂ) + (a : ℂ) * Complex.exp (((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I)
        + (b : ℂ) * (Complex.exp (((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((g : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I)
          * ((a : ℂ) + (b : ℂ) * Complex.exp (((g : ℝ) : ℂ) * Complex.I)) := by ring
    _ = Complex.exp (((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I)
          * ((r : ℂ) * Complex.exp (((φ : ℝ) : ℂ) * Complex.I)) := by rw [hcore]
    _ = (r : ℂ) * (Complex.exp (((c + g * (k : ℝ) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((φ : ℝ) : ℂ) * Complex.I)) := by ring

/-! ### The rings fill the plane -/

/-- **Ring `j` covers the disc of radius `3 ^ j cos (π/n)`.** -/
theorem mem_shape_ringTri (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (j : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 3 ^ j * Real.cos (π / n)) : ∃ k : ℤ, z ∈ shape (ringTri n t j k) := by
  have hpow : (0 : ℝ) < 3 ^ j := by positivity
  have h3 : ((3 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzz : ‖z / (3 : ℂ) ^ j‖ ≤ Real.cos (π / n) := by
    rw [norm_div, norm_pow]
    simp only [Complex.norm_ofNat]
    rw [div_le_iff₀ hpow]
    linarith [hz]
  obtain ⟨k, hk⟩ := mem_shape_fanTri n hn t hzz
  refine ⟨k, ?_⟩
  rw [ringTri, shape_mapTri]
  refine ⟨z / (3 : ℂ) ^ j, hk, ?_⟩
  field_simp
  ring

/-- Ring `j` covers the disc of radius `3 ^ j / 2`, which contains all the earlier rings. -/
theorem closedBall_subset_ring (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (j : ℕ) :
    Metric.closedBall (0 : ℂ) (3 ^ j / 2) ⊆ ⋃ k : ℤ, shape (ringTri n t j k) := by
  intro z hz
  have hnorm : ‖z‖ ≤ 3 ^ j / 2 := by
    simpa [Complex.dist_eq] using hz
  have hpow : (0 : ℝ) < 3 ^ j := by positivity
  have hcos := half_le_cos_pi_div hn
  have hb : ‖z‖ ≤ 3 ^ j * Real.cos (π / n) := by nlinarith
  obtain ⟨k, hk⟩ := mem_shape_ringTri n hn t j hb
  exact Set.mem_iUnion.2 ⟨k, hk⟩

/-- **The rings fill the plane.** -/
theorem iUnion_ring_eq_univ (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    (⋃ (j : ℕ) (k : ℤ), shape (ringTri n t j k)) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 2 * ‖z‖ < 3 ^ j := pow_unbounded_of_one_lt _ (by norm_num)
  have hmem : z ∈ Metric.closedBall (0 : ℂ) (3 ^ j / 2) := by
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    linarith
  have h := closedBall_subset_ring n hn t j hmem
  rw [Set.mem_iUnion] at h
  obtain ⟨k, hk⟩ := h
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, hk⟩⟩

/-! ### The tiles fill the plane -/

/-- **Every point of the plane lies in a tile.** For any depth `d`, every `z : ℂ` belongs to one
of the depth-`d` parts of one of the sectors of one of the rings. -/
theorem exists_tile (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (d : ℕ) (z : ℂ) :
    ∃ (j : ℕ) (k : ℤ) (w : List (Fin 9)), w.length = d ∧ z ∈ shape (tile n t j k w) := by
  have hz : z ∈ (⋃ (j : ℕ) (k : ℤ), shape (ringTri n t j k)) := by
    rw [iUnion_ring_eq_univ n hn t]; trivial
  simp only [Set.mem_iUnion] at hz
  obtain ⟨j, k, hzk⟩ := hz
  rw [shape_eq_iUnion_desc d] at hzk
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hzk
  obtain ⟨w, hw, hz'⟩ := hzk
  exact ⟨j, k, w, hw, hz'⟩

/-- **The filling of the plane by Euclid's triangles at depth `d`.** -/
theorem iUnion_tiles_eq_univ (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (d : ℕ) :
    (⋃ (j : ℕ) (k : ℤ) (w ∈ {w : List (Fin 9) | w.length = d}), shape (tile n t j k w))
      = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨j, k, w, hw, hz⟩ := exists_tile n hn t d z
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  exact ⟨j, k, w, hw, hz⟩

end EuclidTiling
