import Mathlib
import RequestProject.Archimedes369

/-!
# Archimedes' figures as rotating objects

`RequestProject/Archimedes369.lean` puts the regular `n`-gons on the unit circle and squeezes
`π` between their perimeters.  This file makes them **turn**.

Three kinds of rotation appear.

1. *Rotation in the plane.*  The boundary of the regular `n`-gon inscribed in the unit circle
   is the polar graph of one function of the angle,

   `radius n θ = cos (π/n) / cos (wrap n θ)`,   `wrap n θ = θ − (2π/n)·round (nθ/2π)`,

   the *sawtooth* `wrap` being the angle to the nearest edge normal.  The polygon is exactly
   the `2π/n`-periodic profile: `radius_rot` is its `n`-fold rotational symmetry, and
   `cos (π/n) ≤ radius n θ ≤ 1` (`le_radius`, `radius_le_one`) says that under rotation the
   polygon sweeps the annulus between its incircle and the unit circle.  The two bounds are
   attained (`radius_edge_center`, `radius_vertex`), so they are the exact inf and sup
   (`isGLB_radius`, `isLUB_radius`), and the swept annulus has area `π sin²(π/n) → 0`: the
   spinning polygon converges to the circle.

2. *Rotation in space.*  Spin the regular `2m`-gon about one of its long diagonals.  The solid
   of revolution is a stack of `m` conical frusta; `frustum_volume` is the frustum formula as
   an honest integral, `revVolume` is the resulting sum, and

   `revVolume_eq : revVolume m = (4π/3)·cos²(π/2m)`

   is its closed form, a telescoping identity.  Hence `revVolume m → 4π/3`, the volume of the
   unit ball, and the trinity reappears at the bottom of the ladder:

   * `revVolume_two`   — the **square** spun about a diagonal has volume `2π/3`;
   * `revVolume_three` — the **hexagon** spun about a long diagonal has volume **exactly `π`**;
   * `revVolume_six`   — the twelve-gon gives `(4π/3)cos²(π/12) = π(√3+2)/3`.

3. *Rotation of the modular circle.*  The circle carrying these polygons is the arc `|z| = 1`
   of the previous sections, on which `S : z ↦ −1/z` acts as the reflection `θ ↦ π − θ`
   (`neg_inv_circle`).  The vertex set of the `n`-gon anchored at `i` is stable under `S`
   (`S_vertex`), and the corners `ρ = e^{2πi/3}` and `ρ + 1 = e^{πi/3}` of the modular
   fundamental domain are two of the twelve vertices of the regular twelve-gon
   (`vertex_twelve_one`, `vertex_twelve_neg_one`) — the same twelve-gon that gives Archimedes'
   second rung.
-/

namespace Archimedes369

open Real Filter Topology

section Plane

variable {n : ℕ}

/-- The sawtooth angle: the signed angle from `θ` to the nearest edge normal of the regular
`n`-gon whose edge midpoints sit at the multiples of `2π/n`. -/
noncomputable def wrap (n : ℕ) (θ : ℝ) : ℝ := θ - (2 * π / n) * round ((n : ℝ) * θ / (2 * π))

/-- The polar radius function of the regular `n`-gon inscribed in the unit circle, with edge
midpoints at the multiples of `2π/n` and vertices at the odd multiples of `π/n`. -/
noncomputable def radius (n : ℕ) (θ : ℝ) : ℝ := cos (π / n) / cos (wrap n θ)

lemma abs_wrap_le (hn : 3 ≤ n) (θ : ℝ) : |wrap n θ| ≤ π / n := by
  have hp := cast_pos hn
  have h : wrap n θ = (2 * π / n) * ((n : ℝ) * θ / (2 * π) - round ((n : ℝ) * θ / (2 * π))) := by
    unfold wrap; field_simp
  rw [h, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π / n)]
  calc 2 * π / n * |(n : ℝ) * θ / (2 * π) - round ((n : ℝ) * θ / (2 * π))|
      ≤ 2 * π / n * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round _) (by positivity)
    _ = π / n := by ring

/-- Rotating by one `n`-th of a turn is a symmetry of the sawtooth. -/
lemma wrap_rot (hn : 3 ≤ n) (θ : ℝ) : wrap n (θ + 2 * π / n) = wrap n θ := by
  have hp := cast_pos hn
  have h : (n : ℝ) * (θ + 2 * π / n) / (2 * π) = (n : ℝ) * θ / (2 * π) + 1 := by
    field_simp
  unfold wrap
  rw [h, round_add_one]
  push_cast
  ring

lemma cos_wrap_pos (hn : 3 ≤ n) (θ : ℝ) : 0 < cos (wrap n θ) := by
  have h := abs_wrap_le hn θ
  have h2 := pi_div_lt_pi_div_two hn
  refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
    [have := abs_le.mp h |>.1; have := abs_le.mp h |>.2] <;> linarith

lemma cos_pi_div_le_cos_wrap (hn : 3 ≤ n) (θ : ℝ) : cos (π / n) ≤ cos (wrap n θ) := by
  have h := abs_wrap_le hn θ
  have hpi := pi_div_lt_pi_div_two hn
  have : cos (π / n) ≤ cos |wrap n θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) h
  rwa [Real.cos_abs] at this

/-- **The `n`-fold rotational symmetry**: the polygon is carried onto itself by a rotation
through `2π/n`. -/
theorem radius_rot (hn : 3 ≤ n) (θ : ℝ) : radius n (θ + 2 * π / n) = radius n θ := by
  unfold radius; rw [wrap_rot hn]

/-- The boundary point at angle `θ` lies on the edge line, at distance `cos (π/n)` — the
inradius — from the centre. -/
theorem radius_mul_cos_wrap (hn : 3 ≤ n) (θ : ℝ) :
    radius n θ * cos (wrap n θ) = cos (π / n) := by
  unfold radius
  field_simp [(cos_wrap_pos hn θ).ne']

/-- The polygon is inside the unit circle. -/
theorem radius_le_one (hn : 3 ≤ n) (θ : ℝ) : radius n θ ≤ 1 := by
  have h1 := cos_wrap_pos hn θ
  have h2 := cos_pi_div_le_cos_wrap hn θ
  unfold radius
  rw [div_le_one h1]
  exact h2

/-- The polygon contains its incircle, of radius `cos (π/n)`. -/
theorem le_radius (hn : 3 ≤ n) (θ : ℝ) : cos (π / n) ≤ radius n θ := by
  have h1 := cos_wrap_pos hn θ
  have h2 : cos (wrap n θ) ≤ 1 := Real.cos_le_one _
  have h3 := (cos_pi_div_pos hn).le
  unfold radius
  rw [le_div_iff₀ h1]
  nlinarith

/-- At an edge midpoint the radius is the inradius. -/
theorem radius_edge_center (n : ℕ) : radius n 0 = cos (π / n) := by
  have : wrap n 0 = 0 := by unfold wrap; simp
  unfold radius; rw [this]; simp

/-- At a vertex the radius is `1`: the vertices are on the unit circle. -/
theorem radius_vertex (hn : 3 ≤ n) : radius n (π / n) = 1 := by
  have hp := cast_pos hn
  have hround : round ((n : ℝ) * (π / n) / (2 * π)) = 1 := by
    have h : (n : ℝ) * (π / n) / (2 * π) = 1 / 2 := by
      field_simp
    rw [h]
    norm_num [round_eq]
  have hw : wrap n (π / n) = -(π / n) := by
    unfold wrap; rw [hround]; push_cast; ring
  unfold radius
  rw [hw, Real.cos_neg]
  exact div_self (cos_pi_div_pos hn).ne'

/-- The incircle radius is exactly the infimum of the polar radius. -/
theorem isGLB_radius (hn : 3 ≤ n) : IsGLB (Set.range (radius n)) (cos (π / n)) := by
  constructor
  · rintro x ⟨θ, rfl⟩; exact le_radius hn θ
  · intro y hy
    have := hy ⟨0, rfl⟩
    rwa [radius_edge_center n] at this

/-- The circumradius `1` is exactly the supremum of the polar radius. -/
theorem isLUB_radius (hn : 3 ≤ n) : IsLUB (Set.range (radius n)) 1 := by
  constructor
  · rintro x ⟨θ, rfl⟩; exact radius_le_one hn θ
  · intro y hy
    have := hy ⟨π / n, rfl⟩
    rwa [radius_vertex hn] at this

/-- The area of the annulus swept by the spinning `n`-gon: between incircle and circumcircle. -/
noncomputable def sweptArea (n : ℕ) : ℝ := π * (1 - cos (π / n) ^ 2)

theorem sweptArea_eq (n : ℕ) : sweptArea n = π * sin (π / n) ^ 2 := by
  unfold sweptArea
  rw [Real.sin_sq]

/-- Spinning the polygon sweeps less and less: the swept annulus shrinks to nothing, which is
the geometric form of `n`-gon → circle. -/
theorem tendsto_sweptArea : Tendsto (fun n : ℕ => sweptArea n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => π * (1 - cos (π / n) ^ 2)) atTop (𝓝 (π * (1 - 1 ^ 2))) :=
    ((tendsto_cos_pi_div.pow 2).const_sub 1).const_mul π
  simpa using h

end Plane

section Revolution

/-- The volume of a conical frustum of height `h` and end radii `R`, `S`, as an integral of
`π y²` along the axis. -/
theorem frustum_volume (R S h : ℝ) (hh : 0 < h) :
    ∫ x in (0:ℝ)..h, π * (R + (S - R) * x / h) ^ 2 = π * h / 3 * (R ^ 2 + R * S + S ^ 2) := by
  have e : ∀ x : ℝ, π * (R + (S - R) * x / h) ^ 2
      = π * R ^ 2 + (2 * π * R * (S - R) / h) * x + (π * (S - R) ^ 2 / h ^ 2) * x ^ 2 := by
    intro x; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The volume of the solid obtained by spinning the regular `2m`-gon inscribed in the unit
circle about one of its long diagonals: the sum of the `m` frusta cut out by consecutive
vertices, whose heights are `cos (kπ/m) − cos ((k+1)π/m)` and whose end radii are
`sin (kπ/m)`, `sin ((k+1)π/m)`. -/
noncomputable def revVolume (m : ℕ) : ℝ :=
  (π / 3) * ∑ k ∈ Finset.range m, (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) *
    (sin ((k : ℝ) * π / m) ^ 2 + sin ((k : ℝ) * π / m) * sin (((k : ℝ) + 1) * π / m)
      + sin (((k : ℝ) + 1) * π / m) ^ 2)

/-- The telescoping identity behind the frustum sum. -/
lemma revVolume_sum (m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range m, (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) *
      (sin ((k : ℝ) * π / m) ^ 2 + sin ((k : ℝ) * π / m) * sin (((k : ℝ) + 1) * π / m)
        + sin (((k : ℝ) + 1) * π / m) ^ 2) = 2 + 2 * cos (π / m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  set f : ℕ → ℝ := fun k => (2 + cos (π / m)) * cos ((k : ℝ) * π / m) - cos ((k : ℝ) * π / m) ^ 3
    with hf
  have hterm : ∀ k : ℕ, (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) *
      (sin ((k : ℝ) * π / m) ^ 2 + sin ((k : ℝ) * π / m) * sin (((k : ℝ) + 1) * π / m)
        + sin (((k : ℝ) + 1) * π / m) ^ 2) = f k - f (k + 1) := by
    intro k
    have hc : sin ((k : ℝ) * π / m) * sin (((k : ℝ) + 1) * π / m)
        = cos (π / m) - cos ((k : ℝ) * π / m) * cos (((k : ℝ) + 1) * π / m) := by
      have hcs := Real.cos_sub (((k : ℝ) + 1) * π / m) ((k : ℝ) * π / m)
      have harg : ((k : ℝ) + 1) * π / m - (k : ℝ) * π / m = π / m := by field_simp; ring
      rw [harg] at hcs
      linarith [hcs]
    have hs1 : sin ((k : ℝ) * π / m) ^ 2 = 1 - cos ((k : ℝ) * π / m) ^ 2 := Real.sin_sq _
    have hs2 : sin (((k : ℝ) + 1) * π / m) ^ 2 = 1 - cos (((k : ℝ) + 1) * π / m) ^ 2 :=
      Real.sin_sq _
    simp only [hf]
    push_cast
    linear_combination (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) * hs1
      + (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) * hc
      + (cos ((k : ℝ) * π / m) - cos (((k : ℝ) + 1) * π / m)) * hs2
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_range_sub' f m]
  simp only [hf]
  have h0 : ((0:ℕ) : ℝ) * π / m = 0 := by simp
  have hM : ((m : ℕ) : ℝ) * π / m = π := by field_simp
  rw [h0, hM]
  simp [Real.cos_pi]
  ring

/-- **The closed form.**  The regular `2m`-gon spun about a long diagonal sweeps out a solid of
volume `(4π/3)·cos²(π/2m)` — the volume of the unit ball, shrunk by `cos²` of half the central
angle. -/
theorem revVolume_eq (m : ℕ) (hm : 0 < m) : revVolume m = (4 * π / 3) * cos (π / (2 * m)) ^ 2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hdouble : cos (π / m) = 2 * cos (π / (2 * m)) ^ 2 - 1 := by
    have h : π / m = 2 * (π / (2 * m)) := by field_simp
    rw [h, Real.cos_two_mul]
  unfold revVolume
  rw [revVolume_sum m hm, hdouble]
  ring

/-- The **square** (`m = 2`) spun about a diagonal: volume `2π/3`, half the ball. -/
theorem revVolume_two : revVolume 2 = 2 * π / 3 := by
  rw [revVolume_eq 2 (by norm_num)]
  norm_num [Real.cos_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- The **hexagon** (`m = 3`) spun about a long diagonal has volume **exactly `π`**. -/
theorem revVolume_three : revVolume 3 = π := by
  rw [revVolume_eq 3 (by norm_num)]
  norm_num [Real.cos_pi_div_six]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  ring

/-- The twelve-gon (`m = 6`) spun about a long diagonal: `(4π/3)cos²(π/12) = π(2 + √3)/3`. -/
theorem revVolume_six : revVolume 6 = π * (2 + √3) / 3 := by
  rw [revVolume_eq 6 (by norm_num)]
  have h : π / (2 * (6:ℕ)) = π / 12 := by norm_num
  rw [h, cos_pi_div_twelve]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (√3 * √2 + √2) ^ 2 = 8 + 4 * √3 := by
    linear_combination (√3 ^ 2 + 2 * √3 + 1) * h2' + 2 * h3'
  rw [h6, div_pow, key]
  ring

/-- Spinning the `2m`-gon converges to spinning the circle: the volumes tend to `4π/3`, the
volume of the unit ball. -/
theorem tendsto_revVolume : Tendsto (fun m : ℕ => revVolume m) atTop (𝓝 (4 * π / 3)) := by
  have hcos : Tendsto (fun m : ℕ => cos (π / (2 * m))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun m : ℕ => π / (2 * (m : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => (π / 2) / (m : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (π / 2)
      exact this.congr fun m => by ring_nf
    have := (Real.continuous_cos.tendsto 0).comp h0
    simpa using this
  have h : Tendsto (fun m : ℕ => (4 * π / 3) * cos (π / (2 * m)) ^ 2) atTop
      (𝓝 ((4 * π / 3) * 1 ^ 2)) := (hcos.pow 2).const_mul _
  rw [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (revVolume_eq m hm).symm

end Revolution

section ModularCircle

open Complex

/-- On the unit circle, the modular involution `S : z ↦ −1/z` is the reflection `θ ↦ π − θ`. -/
theorem neg_inv_circle (θ : ℝ) :
    -(Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = Complex.exp (((π - θ : ℝ) : ℂ) * Complex.I) := by
  have hsplit : Complex.exp (((π - θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((π : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [hsplit, Complex.exp_pi_mul_I, ← Complex.exp_neg]
  ring

/-- The angle of the `k`-th vertex of the regular `n`-gon inscribed in the unit circle and
anchored at `i`. -/
noncomputable def vertexAngle (n : ℕ) (k : ℤ) : ℝ := π / 2 + 2 * π * k / n

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle and anchored at `i`. -/
noncomputable def vertex (n : ℕ) (k : ℤ) : ℂ :=
  Complex.exp ((vertexAngle n k : ℂ) * Complex.I)

theorem vertex_zero (n : ℕ) : vertex n 0 = Complex.I := by
  have h : vertexAngle n 0 = π / 2 := by unfold vertexAngle; norm_num
  unfold vertex
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

theorem norm_vertex (n : ℕ) (k : ℤ) : ‖vertex n k‖ = 1 := by
  unfold vertex
  rw [Complex.norm_exp]
  simp

/-- The vertex set is stable under `S`: `S` swaps the `k`-th and the `(−k)`-th vertex, fixing
the anchor `i` (`k = 0`). -/
theorem S_vertex (n : ℕ) (k : ℤ) : -(vertex n k)⁻¹ = vertex n (-k) := by
  have hangle : π - vertexAngle n k = vertexAngle n (-k) := by
    unfold vertexAngle; push_cast; ring
  unfold vertex
  rw [neg_inv_circle (vertexAngle n k), hangle]

/-- `ρ = e^{2πi/3}`, a corner of the modular fundamental domain, is a vertex of the regular
twelve-gon — the polygon of Archimedes' second rung. -/
theorem vertex_twelve_one : vertex 12 1 = ⟨-(1/2), √3 / 2⟩ := by
  have h : vertexAngle 12 1 = 2 * π / 3 := by unfold vertexAngle; push_cast; ring
  have hc : Real.cos (2 * π / 3) = -(1/2) := by
    have h23 : (2 : ℝ) * π / 3 = π - π / 3 := by ring
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs : Real.sin (2 * π / 3) = √3 / 2 := by
    have h23 : (2 : ℝ) * π / 3 = π - π / 3 := by ring
    rw [h23, Real.sin_pi_sub, Real.sin_pi_div_three]
  unfold vertex
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  apply Complex.ext <;> simp

/-- `ρ + 1 = e^{πi/3}`, the other corner, is the mirror vertex. -/
theorem vertex_twelve_neg_one : vertex 12 (-1) = ⟨1/2, √3 / 2⟩ := by
  have h : vertexAngle 12 (-1) = π / 3 := by unfold vertexAngle; push_cast; ring
  unfold vertex
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp

end ModularCircle

end Archimedes369
