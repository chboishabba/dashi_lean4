/-
# Orbiting and zooming the three-dimensional picture

`RequestProject/MonsterSpiral3DSvg.lean` draws the six panels of
`visualization/monster-spiral-3d.svg` from one fixed camera each.  The animated,
zoomed-in versions of those panels (`visualization/monster-spiral-3d-panel-a.svg`, …,
`-panel-f.svg`, rendered by `RequestProject/MonsterSpiral3DAnim.lean`) show the *same*
geometry from a camera that walks once around the vertical axis, one frame per azimuth
`2πk/N`, and enlarged to fill its own canvas.

This file proves that the two operations the animation performs — orbiting and zooming —
do not change the object being looked at:

* `rotZ` (rotation about the height axis) is a one-parameter group (`rotZ_add`), fixes the
  height (`rotZ_height`), preserves the distance from the axis (`rotZ_radius`) and all
  distances (`dist3_rotZ`), so it maps the horn `r = e^{-σz}` to itself
  (`rotZ_mem_horn`) and carries the universal helix to itself up to a phase
  (`rotZ_helix3`);
* the frame azimuths `frameAz N k = 2πk/N` are strictly increasing in `k`
  (`frameAz_strictMono`) and the loop closes exactly: after `N` frames the scene is back
  where it started (`rotZ_frameAz_last`);
* zooming, `scale3 c`, multiplies every distance by `|c|` (`dist3_scale3`), so it is a
  similarity: the zoomed panel is a faithful enlargement.
-/
import Mathlib
import RequestProject.MonsterSpiral3D

open Real Complex

set_option autoImplicit false

namespace SpiralOrbit

open MonsterSpiral3D

/-! ## Rotation about the height axis -/

/-- Rotation of `ℝ³` by the angle `a` about the vertical (height) axis: the motion the
animation performs between frames. -/
noncomputable def rotZ (a : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos a * p.1 - Real.sin a * p.2.1, Real.sin a * p.1 + Real.cos a * p.2.1, p.2.2)

@[simp] theorem rotZ_height (a : ℝ) (p : ℝ × ℝ × ℝ) : (rotZ a p).2.2 = p.2.2 := rfl

@[simp] theorem rotZ_zero (p : ℝ × ℝ × ℝ) : rotZ 0 p = p := by
  simp [rotZ]

/-- **Orbiting is a one-parameter group.** -/
theorem rotZ_add (a b : ℝ) (p : ℝ × ℝ × ℝ) : rotZ a (rotZ b p) = rotZ (a + b) p := by
  simp only [rotZ, Real.cos_add, Real.sin_add]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp <;> ring

/-- A full turn is the identity: the animation loops seamlessly. -/
@[simp] theorem rotZ_two_pi (p : ℝ × ℝ × ℝ) : rotZ (2 * π) p = p := by
  simp [rotZ]

/-- The distance from the vertical axis — the radius on the horn — is unchanged. -/
theorem rotZ_radius (a : ℝ) (p : ℝ × ℝ × ℝ) :
    (rotZ a p).1 ^ 2 + (rotZ a p).2.1 ^ 2 = p.1 ^ 2 + p.2.1 ^ 2 := by
  have h : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  simp only [rotZ]
  nlinarith [h]

/-- The euclidean norm of a point of `ℝ³`. -/
noncomputable def nrm3 (p : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

/-- The euclidean distance between two points of `ℝ³`. -/
noncomputable def dist3 (p q : ℝ × ℝ × ℝ) : ℝ := nrm3 (p.1 - q.1, p.2.1 - q.2.1, p.2.2 - q.2.2)

/-- **Orbiting is a rigid motion**: every distance in the scene is preserved, so each frame
of the animation shows the same solid from a different side. -/
theorem dist3_rotZ (a : ℝ) (p q : ℝ × ℝ × ℝ) : dist3 (rotZ a p) (rotZ a q) = dist3 p q := by
  have h : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  simp only [dist3, nrm3, rotZ]
  congr 1
  nlinarith [h]

/-! ## The horn and the helix under rotation -/

/-- The horn `r = e^{-σz}` of `MonsterSpiral3D.norm_helixC`, as a subset of `ℝ³`. -/
def horn (sigma : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) = Real.exp (-(sigma * p.2.2))}

/-- **The horn is invariant under the orbit**, so the animation never changes the surface
the helix is drawn on. -/
theorem rotZ_mem_horn (sigma a : ℝ) {p : ℝ × ℝ × ℝ} (hp : p ∈ horn sigma) :
    rotZ a p ∈ horn sigma := by
  simp only [horn, Set.mem_setOf_eq] at hp ⊢
  rw [rotZ_radius a p, rotZ_height]
  exact hp

/-- Every point of the lifted helix lies on the horn. -/
theorem helix3_mem_horn (sigma t z : ℝ) : helix3 sigma t z ∈ horn sigma := by
  simpa [horn, Set.mem_setOf_eq] using helix3_radius sigma t z

/-- **Rotating the scene by `a` is multiplying the plane coordinate by `e^{ia}`.**  Hence
the orbit carries the universal helix to itself with its phase shifted, which is the
screw symmetry `MonsterSpiral3D.helixC_shift` seen from the camera's side. -/
theorem rotZ_helix3 (sigma t z a : ℝ) :
    rotZ a (helix3 sigma t z) = lift3 (Complex.exp (a * Complex.I) * helixC sigma t z) z := by
  simp only [rotZ, lift3, helix3, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> (simp; try ring)

/-! ## The frames of the orbit -/

/-- The azimuth of frame `k` of an `N`-frame orbit. -/
noncomputable def frameAz (N k : ℕ) : ℝ := 2 * π * k / N

@[simp] theorem frameAz_zero (N : ℕ) : frameAz N 0 = 0 := by simp [frameAz]

/-- The frames sweep the whole circle: frame `N` would be a full turn. -/
theorem frameAz_last {N : ℕ} (hN : 0 < N) : frameAz N N = 2 * π := by
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [frameAz, mul_div_assoc, div_self hne, mul_one]

/-- The azimuths increase strictly along the animation. -/
theorem frameAz_strictMono {N : ℕ} (hN : 0 < N) : StrictMono (frameAz N) := by
  intro j k hjk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h : (j : ℝ) < k := by exact_mod_cast hjk
  have := Real.pi_pos
  rw [frameAz, frameAz, div_lt_div_iff_of_pos_right hNpos]
  nlinarith

/-- Distinct frames of one loop really do show distinct azimuths. -/
theorem frameAz_injOn {N : ℕ} (hN : 0 < N) {j k : ℕ} (h : frameAz N j = frameAz N k) : j = k :=
  (frameAz_strictMono hN).injective h

/-- **The loop closes.**  After the last frame the scene is exactly back at the first. -/
theorem rotZ_frameAz_last {N : ℕ} (hN : 0 < N) (p : ℝ × ℝ × ℝ) : rotZ (frameAz N N) p = p := by
  rw [frameAz_last hN, rotZ_two_pi]

/-- The composite of the `N` inter-frame steps is one full turn. -/
theorem rotZ_step_iterate (N k : ℕ) (p : ℝ × ℝ × ℝ) :
    rotZ (frameAz N 1) (rotZ (frameAz N k) p) = rotZ (frameAz N (k + 1)) p := by
  rw [rotZ_add]
  congr 1
  rw [frameAz, frameAz, frameAz]
  push_cast
  ring

/-! ## Zooming -/

/-- Uniform zoom of the scene by the factor `c`. -/
def scale3 (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (c * p.1, c * p.2.1, c * p.2.2)

@[simp] theorem scale3_one (p : ℝ × ℝ × ℝ) : scale3 1 p = p := by simp [scale3]

/-- **Zooming is a similarity**: all distances are multiplied by `|c|`, so the enlarged
panel is a faithful picture of the same object. -/
theorem dist3_scale3 (c : ℝ) (p q : ℝ × ℝ × ℝ) :
    dist3 (scale3 c p) (scale3 c q) = |c| * dist3 p q := by
  have h : ∀ x y z : ℝ, (c * x - c * y) ^ 2 = c ^ 2 * (x - y) ^ 2 := by
    intro x y _; ring
  simp only [dist3, nrm3, scale3]
  rw [show (c * p.1 - c * q.1) ^ 2 + (c * p.2.1 - c * q.2.1) ^ 2 + (c * p.2.2 - c * q.2.2) ^ 2
      = c ^ 2 * ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Zooming commutes with orbiting, so the zoom factor may be chosen once for the whole
animation. -/
theorem scale3_rotZ (c a : ℝ) (p : ℝ × ℝ × ℝ) : scale3 c (rotZ a p) = rotZ a (scale3 c p) := by
  simp only [scale3, rotZ]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> (simp; ring)

/-! ## The camera, and the axis it turns about

The renderer projects a point of `ℝ³` to the screen by looking from the azimuth `az` and the
elevation `el`, at the perspective distance `dist`; `camProjR` is that projection at unit scale
and with the origin of the screen at `(0,0)` (the `Float` version is `MonsterSpiral3DSvg.camProj`).

The three results below are what makes panel D turn about the axis it draws:

* the whole height axis projects to the single abscissa `0` (`camProjR_axis_fst`), so pinning one
  of its points to a place on the screen pins the entire axis to one vertical line there;
* that projection does not depend on the azimuth at all (`camProjR_axis_congr`), so the pinned
  axis is the *same* segment in every frame of the loop;
* turning the camera by `a` is exactly turning the object by `-a` about that axis
  (`camProjR_rotZ`), so the animation really is a rotation about the displayed axis. -/

/-- The camera projection at unit scale: azimuth `az`, elevation `el`, perspective distance
`dist`. -/
noncomputable def camProjR (az el dist : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  let rx := -Real.sin az * p.1 + Real.cos az * p.2.1
  let uy := -(Real.sin el * Real.cos az) * p.1 - (Real.sin el * Real.sin az) * p.2.1 +
    Real.cos el * p.2.2
  let dp := (Real.cos el * Real.cos az) * p.1 + (Real.cos el * Real.sin az) * p.2.1 +
    Real.sin el * p.2.2
  (dist / (dist - dp) * rx, -(dist / (dist - dp) * uy))

/-- **Every point of the height axis projects to the abscissa `0`**: on the screen the axis is a
vertical line, whatever the camera. -/
@[simp] theorem camProjR_axis_fst (az el dist z : ℝ) :
    (camProjR az el dist (0, 0, z)).1 = 0 := by
  simp [camProjR]

/-- **The picture of the axis does not depend on the azimuth**: as the camera walks around the
loop, every point of the axis stays exactly where it was on the screen. -/
theorem camProjR_axis_congr (az az' el dist z : ℝ) :
    camProjR az el dist (0, 0, z) = camProjR az' el dist (0, 0, z) := by
  simp [camProjR]

/-- **Orbiting the camera is turning the object about the axis**: the frame taken from the
azimuth `az` of the scene turned by `a` is the frame taken from the azimuth `az - a` of the scene
itself. -/
theorem camProjR_rotZ (az el dist a : ℝ) (p : ℝ × ℝ × ℝ) :
    camProjR az el dist (rotZ a p) = camProjR (az - a) el dist p := by
  simp only [camProjR, rotZ, Real.cos_sub, Real.sin_sub]
  refine Prod.ext ?_ ?_ <;> ring_nf

end SpiralOrbit
