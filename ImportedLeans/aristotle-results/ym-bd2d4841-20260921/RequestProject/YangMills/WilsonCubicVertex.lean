/-
# Row A1a — the literal Wilson cubic (three-gluon) vertex, and why the
# single-corner witness is degenerate

The reduced Row A1a route asks for one component of the *first background
variation* `V = D_background Δ` of the constrained fluctuation operator, at one
explicit lattice momentum, to be bounded away from zero uniformly in the scale.
`TransverseBubbleEntry` reduces the Gaussian floor to exactly that datum at the
corner momentum `q = (0,1/2,0,0)`.

`V` is a *cubic gauge-field vertex*: two fluctuation legs and one background
leg.  Its literal Wilson lattice form carries three Lorentz indices,

    Γ_{αβγ}(p,q,r)
      = δ_{αβ} sin((p_γ − q_γ)/2) cos(r_α/2)
      + δ_{βγ} sin((q_α − r_α)/2) cos(p_β/2)
      + δ_{γα} sin((r_β − p_β)/2) cos(q_γ/2),

in the project's normalisation (`LatticeMomentum`: the physical momentum of a
normalised point `x` is `2π x`, so a half-momentum `p_μ/2` is `π x_μ`).

This file proves two facts about that literal tensor, both negative for the
corner witness and both constructive for what replaces it.

* `wilsonCubic_allEqual` : the all-equal Lorentz component vanishes *identically*
  in all three momenta.  So a collapsed scalar written `V_{00}` cannot be the
  all-equal component; a third (background) Lorentz index is essential.
* `wilsonCubic_bgZero_diag_corner_eq_zero` : at background momentum `0`, loop
  momenta `(q,−q)` and any corner momentum (every normalised component in
  `{0,1/2}`, i.e. every physical component in `{0,π}`), **every** component with
  the two fluctuation indices equal vanishes — for every choice of the
  background index.  In particular the project's corner momentum
  `q = (0,1/2,0,0)` annihilates the diagonal entries of the first background
  variation, so it is precisely the wrong momentum at which to seek a nonzero
  witness.
* `wilsonCubic_bgZero_diag_quarter_eq_one` : at the *quarter* momentum
  (one normalised component `1/4`, i.e. physical `π/2`) the same component
  equals `1`.  This is a strictly positive statement and is what makes the
  positive-volume patch route of `PositivePatchEnclosure` viable.

Nothing here asserts that the Wilson cubic vertex *is* Bałaban's constrained
first variation; the constrained variation also has averaging and projection
pieces (see `FirstVariationDecomposition`).  What is proved is that this
standard cubic tensor — the `W` piece — vanishes on the corner witness, which is
already enough to disqualify the corner as a literal witness.
-/
import RequestProject.YangMills.LatticeMomentum

namespace YangMills

open Real

/-- The literal Wilson three-gluon vertex tensor in the project's normalisation.
`x y z` are the three normalised momenta (physical momentum `2π ·`), and
`al be ga` the three Lorentz indices. -/
noncomputable def wilsonCubic (x y z : Fin 4 → ℝ) (al be ga : Fin 4) : ℝ :=
    (if al = be then 1 else 0) * Real.sin (π * (x ga - y ga)) * Real.cos (π * z al)
  + (if be = ga then 1 else 0) * Real.sin (π * (y al - z al)) * Real.cos (π * x be)
  + (if ga = al then 1 else 0) * Real.sin (π * (z be - x be)) * Real.cos (π * y ga)

/-- **The all-equal Lorentz component of the Wilson cubic vertex vanishes
identically**, for all three momenta.  Hence a scalar called `V_{00}` cannot be
the all-equal component of the first background variation: the background
Lorentz index must stay visible. -/
theorem wilsonCubic_allEqual (x y z : Fin 4 → ℝ) (mu : Fin 4) :
    wilsonCubic x y z mu mu mu = 0 := by
  have h : ∀ a b c : ℝ,
      Real.sin (a - b) * Real.cos c + Real.sin (b - c) * Real.cos a
        + Real.sin (c - a) * Real.cos b = 0 := by
    intro a b c
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
  have hx : π * (x mu - y mu) = π * x mu - π * y mu := by ring
  have hy : π * (y mu - z mu) = π * y mu - π * z mu := by ring
  have hz : π * (z mu - x mu) = π * z mu - π * x mu := by ring
  simp only [wilsonCubic, if_true, hx, hy, hz]
  simpa using h (π * x mu) (π * y mu) (π * z mu)

/-- The vertex at background momentum `0` with the two fluctuation legs carrying
`(x, −x)`: this is the configuration that enters the one-loop bubble. -/
noncomputable def wilsonCubicBgZero (x : Fin 4 → ℝ) (al be ga : Fin 4) : ℝ :=
  wilsonCubic x (fun mu => -x mu) (fun _ => 0) al be ga

/-- Explicit evaluation of the diagonal (equal fluctuation indices) components
at background momentum zero. -/
theorem wilsonCubicBgZero_diag (x : Fin 4 → ℝ) (mu rho : Fin 4) :
    wilsonCubicBgZero x mu mu rho
      = Real.sin (π * (2 * x rho))
        + (if mu = rho then 1 else 0) *
            (- Real.sin (π * x mu) * Real.cos (π * x mu)
             - Real.sin (π * x mu) * Real.cos (π * x rho)) := by
  have h1 : π * (x rho - -x rho) = π * (2 * x rho) := by ring
  have h2 : π * (-x mu - 0) = -(π * x mu) := by ring
  have h3 : π * (0 - x mu) = -(π * x mu) := by ring
  have h4 : π * -x rho = -(π * x rho) := by ring
  have h5 : π * (0 : ℝ) = 0 := by ring
  by_cases h : mu = rho
  · subst h
    simp only [wilsonCubicBgZero, wilsonCubic, h1, h2, h3, h4, h5,
      Real.sin_neg, Real.cos_neg, Real.cos_zero, if_true]
    ring_nf
  · simp only [wilsonCubicBgZero, wilsonCubic, h1, h2, h3, h4, h5,
      Real.sin_neg, Real.cos_neg, Real.cos_zero, if_neg h, if_neg (Ne.symm h), if_true]
    ring_nf

/-- A normalised momentum is a *corner* momentum when every component is `0` or
`1/2`, i.e. every physical component is `0` or `π` — the Brillouin-zone
boundary.  The project's `cornerMomentum = (0,1/2,0,0)` is such a point. -/
def IsCornerMomentum (x : Fin 4 → ℝ) : Prop := ∀ mu, x mu = 0 ∨ x mu = 1 / 2

private lemma sin_two_pi_of_corner {t : ℝ} (h : t = 0 ∨ t = 1 / 2) :
    Real.sin (π * (2 * t)) = 0 := by
  rcases h with h | h <;> subst h
  · norm_num
  · have : π * (2 * (1 / 2 : ℝ)) = π := by ring
    rw [this, Real.sin_pi]

private lemma sin_cos_of_corner {t : ℝ} (h : t = 0 ∨ t = 1 / 2) :
    Real.sin (π * t) * Real.cos (π * t) = 0 := by
  rcases h with h | h <;> subst h
  · norm_num
  · have : π * (1 / 2 : ℝ) = π / 2 := by ring
    rw [this, Real.cos_pi_div_two, mul_zero]

/-- **The corner witness is degenerate.**  At background momentum `0`, loop
momenta `(q,−q)` and any Brillouin-boundary ("corner") momentum, every component
of the Wilson cubic vertex with equal fluctuation indices vanishes, for every
background Lorentz index.  So no nonzero `V_{μμ;ρ}` can be read off at such a
momentum. -/
theorem wilsonCubic_bgZero_diag_corner_eq_zero {x : Fin 4 → ℝ}
    (hx : IsCornerMomentum x) (mu rho : Fin 4) :
    wilsonCubicBgZero x mu mu rho = 0 := by
  rw [wilsonCubicBgZero_diag]
  rw [sin_two_pi_of_corner (hx rho)]
  by_cases h : mu = rho
  · subst h
    rw [if_pos rfl]
    linear_combination (-2 : ℝ) * sin_cos_of_corner (hx mu)
  · rw [if_neg h]
    ring

/-- The project's corner momentum `q = (0,1/2,0,0)` is a corner momentum. -/
theorem isCornerMomentum_cornerMomentum :
    IsCornerMomentum (fun mu : Fin 4 => if mu = 1 then (1 : ℝ) / 2 else 0) := by
  intro mu
  by_cases h : mu = 1 <;> simp [h]

/-- Consequently the diagonal first-variation entries vanish at the corner
momentum used by `TransverseBubbleEntry`, for every background index. -/
theorem wilsonCubic_bgZero_diag_projectCorner_eq_zero (mu rho : Fin 4) :
    wilsonCubicBgZero (fun mu : Fin 4 => if mu = 1 then (1 : ℝ) / 2 else 0) mu mu rho = 0 :=
  wilsonCubic_bgZero_diag_corner_eq_zero isCornerMomentum_cornerMomentum mu rho

/-- The *quarter* momentum: a single normalised component equal to `1/4`
(physical momentum `π/2`), away from the Brillouin boundary. -/
noncomputable def quarterMomentum (rho : Fin 4) : Fin 4 → ℝ :=
  fun mu => if mu = rho then 1 / 4 else 0

/-- **The quarter momentum is a nonzero witness.**  With the background index
`ρ` carrying the normalised momentum `1/4` and the two fluctuation indices equal
to any `μ ≠ ρ`, the Wilson cubic vertex equals `1`.  This is the positive
counterpart to `wilsonCubic_bgZero_diag_corner_eq_zero`, and is why the patch
route looks for a box around normalised momentum `1/4`. -/
theorem wilsonCubic_bgZero_diag_quarter_eq_one {mu rho : Fin 4} (h : mu ≠ rho) :
    wilsonCubicBgZero (quarterMomentum rho) mu mu rho = 1 := by
  rw [wilsonCubicBgZero_diag]
  have hr : quarterMomentum rho rho = 1 / 4 := by simp [quarterMomentum]
  rw [hr, if_neg h]
  have : π * (2 * (1 / 4 : ℝ)) = π / 2 := by ring
  rw [this, Real.sin_pi_div_two]
  ring

/-- The vertex is a *continuous* function of the momentum in the background
direction, so the nonzero value at `1/4` persists on a whole neighbourhood; this
is the analytic input the positive-volume patch needs (as opposed to a single
Fourier mode, cf. `SingleModeWeight`). -/
theorem wilsonCubic_bgZero_diag_continuous {mu rho : Fin 4} (h : mu ≠ rho) :
    Continuous fun t : ℝ =>
      wilsonCubicBgZero (fun nu => if nu = rho then t else 0) mu mu rho := by
  have : (fun t : ℝ =>
      wilsonCubicBgZero (fun nu => if nu = rho then t else 0) mu mu rho)
      = fun t : ℝ => Real.sin (π * (2 * t)) := by
    funext t
    rw [wilsonCubicBgZero_diag, if_neg h]
    simp
  rw [this]
  fun_prop

end YangMills
