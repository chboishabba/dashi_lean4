/-
# The increment formulation (§15)

Constants are the nuisance in every Liouville-type argument, so the route
proposes quotienting them out from the start by passing to the increments

  `δ_h U (x,t) = U(x+h,t) − U(x,t)`,

for which constancy of `U` is literally `δ_h U ≡ 0` for all `h`.  This file
supplies the corresponding exact PDE, derived (not postulated) from the
Navier–Stokes system of this development:

* `ClayNS.shift` and its calculus (`ClayNS.dvec_shift`, `ClayNS.adv_shift`, …) —
  the spatially translated field, and the fact that every differential operator
  of the system commutes with the translation;
* `ClayNS.shift_momentum`, `ClayNS.shift_incompressible` — a spatial translate of
  a solution is a solution (with the translated pressure);
* `ClayNS.increment_transport` — **the increment equation**
  `∂_t δ_h u_a + (u(·+h)·∇) δ_h u_a = −(δ_h u·∇) u_a − ∂_a δ_h p + ν Δ δ_h u_a`,
  i.e. exactly the system displayed in §15: the increment is transported by the
  shifted velocity and stretched against the *unshifted* velocity gradient.
  The obstruction term is precisely `δ_h u · ∇u`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.Uniqueness

open scoped BigOperators

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spatial translate of a spacetime field by `h`. -/
def shift (h : E3) (V : STime → F) : STime → F := fun z => V (z + (0, h))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp] lemma shift_apply (h : E3) (V : STime → F) (z : STime) :
    shift h V z = V (z.1, z.2 + h) := by
  have hz : z + ((0 : ℝ), h) = (z.1, z.2 + h) := by
    simp [Prod.ext_iff]
  rw [shift, hz]

/-- Every directional derivative commutes with the spatial translation. -/
lemma dvec_shift (h : E3) (V : STime → F) (a z : STime) :
    dvec a (shift h V) z = dvec a V (z + (0, h)) := by
  rw [dvec, dvec, show (shift h V) = (fun w : STime => V (w + (0, h))) from rfl,
    fderiv_comp_add_right]

lemma dtime_shift (h : E3) (V : STime → F) (z : STime) :
    dtime (shift h V) z = dtime V (z + (0, h)) :=
  dvec_shift h V (1, 0) z

lemma dspace_shift (h : E3) (V : STime → F) (i : Fin 3) (z : STime) :
    dspace (shift h V) i z = dspace V i (z + (0, h)) :=
  dvec_shift h V (0, ee i) z

lemma dspace_shift_fun (h : E3) (V : STime → F) (i : Fin 3) :
    dspace (shift h V) i = shift h (fun w => dspace V i w) := by
  funext z
  rw [dspace_shift h V i z]
  rfl

lemma lap_shift (h : E3) (V : STime → F) (z : STime) :
    lap (shift h V) z = lap V (z + (0, h)) := by
  simp only [lap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun w => dspace (shift h V) i w) = shift h (fun w => dspace V i w) from
    dspace_shift_fun h V i, dspace_shift]

lemma grad_shift (h : E3) (P : STime → ℝ) (z : STime) :
    grad (shift h P) z = grad P (z + (0, h)) := by
  simp only [grad]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dspace_shift]

lemma adv_shift (h : E3) (V : STime → E3) (z : STime) :
    adv (shift h V) z = adv V (z + (0, h)) := by
  simp only [adv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dspace_shift]
  rfl

lemma divg_shift (h : E3) (V : STime → E3) (z : STime) :
    divg (shift h V) z = divg V (z + (0, h)) := by
  simp only [divg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dspace_shift]

lemma contDiff_shift (h : E3) {V : STime → F} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (shift h V) :=
  hV.comp (contDiff_id.add contDiff_const)

/-- A spatial translate of a solution solves the same momentum equation. -/
lemma shift_momentum {nu : ℝ} {V : STime → E3} {P : STime → ℝ} (h : E3)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z) :
    ∀ z : STime, dtime (shift h V) z + adv (shift h V) z
      = - grad (shift h P) z + nu • lap (shift h V) z := by
  intro z
  rw [dtime_shift, adv_shift, grad_shift, lap_shift]
  exact hmom (z + (0, h))

/-- A spatial translate of a divergence-free field is divergence free. -/
lemma shift_incompressible {V : STime → E3} (h : E3) (hdiv : ∀ z : STime, divg V z = 0) :
    ∀ z : STime, divg (shift h V) z = 0 := by
  intro z
  rw [divg_shift]
  exact hdiv (z + (0, h))

/-- **The increment equation (§15).**  For a smooth solution `(u,p)` of the
zero-force Navier–Stokes system and any `h`, the increment
`δ_h u = u(·+h) − u` satisfies

`∂_t δ_h u_a + (u(·+h)·∇) δ_h u_a = −(δ_h u·∇) u_a − ∂_a δ_h p + ν Δ δ_h u_a`.

Constants have been quotiented out of the unknown: `δ_h u ≡ 0` for all `h` is
exactly spatial constancy of `u`.  The obstruction is the stretching term
`(δ_h u·∇) u`. -/
theorem increment_transport (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (a : Fin 3) (z : STime) :
    dvec (1, 0) (fun w => shift h V w a - V w a) z
        + ∑ j, shift h V z j * dvec (0, ee j) (fun w => shift h V w a - V w a) z
      = (-(∑ j, (shift h V z j - V z j) * dvec (0, ee j) (fun w => V w a) z)
          - dvec (0, ee a) (fun w => shift h P w - P w) z)
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => shift h V w a - V w a)) z :=
  difference_transport nu (shift h V) V (shift h P) P (contDiff_shift h hV) hV
    (contDiff_shift h hP) hP a z (shift_momentum h hmom z) (hmom z)

/-- Spatial constancy at each time is exactly the vanishing of all increments. -/
theorem spatially_constant_iff_shift_eq (V : STime → E3) :
    (∀ (h : E3) (z : STime), shift h V z - V z = 0)
      ↔ ∀ (t : ℝ) (x y : E3), V (t, x) = V (t, y) := by
  constructor
  · intro hzero t x y
    have := hzero (x - y) (t, y)
    simp only [shift_apply, sub_eq_zero] at this
    rw [← this]
    congr 1
    abel_nf
  · intro hconst h z
    have : V (z.1, z.2 + h) = V (z.1, z.2) := hconst z.1 (z.2 + h) z.2
    simp [shift_apply, this]

end ClayNS
