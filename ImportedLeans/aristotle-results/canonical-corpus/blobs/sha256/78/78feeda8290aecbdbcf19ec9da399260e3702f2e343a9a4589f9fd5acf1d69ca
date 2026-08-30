import Mathlib

/-!
# QFT/GR frontier, lane 4 — source-coordinate discipline for second variations

The merged Yang–Mills work recorded a correction that this lane states and
proves in its own right, with no gauge-theoretic content and no reference to any
Yang–Mills or Navier–Stokes material:

```
D_B²(E ∘ A) = D_A²E[A', A'] + D_A E[A'']
```

so a second variation taken in a *substituted* coordinate `B` cannot be
identified with the bare second variation in the original coordinate `A` unless
the substitution is affine (`A'' = 0`).

It is proved here twice: first in the one-dimensional case, which is exactly the
case in which the identification is usually made silently (`A : ℝ → ℝ` the source
substitution, `f : ℝ → ℝ` the energy); and then in full generality on Banach
spaces, where the correction term is the honest bilinear `D²A[v, w]`.

## What is proved

* `second_deriv_comp` — the chain rule above, for `C²` data;
* `second_deriv_comp_affine` — for an affine substitution the correction term
  vanishes and the naive identification is *correct*, with the expected factor
  `(A')²`;
* `naive_hessian_identification_fails` — an explicit witness (`f = id`,
  `A = (·)²`) in which the two differ, so the affineness hypothesis is
  load-bearing;
* `affine_iff_no_correction_at` — locally, the correction term vanishes exactly
  when the substitution has vanishing second derivative there, for any energy
  with non-vanishing first derivative.

And on Banach spaces, with no dimension restriction:

* `second_fderiv_comp` — the Fréchet form
  `D²(f ∘ A)[v, w] = D²f[DA v, DA w] + Df[D²A[v, w]]`;
* `second_fderiv_comp_of_const_fderiv` — the affine case, in which the second
  term drops and the substituted Hessian is the bare Hessian pulled back along
  the (constant) differential;
* `correction_is_detected_by_a_linear_energy` — the sharp negative: whenever
  `D²A[v, w] ≠ 0` there is a *linear* energy — one with no curvature of its own
  whatsoever — whose substituted Hessian is nonzero.  So the correction term can
  never be dismissed as an artefact of the energy; a nonaffine substitution is
  always visible in some second variation.
-/

namespace Integration.Variation.SourceCoordinate

/-- **The second-order chain rule.**  The Hessian in the substituted coordinate
is the pulled-back Hessian *plus* the first derivative against the second
derivative of the substitution. -/
theorem second_deriv_comp (f A : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hA : ContDiff ℝ 2 A)
    (t : ℝ) :
    deriv (deriv (f ∘ A)) t
      = deriv (deriv f) (A t) * (deriv A t) ^ 2 + deriv f (A t) * deriv (deriv A) t := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hdfC : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' hf
  have hdAC : ContDiff ℝ 1 (deriv A) := ContDiff.deriv' hA
  have hdf1 : Differentiable ℝ (deriv f) := hdfC.differentiable (by norm_num)
  have hdA1 : Differentiable ℝ (deriv A) := hdAC.differentiable (by norm_num)
  have h1 : deriv (f ∘ A) = fun x => deriv f (A x) * deriv A x := by
    funext x
    exact deriv_comp x (hf1 (A x)) (hA1 x)
  have hcomp : DifferentiableAt ℝ (fun x => deriv f (A x)) t := (hdf1 (A t)).comp t (hA1 t)
  rw [h1, deriv_fun_mul hcomp (hdA1 t)]
  have h2 : deriv (fun x => deriv f (A x)) t = deriv (deriv f) (A t) * deriv A t :=
    deriv_comp t (hdf1 (A t)) (hA1 t)
  rw [h2]
  ring

/-- For an affine source substitution the correction term vanishes, and the
substituted Hessian is the bare Hessian rescaled by `(A')²`. -/
theorem second_deriv_comp_affine (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (a b t : ℝ) :
    deriv (deriv (f ∘ fun x : ℝ => a * x + b)) t
      = deriv (deriv f) (a * t + b) * a ^ 2 := by
  have hA : ContDiff ℝ 2 (fun x : ℝ => a * x + b) := by fun_prop
  have hd : deriv (fun x : ℝ => a * x + b) = fun _ : ℝ => a := by
    funext x
    rw [deriv_add_const, deriv_const_mul_field]
    simp
  rw [second_deriv_comp f _ hf hA t, hd]
  simp

/-- **The naive identification fails.**  With `f = id` and the quadratic
substitution `A x = x²`, the bare Hessian term is zero while the substituted
Hessian is `2`. -/
theorem naive_hessian_identification_fails :
    deriv (deriv ((id : ℝ → ℝ) ∘ fun x : ℝ => x ^ 2)) 1
      ≠ deriv (deriv (id : ℝ → ℝ)) ((1 : ℝ) ^ 2) * (deriv (fun x : ℝ => x ^ 2) 1) ^ 2 := by
  have hcomp : ((id : ℝ → ℝ) ∘ fun x : ℝ => x ^ 2) = fun x : ℝ => x ^ 2 := rfl
  have h1 : deriv (fun x : ℝ => x ^ 2) = fun x : ℝ => 2 * x := by
    funext x
    show deriv (fun x : ℝ => x ^ 2) x = 2 * x
    simp
  have h2 : deriv (deriv (fun x : ℝ => x ^ 2)) 1 = 2 := by
    rw [h1, deriv_const_mul_field]
    simp
  have h3 : deriv (deriv (id : ℝ → ℝ)) ((1 : ℝ) ^ 2) = 0 := by
    have : deriv (id : ℝ → ℝ) = fun _ : ℝ => 1 := by
      funext x
      simp
    rw [this, deriv_const]
  rw [hcomp, h2, h3]
  norm_num

/-- Locally, and for an energy whose first derivative does not vanish at the
substituted point, the correction term is absent exactly when the substitution
has vanishing second derivative there. -/
theorem affine_iff_no_correction_at (f A : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hA : ContDiff ℝ 2 A) (t : ℝ) (hne : deriv f (A t) ≠ 0) :
    deriv (deriv (f ∘ A)) t = deriv (deriv f) (A t) * (deriv A t) ^ 2
      ↔ deriv (deriv A) t = 0 := by
  rw [second_deriv_comp f A hf hA t]
  constructor
  · intro h
    have : deriv f (A t) * deriv (deriv A) t = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hne
    · exact h'
  · intro h
    rw [h]
    ring

/-! ### The Banach-space form -/

section Frechet

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The second-order chain rule on Banach spaces.**
`D²(f ∘ A)[v, w] = D²f[DA v, DA w] + Df[D²A[v, w]]`.  The second term is the
correction that a substituted-coordinate Hessian carries and a bare Hessian does
not. -/
theorem second_fderiv_comp (f : F → G) (A : E → F) (hf : ContDiff ℝ 2 f)
    (hA : ContDiff ℝ 2 A) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ A) y) x v w
      = fderiv ℝ (fderiv ℝ f) (A x) (fderiv ℝ A x v) (fderiv ℝ A x w)
        + fderiv ℝ f (A x) (fderiv ℝ (fderiv ℝ A) x v w) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hdf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdA1 : Differentiable ℝ (fderiv ℝ A) :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hrw : (fun y => fderiv ℝ (f ∘ A) y)
      = fun y => (fderiv ℝ f (A y)).comp (fderiv ℝ A y) :=
    funext fun y => fderiv_comp y (hf1 (A y)) (hA1 y)
  have hc : HasFDerivAt (fun y => fderiv ℝ f (A y))
      ((fderiv ℝ (fderiv ℝ f) (A x)).comp (fderiv ℝ A x)) x :=
    HasFDerivAt.comp x (hdf1 (A x)).hasFDerivAt (hA1 x).hasFDerivAt
  have hd : HasFDerivAt (fun y => fderiv ℝ A y) (fderiv ℝ (fderiv ℝ A) x) x :=
    (hdA1 x).hasFDerivAt
  rw [hrw, (hc.clm_comp hd).fderiv]
  simp [ContinuousLinearMap.compL, add_comm]

/-- For a substitution with constant differential — the affine case — the
correction term drops and the substituted Hessian is the bare Hessian pulled
back along that differential. -/
theorem second_fderiv_comp_of_const_fderiv (f : F → G) (A : E → F) (hf : ContDiff ℝ 2 f)
    (hA : ContDiff ℝ 2 A) (L : E →L[ℝ] F) (hL : ∀ y, fderiv ℝ A y = L) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ A) y) x v w
      = fderiv ℝ (fderiv ℝ f) (A x) (L v) (L w) := by
  have hconst : fderiv ℝ (fderiv ℝ A) x = 0 := by
    rw [funext hL, show (fderiv ℝ fun _ : E => L) = 0 from fderiv_fun_const _]
    rfl
  rw [second_fderiv_comp f A hf hA x v w, hconst, hL x]
  simp

/-- **The correction term is never invisible.**  If the substitution has a
nonzero second derivative in the directions `v, w`, then some *linear* energy —
one whose own Hessian vanishes identically — already has a nonzero substituted
Hessian there.  So `D²A` cannot be argued away as an artefact of a curved
energy. -/
theorem correction_is_detected_by_a_linear_energy (A : E → F) (hA : ContDiff ℝ 2 A)
    (x v w : E) (hne : fderiv ℝ (fderiv ℝ A) x v w ≠ 0) :
    ∃ f : F →L[ℝ] ℝ, fderiv ℝ (fun y => fderiv ℝ ((f : F → ℝ) ∘ A) y) x v w ≠ 0 := by
  obtain ⟨f, -, hfx⟩ :=
    exists_dual_vector ℝ (fderiv ℝ (fderiv ℝ A) x v w) (by simpa using hne)
  refine ⟨f, ?_⟩
  have hfd : fderiv ℝ (f : F → ℝ) = fun _ => (f : F →L[ℝ] ℝ) := funext fun _ => f.fderiv
  rw [second_fderiv_comp (f : F → ℝ) A f.contDiff hA x v w, hfd,
    show (fderiv ℝ fun _ : F => (f : F →L[ℝ] ℝ)) = 0 from fderiv_fun_const _]
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_add]
  rw [hfx]
  simpa using hne

end Frechet

end Integration.Variation.SourceCoordinate
