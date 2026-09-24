import Mathlib
import Integration.Variation.SourceCoordinate

/-!
# Source-coordinate discipline in a Banach space

`Integration.Variation.SourceCoordinate` proves the source-coordinate second
derivative law for `ℝ → ℝ`:

```
(f ∘ A)'' = f''(A) (A')² + f'(A) A''
```

The frontier asks for this in the form the physics actually uses: the energy is
a function on a Banach space of fields, and the source coordinate is a curve
into that space.  This file proves exactly that:

```
D²(E ∘ A)[t] = D²E(A t)[A' t, A' t] + DE(A t)[A'' t]
```

for `E : X → ℝ` on a real normed space `X` and a curve `A : ℝ → X`, both `C²`.
The second term is the source-coordinate correction, and it vanishes precisely
because `A'' = 0` when the source coordinate is affine.

It then proves the third-order law in the same setting,

```
D³(E ∘ A) = D³E[A', A', A'] + D²E[A'', A'] + 2 D²E[A', A''] + DE[A''']
```

both in that raw form (no symmetry used) and, via symmetry of the second
derivative, in the familiar `+ 3 D²E[A', A'']` form.

The file closes with two further consequences:

* `second_fderiv_apply_real` — the quadratic term of the Banach formula reduces
  to `f''(x) v²` in one dimension, so the new statement is a genuine
  generalisation of the old one and not a differently-normalised object;
* `banach_third_term_is_load_bearing` — a curve for which the naive
  identification `D²(E ∘ A) = D²E[A', A']` fails.

Nothing here is about gravity: `X` is an arbitrary real normed space and `E` an
arbitrary `C²` function on it.
-/

namespace Integration.Variation.SourceCoordinateBanach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The source-coordinate second derivative law in a normed space.**  For a
`C²` function `f` on `X` and a `C²` curve `A : ℝ → X`,

```
(f ∘ A)''(t) = D²f(A t)[A'(t), A'(t)] + Df(A t)[A''(t)].
```

The two Hessians agree only when the curvature term `A''` vanishes. -/
theorem second_deriv_comp_curve (f : X → ℝ) (A : ℝ → X)
    (hf : ContDiff ℝ 2 f) (hA : ContDiff ℝ 2 A) (t : ℝ) :
    deriv (deriv (f ∘ A)) t
      = (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv A t)
        + (fderiv ℝ f (A t)) (deriv (deriv A) t) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_refl _)
  have hAd : ContDiff ℝ 1 (deriv A) := hA.deriv'
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst : ∀ s, HasDerivAt (f ∘ A) ((fderiv ℝ f (A s)) (deriv A s)) s := fun s =>
    (hf1 (A s)).hasFDerivAt.comp_hasDerivAt s (hA1 s).hasDerivAt
  have hfun : deriv (f ∘ A) = fun s => (fderiv ℝ f (A s)) (deriv A s) :=
    funext fun s => (hfirst s).deriv
  rw [hfun]
  have hF : HasDerivAt (fun s => fderiv ℝ f (A s))
      (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) t :=
    ((hfd.differentiable one_ne_zero) (A t)).hasFDerivAt.comp_hasDerivAt t (hA1 t).hasDerivAt
  have hv : HasDerivAt (deriv A) (deriv (deriv A) t) t :=
    ((hAd.differentiable one_ne_zero) t).hasDerivAt
  exact (hF.clm_apply hv).deriv

/-- An affine source coordinate is `C²`. -/
theorem contDiff_affine (a v : X) : ContDiff ℝ 2 (fun s : ℝ => a + s • v) :=
  contDiff_const.add ((contDiff_id (𝕜 := ℝ)).smul contDiff_const)

/-- The derivative of an affine source coordinate is constant. -/
theorem deriv_affine (a v : X) : deriv (fun s : ℝ => a + s • v) = fun _ => v := by
  funext s
  simpa using (((hasDerivAt_id s).smul_const v).const_add a).deriv

/-- **The affine case.**  Along an affine source coordinate the correction term
vanishes and the second derivative is exactly the Hessian evaluated twice on the
direction. -/
theorem second_deriv_comp_affine_curve (f : X → ℝ) (hf : ContDiff ℝ 2 f) (a v : X) (t : ℝ) :
    deriv (deriv (f ∘ fun s : ℝ => a + s • v)) t
      = (fderiv ℝ (fderiv ℝ f) (a + t • v) v) v := by
  have hA := contDiff_affine a v
  have hderiv := deriv_affine a v
  have h := second_deriv_comp_curve f (fun s : ℝ => a + s • v) hf hA t
  rw [hderiv] at h
  simpa using h

/-- **The Banach quadratic term is the classical second derivative.**  In one
dimension the first term of `second_deriv_comp_curve` is `f''(x) v²`, so the
normed-space law generalises `SourceCoordinate.second_deriv_comp` rather than
restating a differently normalised object. -/
theorem second_fderiv_apply_real (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x v : ℝ) :
    (fderiv ℝ (fderiv ℝ f) x v) v = deriv (deriv f) x * v ^ 2 := by
  have hA : ContDiff ℝ 2 (fun s : ℝ => x + s • v) := contDiff_affine x v
  have hderiv : deriv (fun s : ℝ => x + s • v) = fun _ => v := deriv_affine x v
  have hbanach := second_deriv_comp_affine_curve f hf x v 0
  have hclassical :=
    SourceCoordinate.second_deriv_comp f (fun s : ℝ => x + s • v) hf hA 0
  rw [hderiv] at hclassical
  simp only [smul_eq_mul, zero_mul, add_zero, deriv_const] at hbanach hclassical ⊢
  rw [← hbanach, hclassical]
  ring

/-- **The third-order source-coordinate law in a normed space.**  For `C³` data,

```
(f ∘ A)'''(t) = D³f(A t)[A', A', A'] + D²f(A t)[A'', A'] + 2 D²f(A t)[A', A'']
                 + Df(A t)[A'''].
```

The two middle terms are kept separate here: no symmetry of the second
derivative is used, so the statement is exactly what the chain rule gives. -/
theorem third_deriv_comp_curve (f : X → ℝ) (A : ℝ → X)
    (hf : ContDiff ℝ 3 f) (hA : ContDiff ℝ 3 A) (t : ℝ) :
    deriv (deriv (deriv (f ∘ A))) t
      = ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (A t) (deriv A t)) (deriv A t)) (deriv A t)
        + (fderiv ℝ (fderiv ℝ f) (A t) (deriv (deriv A) t)) (deriv A t)
        + 2 * (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv (deriv A) t)
        + (fderiv ℝ f (A t)) (deriv (deriv (deriv A)) t) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hA2 : ContDiff ℝ 2 A := hA.of_le (by norm_num)
  have hsecond : deriv (deriv (f ∘ A)) = fun s =>
      (fderiv ℝ (fderiv ℝ f) (A s) (deriv A s)) (deriv A s)
        + (fderiv ℝ f (A s)) (deriv (deriv A) s) :=
    funext fun s => second_deriv_comp_curve f A hf2 hA2 s
  rw [hsecond]
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hfd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (le_refl _)
  have hfdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hfd.fderiv_right (le_refl _)
  have hAd : ContDiff ℝ 2 (deriv A) := hA.deriv'
  have hAdd : ContDiff ℝ 1 (deriv (deriv A)) := hAd.deriv'
  have hF1 : HasDerivAt (fun s => fderiv ℝ f (A s))
      (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) t :=
    ((hfd.differentiable (by norm_num)) (A t)).hasFDerivAt.comp_hasDerivAt t (hA1 t).hasDerivAt
  have hF2 : HasDerivAt (fun s => fderiv ℝ (fderiv ℝ f) (A s))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (A t) (deriv A t)) t :=
    ((hfdd.differentiable (by norm_num)) (A t)).hasFDerivAt.comp_hasDerivAt t (hA1 t).hasDerivAt
  have hv : HasDerivAt (deriv A) (deriv (deriv A) t) t :=
    ((hAd.differentiable (by norm_num)) t).hasDerivAt
  have ha : HasDerivAt (deriv (deriv A)) (deriv (deriv (deriv A)) t) t :=
    ((hAdd.differentiable (by norm_num)) t).hasDerivAt
  have hP : HasDerivAt (fun s => fderiv ℝ (fderiv ℝ f) (A s) (deriv A s))
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (A t) (deriv A t)) (deriv A t)
        + fderiv ℝ (fderiv ℝ f) (A t) (deriv (deriv A) t)) t := hF2.clm_apply hv
  have hsum : HasDerivAt (fun s => (fderiv ℝ (fderiv ℝ f) (A s) (deriv A s)) (deriv A s)
        + (fderiv ℝ f (A s)) (deriv (deriv A) s))
      ((((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (A t) (deriv A t)) (deriv A t)
            + fderiv ℝ (fderiv ℝ f) (A t) (deriv (deriv A) t)) (deriv A t)
          + (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv (deriv A) t))
        + ((fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv (deriv A) t)
          + (fderiv ℝ f (A t)) (deriv (deriv (deriv A)) t))) t :=
    (hP.clm_apply hv).add (hF1.clm_apply ha)
  rw [hsum.deriv]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- **The symmetric form of the third-order law.**  Using symmetry of the second
derivative the two mixed terms merge, giving the familiar shape

```
(f ∘ A)''' = D³f[A', A', A'] + 3 D²f[A', A''] + Df[A'''].
``` -/
theorem third_deriv_comp_curve_symm (f : X → ℝ) (A : ℝ → X)
    (hf : ContDiff ℝ 3 f) (hA : ContDiff ℝ 3 A) (t : ℝ) :
    deriv (deriv (deriv (f ∘ A))) t
      = ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (A t) (deriv A t)) (deriv A t)) (deriv A t)
        + 3 * (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv (deriv A) t)
        + (fderiv ℝ f (A t)) (deriv (deriv (deriv A)) t) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (le_refl _)
  have hsymm := second_derivative_symmetric (f := f) (f' := fderiv ℝ f)
    (f'' := fderiv ℝ (fderiv ℝ f) (A t)) (x := A t)
    (fun y => (hf1 y).hasFDerivAt)
    ((hfd.differentiable (by norm_num)) (A t)).hasFDerivAt
    (deriv (deriv A) t) (deriv A t)
  rw [third_deriv_comp_curve f A hf hA t, hsymm]
  ring

/-- **The correction term is load-bearing in the normed-space statement too.**
There is a `C²` function and a `C²` curve for which the second derivative of the
composite differs from the Hessian term alone. -/
theorem banach_third_term_is_load_bearing :
    ∃ (f : ℝ → ℝ) (A : ℝ → ℝ) (t : ℝ), ContDiff ℝ 2 f ∧ ContDiff ℝ 2 A ∧
      deriv (deriv (f ∘ A)) t ≠ (fderiv ℝ (fderiv ℝ f) (A t) (deriv A t)) (deriv A t) := by
  refine ⟨id, fun s => s ^ 2, 1, contDiff_id, by fun_prop, ?_⟩
  have hf : ContDiff ℝ 2 (id : ℝ → ℝ) := contDiff_id
  have hA : ContDiff ℝ 2 (fun s : ℝ => s ^ 2) := by fun_prop
  have hcomp : (id ∘ fun s : ℝ => s ^ 2) = fun s : ℝ => s ^ 2 := rfl
  have hderivA : deriv (fun s : ℝ => s ^ 2) = fun s : ℝ => 2 * s := by
    funext s
    simp [(hasDerivAt_pow 2 s).deriv]
  have hquad : (fderiv ℝ (fderiv ℝ (id : ℝ → ℝ)) ((fun s : ℝ => s ^ 2) 1)
      (deriv (fun s : ℝ => s ^ 2) 1)) (deriv (fun s : ℝ => s ^ 2) 1) = 0 := by
    rw [second_fderiv_apply_real id hf]
    simp [deriv_id'']
  have htwo : deriv (fun s : ℝ => 2 * s) 1 = 2 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_mul (2 : ℝ)).deriv
  rw [hquad, hcomp, hderivA, htwo]
  norm_num

end Integration.Variation.SourceCoordinateBanach
