import Integration.Variation.SourceCoordinate

/-!
# QFT/GR frontier, lane 11 — the source-coordinate law beyond second order

Item 7 of the frontier report states the limitation of the source-coordinate
lane precisely: the substitution law `D²(E ∘ A) = D²E[A', A'] + DE[A'']` is
discharged at second order in both the one-dimensional and the Banach setting,
but *nothing is proved about third and higher variations*.

This lane closes the third-order case in the one-dimensional model:

```
(f ∘ A)''' = f'''(A) (A')³ + 3 f''(A) A' A'' + f'(A) A'''.
```

Two things are worth recording about the shape of this identity, because they
are exactly what a "just rescale the derivatives" reading of a source-coordinate
change would get wrong:

* the second-order correction does **not** simply persist — it acquires the
  combinatorial factor `3` and a new mixed term, so the third variation is not
  obtainable from the second-order law by iteration alone;
* the `A'''` term is genuinely there
  (`third_order_correction_is_load_bearing`): a substitution can be
  *stationary to second order* in the sense that the pulled-back terms vanish
  and still produce a nonzero third variation.

## What is proved

* `third_deriv_comp` — the third-order chain rule for a `C³` substitution;
* `third_deriv_comp_affine` — for an affine substitution all corrections vanish
  and the third variation is the bare one rescaled by `a³`;
* `third_order_correction_is_load_bearing` — the `A'''` term cannot be dropped.

## What is *not* proved

Only the one-dimensional case, and only order three: no Faà di Bruno formula for
general order, no Banach-space version (the second-order Banach law remains
`SourceCoordinate.second_fderiv_comp`), and `C³` regularity is assumed
throughout.
-/

namespace Integration.Variation.ThirdOrder

open Integration.Variation.SourceCoordinate

/-- **The third-order source-coordinate law.**
`(f ∘ A)''' = f'''(A) (A')³ + 3 f''(A) A' A'' + f'(A) A'''`. -/
theorem third_deriv_comp (f A : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hA : ContDiff ℝ 3 A) (t : ℝ) :
    deriv (deriv (deriv (f ∘ A))) t
      = deriv (deriv (deriv f)) (A t) * (deriv A t) ^ 3
        + 3 * (deriv (deriv f) (A t) * (deriv A t * deriv (deriv A) t))
        + deriv f (A t) * deriv (deriv (deriv A)) t := by
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hdf : ContDiff ℝ 2 (deriv f) := ContDiff.deriv' hf
  have hdA : ContDiff ℝ 2 (deriv A) := ContDiff.deriv' hA
  have hddf : ContDiff ℝ 1 (deriv (deriv f)) := ContDiff.deriv' hdf
  have hddA : ContDiff ℝ 1 (deriv (deriv A)) := ContDiff.deriv' hdA
  have hdf1 : Differentiable ℝ (deriv f) := hdf.differentiable (by norm_num)
  have hdA1 : Differentiable ℝ (deriv A) := hdA.differentiable (by norm_num)
  have hddf1 : Differentiable ℝ (deriv (deriv f)) := hddf.differentiable (by norm_num)
  have hddA1 : Differentiable ℝ (deriv (deriv A)) := hddA.differentiable (by norm_num)
  have h2 : deriv (deriv (f ∘ A))
      = fun x => deriv (deriv f) (A x) * (deriv A x) ^ 2 + deriv f (A x) * deriv (deriv A) x := by
    funext x
    exact second_deriv_comp f A (hf.of_le (by norm_num)) (hA.of_le (by norm_num)) x
  rw [h2]
  have hc1 : DifferentiableAt ℝ (fun x => deriv (deriv f) (A x)) t :=
    (hddf1 (A t)).comp t (hA1 t)
  have hc2 : DifferentiableAt ℝ (fun x => (deriv A x) ^ 2) t := (hdA1 t).fun_pow 2
  have hc3 : DifferentiableAt ℝ (fun x => deriv f (A x)) t := (hdf1 (A t)).comp t (hA1 t)
  rw [deriv_fun_add (hc1.fun_mul hc2) (hc3.fun_mul (hddA1 t)), deriv_fun_mul hc1 hc2,
    deriv_fun_mul hc3 (hddA1 t)]
  have e1 : deriv (fun x => deriv (deriv f) (A x)) t
      = deriv (deriv (deriv f)) (A t) * deriv A t := deriv_comp t (hddf1 (A t)) (hA1 t)
  have e2 : deriv (fun x => (deriv A x) ^ 2) t = 2 * deriv A t * deriv (deriv A) t := by
    rw [deriv_fun_pow (hdA1 t)]
    norm_num
  have e3 : deriv (fun x => deriv f (A x)) t = deriv (deriv f) (A t) * deriv A t :=
    deriv_comp t (hdf1 (A t)) (hA1 t)
  rw [e1, e2, e3]
  ring

/-- For an affine source substitution both third-order corrections vanish. -/
theorem third_deriv_comp_affine (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (a b t : ℝ) :
    deriv (deriv (deriv (f ∘ fun x : ℝ => a * x + b))) t
      = deriv (deriv (deriv f)) (a * t + b) * a ^ 3 := by
  have hA : ContDiff ℝ 3 (fun x : ℝ => a * x + b) := by fun_prop
  have hd1 : deriv (fun x : ℝ => a * x + b) = fun _ => a := by
    funext x
    have h : HasDerivAt (fun x : ℝ => a * x + b) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const b
    exact h.deriv
  rw [third_deriv_comp f _ hf hA t, hd1]
  simp

/-- **The `A'''` correction is load-bearing.**  With `f` the identity and the
substitution `A x = x³`, every pulled-back term vanishes at the origin and the
third variation is nevertheless `6`.  So a source-coordinate change can be
invisible to the first and second variations and still move the third. -/
theorem third_order_correction_is_load_bearing :
    ∃ f A : ℝ → ℝ, ContDiff ℝ 3 f ∧ ContDiff ℝ 3 A ∧
      deriv (deriv (deriv f)) (A 0) * (deriv A 0) ^ 3
          + 3 * (deriv (deriv f) (A 0) * (deriv A 0 * deriv (deriv A) 0)) = 0 ∧
      deriv (deriv (deriv ((fun x : ℝ => x) ∘ fun x : ℝ => x ^ 3))) 0 = 6 := by
  refine ⟨fun x : ℝ => x, fun x : ℝ => x ^ 3, by fun_prop, by fun_prop, ?_, ?_⟩
  · have hid1 : deriv (fun x : ℝ => x) = fun _ : ℝ => (1 : ℝ) := by
      funext x; simp
    have hid2 : deriv (deriv fun x : ℝ => x) = fun _ : ℝ => (0 : ℝ) := by
      rw [hid1]; funext x; simp
    rw [hid2]
    simp
  · have h1 : deriv (fun x : ℝ => x ^ 3) = fun x : ℝ => 3 * x ^ 2 := by
      funext x
      simp [deriv_fun_pow]
    have h2 : deriv (deriv fun x : ℝ => x ^ 3) = fun x : ℝ => 6 * x := by
      rw [h1]
      funext x
      rw [deriv_const_mul _ (by fun_prop), deriv_fun_pow (by fun_prop)]
      simp
      ring
    have h3 : deriv (deriv (deriv fun x : ℝ => x ^ 3)) = fun _ : ℝ => (6 : ℝ) := by
      rw [h2]
      funext x
      rw [deriv_const_mul _ (by fun_prop)]
      simp
    have hcomp : ((fun x : ℝ => x) ∘ fun x : ℝ => x ^ 3) = fun x : ℝ => x ^ 3 := rfl
    rw [hcomp, h3]

end Integration.Variation.ThirdOrder
