import Mathlib

/-!
# QFT/GR frontier, lane 5 — the metric-density first variation

Item A of the frontier collapse — `δ_g S_common[h] = ⟨G, h⟩` for an actual
action — is analytic and is *not* proved anywhere in this repository.  What is
proved here is its first genuinely computational ingredient, in the only setting
where it is pure algebra and analysis rather than differential geometry: the
first variation of the metric *determinant* and of the volume density
`√(-det g)`, at a point, for a metric represented by an invertible real matrix.

```
   d/dt det(g + t h) |_{t=0}      = det g · tr(g⁻¹ h)          (Jacobi)
   d/dt √(-det(g + t h)) |_{t=0}  = ½ √(-det g) · tr(g⁻¹ h)
```

The second line is the familiar `δ√(-g) = ½ √(-g) g^{μν} δg_{μν}`, here as a
checked theorem about matrices rather than as a formula quoted from a text.

## What is proved

* `hasDerivAt_det_one_add_smul` — Jacobi's formula at the identity;
* `hasDerivAt_det_add_smul` — Jacobi's formula at any invertible `g`;
* `hasDerivAt_sqrt_neg_det` — the density variation, in the Lorentzian
  normalisation `det g < 0`;
* `density_variation_is_a_trace_pairing` — the density variation is a *pairing*
  in the sense of lane 1: it is `h ↦ tr(Tᵀ h)` for one explicit `T`, so it is
  exactly the kind of object the stress weld manipulates;
* `density_variation_is_linear` — and it is linear in the perturbation.

And one negative, which is the reason this lane cannot be mistaken for item A:

* `density_variation_does_not_determine_the_perturbation` — as soon as the index
  set has two elements, the density variation annihilates a nonzero
  perturbation.  Knowing `δ√(-g)` therefore determines nothing about the
  traceless part of `h`; a variational identity built only from the volume
  density can never separate stress tensors, exactly as
  `Pairing.exists_ne_agreeing_of_ne_top` predicts.

## What is *not* proved

Nothing here mentions curvature.  The Ricci and scalar curvature terms of the
Einstein–Hilbert variation, and the divergence terms that are discarded under an
integral, are entirely absent; `g` is a single matrix, not a metric field on a
manifold, and there is no integration.  This lane discharges the density factor
of item A and nothing else.
-/

namespace Integration.Variation.MetricDensity

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Jacobi's formula at the identity.**  `d/dt det(1 + t M)|_{t=0} = tr M`. -/
theorem hasDerivAt_det_one_add_smul (M : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  set q : Polynomial ℝ :=
    ((1 : Matrix n n (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) • M.map ⇑Polynomial.C).det.divX.divX with hq
  have hfun : (fun t : ℝ => (1 + t • M).det)
      = fun t : ℝ => 1 + M.trace * t + Polynomial.eval t q * t ^ 2 :=
    funext fun t => Matrix.det_one_add_smul t M
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => Polynomial.eval t q) (Polynomial.eval 0 q.derivative) 0 :=
    q.hasDerivAt 0
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (0 : ℝ) ^ 1) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => 1 + M.trace * t) M.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul M.trace).const_add 1
  simpa using h3.add (h1.mul h2)

/-- **Jacobi's formula.**  `d/dt det(g + t h)|_{t=0} = det g · tr(g⁻¹ h)` at any
invertible `g`. -/
theorem hasDerivAt_det_add_smul (g h : Matrix n n ℝ) (hg : IsUnit g.det) :
    HasDerivAt (fun t : ℝ => (g + t • h).det) (g.det * (g⁻¹ * h).trace) 0 := by
  have hfac : ∀ t : ℝ, g + t • h = g * (1 + t • (g⁻¹ * h)) := by
    intro t
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv g hg, Matrix.one_mul]
  have hfun : (fun t : ℝ => (g + t • h).det)
      = fun t : ℝ => g.det * (1 + t • (g⁻¹ * h)).det :=
    funext fun t => by rw [hfac t, Matrix.det_mul]
  rw [hfun]
  exact (hasDerivAt_det_one_add_smul (g⁻¹ * h)).const_mul g.det

/-- **The volume-density variation**, `δ√(-g) = ½ √(-g) · g^{μν} δg_{μν}`, in
the Lorentzian normalisation `det g < 0`. -/
theorem hasDerivAt_sqrt_neg_det (g h : Matrix n n ℝ) (hg : g.det < 0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (-(g + t • h).det))
      (Real.sqrt (-g.det) * (g⁻¹ * h).trace / 2) 0 := by
  have hu : HasDerivAt (fun t : ℝ => -(g + t • h).det) (-(g.det * (g⁻¹ * h).trace)) 0 :=
    (hasDerivAt_det_add_smul g h (isUnit_iff_ne_zero.mpr hg.ne)).neg
  have hpos : (0 : ℝ) < -g.det := by linarith
  have hne : (fun t : ℝ => -(g + t • h).det) 0 ≠ 0 := by simpa using hpos.ne'
  have hd := hu.sqrt hne
  simp only [zero_smul, add_zero] at hd
  convert hd using 1
  have hs : Real.sqrt (-g.det) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

/-- The density variation of lane 5 is a *pairing* in the sense of lane 1: it is
`h ↦ tr(Tᵀ h)` for the single explicit tensor `T = ½ √(-det g) (g⁻¹)ᵀ`. -/
theorem density_variation_is_a_trace_pairing (g : Matrix n n ℝ) :
    ∀ h : Matrix n n ℝ,
      Real.sqrt (-g.det) * (g⁻¹ * h).trace / 2
        = (((Real.sqrt (-g.det) / 2) • g⁻¹ᵀ)ᵀ * h).trace := by
  intro h
  rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.trace_smul]
  simp [smul_eq_mul]
  ring

/-- The density variation is linear in the perturbation. -/
theorem density_variation_is_linear (g h k : Matrix n n ℝ) (a b : ℝ) :
    Real.sqrt (-g.det) * (g⁻¹ * (a • h + b • k)).trace / 2
      = a * (Real.sqrt (-g.det) * (g⁻¹ * h).trace / 2)
        + b * (Real.sqrt (-g.det) * (g⁻¹ * k).trace / 2) := by
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  simp [smul_eq_mul]
  ring

/-- **The density variation determines nothing about the traceless part.**  As
soon as the index set has two elements there is a nonzero perturbation on which
the whole density variation vanishes.  So an identity involving only `δ√(-g)`
can never separate tensors — the concrete instance of
`Pairing.exists_ne_agreeing_of_ne_top` for this lane. -/
theorem density_variation_does_not_determine_the_perturbation [Nontrivial n]
    (g : Matrix n n ℝ) (hg : IsUnit g.det) :
    ∃ h : Matrix n n ℝ, h ≠ 0 ∧ (g⁻¹ * h).trace = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  refine ⟨g * Matrix.single i j (1 : ℝ), ?_, ?_⟩
  · intro hc
    have hE : Matrix.single i j (1 : ℝ) = 0 := by
      have := congrArg (fun M => g⁻¹ * M) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg] using this
    have := congrFun (congrFun hE i) j
    simp at this
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]
    simp [Matrix.trace, Matrix.diag, Matrix.single_apply, hij.symm]

end Integration.Variation.MetricDensity
