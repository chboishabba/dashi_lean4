import Integration.Variation.MetricDensity

/-!
# QFT/GR frontier, lane 9 — the inverse-metric variation

Lane 5 (`Integration.Variation.MetricDensity`) supplies one of the two purely
algebraic ingredients of the Einstein–Hilbert first variation: the density
factor `δ√(-g) = ½ √(-g) · tr(g⁻¹ δg)`.  The frontier report lists the remaining
ingredients of item A as curvature (Christoffels, Ricci, Palatini) — genuinely
analytic and geometric — but there is one more *algebraic* ingredient sitting
between the two, used every time an index is raised inside a variation:

```
δ(g⁻¹) = − g⁻¹ (δg) g⁻¹              i.e.   δg^{μν} = − g^{μα} g^{νβ} δg_{αβ}.
```

This lane proves it, in the same honest model as lane 5: `g` is a single
invertible real matrix, the variation is the derivative at `t = 0` along the
straight line `g + t h`, and no manifold, curvature or integration is involved.

The two lanes then combine into the variation of the *densitised* inverse metric
`√(-g) g⁻¹`, which is the object that actually appears in a matter action.

The lane also records the sharp contrast with lane 5 on the information
question.  The density variation is a trace, so it forgets everything except one
scalar (`MetricDensity.density_variation_does_not_determine_the_perturbation`);
the inverse-metric variation forgets nothing
(`inverse_variation_determines_the_perturbation`) — it is an injective linear
map of the perturbation.  And it preserves symmetry
(`isSymm_inverse_variation`), so it maps the physical fibre of lane 6/8 into
itself.

## What is proved

* `hasDerivAt_inv_add_smul` — `δ(g⁻¹) = −g⁻¹ (δg) g⁻¹` at any invertible `g`;
* `inverse_variation_is_a_trace_pairing` — against a fixed tensor the
  inverse-metric variation is again a trace pairing, with the explicitly
  conjugated tensor;
* `isSymm_inverse_variation` — symmetry of `g` and of the perturbation is
  inherited by the variation;
* `inverse_variation_determines_the_perturbation` and
  `inverse_variation_is_injective` — no information is lost, in contrast with
  the density lane;
* `hasDerivAt_sqrt_neg_det_smul_inv` — the two lanes combined:
  `δ(√(-g) g⁻¹) = √(-g) (½ tr(g⁻¹ δg) g⁻¹ − g⁻¹ (δg) g⁻¹)`.

## What is *not* proved

Nothing here mentions curvature, connections, manifolds or integration, and the
matrix is not required to have Lorentzian signature except where lane 5's
`√(-det)` normalisation is used.  This lane closes the *second* algebraic
ingredient of item A; the curvature ingredients remain open exactly as the
frontier report states.
-/

namespace Integration.Variation.InverseMetric

open Matrix
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The inverse-metric variation.**  `d/dt (g + t h)⁻¹ |_{t=0} = −g⁻¹ h g⁻¹`
at any invertible `g`.  This is the matrix form of `δg^{μν} = −g^{μα} g^{νβ}
δg_{αβ}`. -/
theorem hasDerivAt_inv_add_smul (g h : Matrix n n ℝ) (hg : IsUnit g) :
    HasDerivAt (fun t : ℝ => (g + t • h)⁻¹) (-(g⁻¹ * h * g⁻¹)) 0 := by
  obtain ⟨u, rfl⟩ := hg
  set F : ℝ → Matrix n n ℝ := fun t => (u : Matrix n n ℝ) + t • h with hF
  have hF0 : F 0 = (u : Matrix n n ℝ) := by simp [hF]
  have hline : HasDerivAt F h 0 := by
    have hsmul : HasDerivAt (fun t : ℝ => t • h) h 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
    simpa [hF] using hsmul.const_add (u : Matrix n n ℝ)
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) (↑u⁻¹) (↑u⁻¹)) (F 0) := by
    rw [hF0]
    exact hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hcomp := hinv.comp_hasDerivAt 0 hline
  have huinv : ((u : Matrix n n ℝ))⁻¹ = ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  have hfun : (fun t : ℝ => (((u : Matrix n n ℝ) + t • h))⁻¹)
      = fun t => Ring.inverse (F t) := by
    funext t
    rw [hF]
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  convert hcomp using 1
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, huinv]

/-- Against a fixed tensor `A`, the inverse-metric variation is again a trace
pairing in the perturbation — with the tensor conjugated by `g⁻¹`.  So raising
indices inside a variation moves the conjugation onto the stress side and stays
inside the pairing language of lane 1. -/
theorem inverse_variation_is_a_trace_pairing (g A h : Matrix n n ℝ) :
    (A * -(g⁻¹ * h * g⁻¹)).trace = (-(g⁻¹ * A * g⁻¹) * h).trace := by
  rw [Matrix.mul_neg, Matrix.trace_neg, Matrix.neg_mul, Matrix.trace_neg]
  congr 1
  have h1 : A * (g⁻¹ * h * g⁻¹) = A * g⁻¹ * h * g⁻¹ := by
    simp [Matrix.mul_assoc]
  have h2 : g⁻¹ * A * g⁻¹ * h = g⁻¹ * (A * g⁻¹) * h := by
    simp [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_cycle]

/-- The inverse-metric variation preserves symmetry: a symmetric perturbation of
a symmetric metric produces a symmetric variation.  So the map sends the
physical fibre of lanes 6 and 8 into itself. -/
theorem isSymm_inverse_variation {g h : Matrix n n ℝ} (hg : g.IsSymm) (hh : h.IsSymm) :
    (-(g⁻¹ * h * g⁻¹)).IsSymm := by
  have hginv : (g⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_nonsing_inv, hg.eq]
  unfold Matrix.IsSymm
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, hginv.eq, hh.eq,
    Matrix.mul_assoc]

/-- **The inverse-metric variation loses no information.**  If the variation
vanishes then the perturbation vanishes — the exact opposite of the density
lane, where an entire traceless subspace is invisible. -/
theorem inverse_variation_determines_the_perturbation {g h : Matrix n n ℝ} (hg : IsUnit g.det)
    (hzero : -(g⁻¹ * h * g⁻¹) = 0) : h = 0 := by
  have h0 : g⁻¹ * h * g⁻¹ = 0 := by
    have := congrArg (fun M : Matrix n n ℝ => -M) hzero
    simpa using this
  have hleft := congrArg (fun M : Matrix n n ℝ => g * M * g) h0
  simp only [Matrix.mul_zero, Matrix.zero_mul] at hleft
  rw [Matrix.mul_assoc g (g⁻¹ * h * g⁻¹) g, Matrix.mul_assoc (g⁻¹ * h) g⁻¹ g,
    Matrix.nonsing_inv_mul g hg, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv g hg, Matrix.one_mul] at hleft
  exact hleft

/-- The same statement as injectivity of the linear map `h ↦ −g⁻¹ h g⁻¹`. -/
theorem inverse_variation_is_injective {g : Matrix n n ℝ} (hg : IsUnit g.det) :
    Function.Injective (fun h : Matrix n n ℝ => -(g⁻¹ * h * g⁻¹)) := by
  intro h k hhk
  have hsub : -(g⁻¹ * (h - k) * g⁻¹) = 0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, neg_sub] at *
    rw [sub_eq_zero]
    have := hhk
    simp only [neg_inj] at this
    exact this.symm
  have := inverse_variation_determines_the_perturbation hg hsub
  rwa [sub_eq_zero] at this

/-- **The two algebraic ingredients combined.**  The variation of the densitised
inverse metric `√(-g) g⁻¹` — the object appearing in a matter action — is
`√(-g) (½ tr(g⁻¹ δg) g⁻¹ − g⁻¹ (δg) g⁻¹)`. -/
theorem hasDerivAt_sqrt_neg_det_smul_inv (g h : Matrix n n ℝ) (hg : g.det < 0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (-(g + t • h).det) • (g + t • h)⁻¹)
      ((Real.sqrt (-g.det) * (g⁻¹ * h).trace / 2) • g⁻¹
        + Real.sqrt (-g.det) • -(g⁻¹ * h * g⁻¹)) 0 := by
  have hdet := MetricDensity.hasDerivAt_sqrt_neg_det g h hg
  have hinv := hasDerivAt_inv_add_smul g h ((Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg.ne))
  have hcomb := hdet.smul hinv
  simpa [smul_neg, add_comm] using hcomb

end Integration.Variation.InverseMetric
