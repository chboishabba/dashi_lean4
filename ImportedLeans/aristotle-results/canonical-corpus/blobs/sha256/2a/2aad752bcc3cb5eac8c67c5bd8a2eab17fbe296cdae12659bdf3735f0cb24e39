/-
# `RecordNormalizedInheritedBounds`: what the first-singularity rescaling really gives

The A lane's amplitude no-go (`PhysicalGaussianNearFarRelativeBound.lean`) shows
that no relative contraction can hold uniformly over the amplitude family
`V = λV₀`.  The reply is that the blow-up class actually produced by a first
singularity is **not** amplitude free: it is normalised by the running maximum
of the sup norm.  This file proves, with no hypothesis beyond the running
maximum property, exactly which facts that normalisation supplies, and
separates them into the two categories that matter for the A and C gates:

* **inherited by scaling alone** — no compactness, no regularity theory:
  * `ClayNS.recordRescale_norm_le_one` — `‖U‖_∞ ≤ 1` on the backward interval;
  * `ClayNS.recordRescale_base_norm` — `‖U(0,0)‖ = 1`, the profile is not
    trivial;
  * `ClayNS.recordRescale_divg` — incompressibility;
  * `ClayNS.recordRescale_momentum` — the Navier–Stokes momentum equation with
    the **same** viscosity;
  * `ClayNS.recordRescale_isNS` — the packaged statement of the three previous
    items;
  * `ClayNS.recordRescale_gradient_bound` — the gradient of the rescaled field
    at a point is `M⁻²` times the gradient of `u`; i.e. no gradient bound at
    all is inherited unless one is assumed upstream.

* **not inherited** — proved impossible here, so that A and C are not designed
  against norms that the class does not have:
  * `ClayNS.sup_bound_not_gradient_bound` — `‖V‖_∞ ≤ 1` together with
    incompressibility puts **no** bound on `‖∇V‖`, at any single point, and in
    particular none on any Gaussian or local Dirichlet energy: for every `C`
    there is a smooth divergence-free field with `‖V‖_∞ ≤ 1` and
    `‖∇V(0)‖ ≥ C`.

The moral for the roadmap is the one the A lane needs: the record
normalisation gives an amplitude bound *and nothing else*.  Any Dirichlet- or
Gaussian-energy quantity used to pay an interaction bill has to come from the
local energy inequality (a compactness/limit input), never from the
normalisation itself.

The rescaling is the standard one.  With `M = ‖u(t₀)‖_∞` a running maximum at
the record time `t₀`, and `x₀` a point where it is attained,

  `U(s,y) = M⁻¹ u(t₀ + s/M², x₀ + y/M)`,   `Q(s,y) = M⁻² p(t₀ + s/M², x₀ + y/M)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PressurePoisson

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The record-time rescaling -/

/-- The spacetime affine change of variables `(s,y) ↦ (t₀ + s/M², x₀ + y/M)`. -/
def rescMap (M t0 : ℝ) (x0 : E3) : STime → STime :=
  fun z => (t0 + z.1 / M ^ 2, x0 + M⁻¹ • z.2)

/-- The derivative of `rescMap`: `M⁻²` in time, `M⁻¹` in space. -/
def rescCLM (M : ℝ) : STime →L[ℝ] STime :=
  ContinuousLinearMap.prodMap ((M ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (M⁻¹ • ContinuousLinearMap.id ℝ E3)

@[simp] lemma rescCLM_apply (M : ℝ) (z : STime) :
    rescCLM M z = ((M ^ 2)⁻¹ * z.1, M⁻¹ • z.2) := rfl

lemma hasFDerivAt_rescMap (M t0 : ℝ) (x0 : E3) (z : STime) :
    HasFDerivAt (rescMap M t0 x0) (rescCLM M) z := by
  have h1 : HasFDerivAt (fun w : STime => t0 + w.1 / M ^ 2)
      ((M ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ E3) z := by
    have : HasFDerivAt (fun w : STime => w.1 / M ^ 2)
        ((M ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ E3) z := by
      simpa [div_eq_inv_mul, mul_comm] using
        ((hasFDerivAt_fst (p := z)).const_mul ((M ^ 2)⁻¹))
    simpa using this.const_add t0
  have h2 : HasFDerivAt (fun w : STime => x0 + M⁻¹ • w.2)
      (M⁻¹ • ContinuousLinearMap.snd ℝ ℝ E3) z := by
    have : HasFDerivAt (fun w : STime => M⁻¹ • w.2)
        (M⁻¹ • ContinuousLinearMap.snd ℝ ℝ E3) z :=
      (hasFDerivAt_snd (p := z)).const_smul M⁻¹
    simpa using this.const_add x0
  exact h1.prodMk h2

/-- The record-normalised velocity `U(s,y) = M⁻¹ u(t₀ + s/M², x₀ + y/M)`. -/
def recordRescaleV (M t0 : ℝ) (x0 : E3) (V : STime → E3) : STime → E3 :=
  fun z => M⁻¹ • V (rescMap M t0 x0 z)

/-- The record-normalised pressure `Q(s,y) = M⁻² p(t₀ + s/M², x₀ + y/M)`. -/
def recordRescaleP (M t0 : ℝ) (x0 : E3) (P : STime → ℝ) : STime → ℝ :=
  fun z => (M ^ 2)⁻¹ * P (rescMap M t0 x0 z)

/-! ## Amplitude normalisation: what the record time gives -/

/-- **Inherited (scaling only): `‖U‖_∞ ≤ 1` on the backward interval.**  If `M`
dominates `‖u(t)‖_∞` for every time `t` in `[0,t₀]` — the defining property of a
record time — then the rescaled profile is bounded by `1` at every rescaled
time `s ≤ 0` still lying above the initial time. -/
theorem recordRescale_norm_le_one {M t0 : ℝ} {x0 : E3} {V : STime → E3}
    (hM : 0 < M) (hrec : ∀ z : STime, 0 ≤ z.1 → z.1 ≤ t0 → ‖V z‖ ≤ M)
    {z : STime} (hs : z.1 ≤ 0) (hs0 : 0 ≤ t0 + z.1 / M ^ 2) :
    ‖recordRescaleV M t0 x0 V z‖ ≤ 1 := by
  have hM2 : (0 : ℝ) < M ^ 2 := by positivity
  have hle : t0 + z.1 / M ^ 2 ≤ t0 := by
    have : z.1 / M ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hM2.le
    linarith
  have hbound : ‖V (rescMap M t0 x0 z)‖ ≤ M := hrec _ hs0 hle
  have : ‖recordRescaleV M t0 x0 V z‖ = M⁻¹ * ‖V (rescMap M t0 x0 z)‖ := by
    rw [recordRescaleV, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  rw [this]
  calc M⁻¹ * ‖V (rescMap M t0 x0 z)‖ ≤ M⁻¹ * M :=
        mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hM).le
    _ = 1 := inv_mul_cancel₀ hM.ne'

/-- **Inherited (scaling only): the profile is normalised at the base point.**
If the record value is attained at `(t₀,x₀)` then `‖U(0,0)‖ = 1`, so the
rescaled class is non-degenerate. -/
theorem recordRescale_base_norm {M t0 : ℝ} {x0 : E3} {V : STime → E3}
    (hM : 0 < M) (hattain : ‖V (t0, x0)‖ = M) :
    ‖recordRescaleV M t0 x0 V (0, 0)‖ = 1 := by
  have hbase : rescMap M t0 x0 ((0 : ℝ), (0 : E3)) = (t0, x0) := by
    simp [rescMap]
  rw [recordRescaleV, hbase]
  rw [norm_smul, hattain, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM),
    inv_mul_cancel₀ hM.ne']

/-! ## Derivatives of the rescaled fields -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Time derivative of a rescaled field: one factor `M⁻²`. -/
lemma dtime_rescale (M t0 : ℝ) (x0 : E3) (c : ℝ) (f : STime → F)
    (hf : Differentiable ℝ f) (z : STime) :
    dtime (fun w => c • f (rescMap M t0 x0 w)) z
      = (c * (M ^ 2)⁻¹) • dtime f (rescMap M t0 x0 z) := by
  have hcomp : HasFDerivAt (fun w : STime => c • f (rescMap M t0 x0 w))
      (c • ((fderiv ℝ f (rescMap M t0 x0 z)).comp (rescCLM M))) z := by
    exact (((hf (rescMap M t0 x0 z)).hasFDerivAt).comp z
      (hasFDerivAt_rescMap M t0 x0 z)).const_smul c
  have happ : rescCLM M ((1 : ℝ), (0 : E3)) = (M ^ 2)⁻¹ • ((1 : ℝ), (0 : E3)) := by
    simp [rescCLM_apply, Prod.smul_mk]
  rw [dtime, hcomp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  rw [happ, map_smul, smul_smul, dtime]

/-- Spatial derivative of a rescaled field: one factor `M⁻¹`. -/
lemma dspace_rescale (M t0 : ℝ) (x0 : E3) (c : ℝ) (f : STime → F)
    (hf : Differentiable ℝ f) (i : Fin 3) (z : STime) :
    dspace (fun w => c • f (rescMap M t0 x0 w)) i z
      = (c * M⁻¹) • dspace f i (rescMap M t0 x0 z) := by
  have hcomp : HasFDerivAt (fun w : STime => c • f (rescMap M t0 x0 w))
      (c • ((fderiv ℝ f (rescMap M t0 x0 z)).comp (rescCLM M))) z := by
    exact (((hf (rescMap M t0 x0 z)).hasFDerivAt).comp z
      (hasFDerivAt_rescMap M t0 x0 z)).const_smul c
  rw [dspace, hcomp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, rescCLM_apply]
  rw [dspace]
  have : ((0 : ℝ), M⁻¹ • ee i) = M⁻¹ • ((0 : ℝ), ee i) := by
    simp [Prod.smul_mk]
  rw [show ((M ^ 2)⁻¹ * ((0 : ℝ), ee i).1, M⁻¹ • ((0:ℝ), ee i).2) = ((0:ℝ), M⁻¹ • ee i) by simp,
    this, map_smul, smul_smul]

/-- Smoothness is inherited by the rescaling. -/
lemma contDiff_rescale (M t0 : ℝ) (x0 : E3) (c : ℝ) {f : STime → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => c • f (rescMap M t0 x0 w)) := by
  have hres : ContDiff ℝ (⊤ : ℕ∞) (rescMap M t0 x0) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => ((t0 : ℝ) + w.1 / M ^ 2, x0 + M⁻¹ • w.2)) := by
      refine ContDiff.prodMk ?_ ?_
      · exact contDiff_const.add ((contDiff_fst).div_const _)
      · exact contDiff_const.add ((contDiff_snd).const_smul _)
    exact this
  exact (hf.comp hres).const_smul c

/-- **Inherited (scaling only): the gradient scales by `M⁻²`.**  This is the
quantitative statement that the record normalisation supplies *no* gradient
information: the rescaled gradient is the old gradient divided by `M²`, and `M`
is exactly the quantity that is blowing up. -/
theorem recordRescale_gradient_bound {M t0 : ℝ} {x0 : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (i : Fin 3) (z : STime) :
    dspace (recordRescaleV M t0 x0 V) i z
      = (M⁻¹ * M⁻¹) • dspace V i (rescMap M t0 x0 z) := by
  simpa [recordRescaleV] using
    dspace_rescale M t0 x0 M⁻¹ V (hV.differentiable (by simp)) i z

/-! ## The equations are inherited, with the same viscosity -/

/-- **Inherited (scaling only): incompressibility.** -/
theorem recordRescale_divg {M t0 : ℝ} {x0 : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime)
    (hdiv : divg V (rescMap M t0 x0 z) = 0) :
    divg (recordRescaleV M t0 x0 V) z = 0 := by
  have hd : ∀ i : Fin 3, dspace (recordRescaleV M t0 x0 V) i z
      = (M⁻¹ * M⁻¹) • dspace V i (rescMap M t0 x0 z) :=
    fun i => recordRescale_gradient_bound hV i z
  have : divg (recordRescaleV M t0 x0 V) z
      = (M⁻¹ * M⁻¹) * divg V (rescMap M t0 x0 z) := by
    simp only [divg, hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [this, hdiv, mul_zero]

/-- **Inherited (scaling only): the momentum equation with the same viscosity.**
The whole point of the parabolic rescaling: every term picks up the same factor
`M⁻³`, so the record-normalised pair solves Navier–Stokes with the *unchanged*
viscosity `ν`. -/
theorem recordRescale_momentum {M t0 nu : ℝ} {x0 : E3} {V : STime → E3} {P : STime → ℝ}
    (hM : 0 < M) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (z : STime)
    (hmom : dtime V (rescMap M t0 x0 z) + adv V (rescMap M t0 x0 z)
      = - grad P (rescMap M t0 x0 z) + nu • lap V (rescMap M t0 x0 z)) :
    dtime (recordRescaleV M t0 x0 V) z + adv (recordRescaleV M t0 x0 V) z
      = - grad (recordRescaleP M t0 x0 P) z + nu • lap (recordRescaleV M t0 x0 V) z := by
  set w := rescMap M t0 x0 z with hw
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hM2 : (M ^ 2)⁻¹ = M⁻¹ * M⁻¹ := by
    field_simp [pow_two]
  -- time derivative
  have hdt : dtime (recordRescaleV M t0 x0 V) z = (M⁻¹ * (M ^ 2)⁻¹) • dtime V w :=
    dtime_rescale M t0 x0 M⁻¹ V hVd z
  -- spatial derivatives
  have hds : ∀ i : Fin 3, dspace (recordRescaleV M t0 x0 V) i z
      = (M⁻¹ * M⁻¹) • dspace V i w := fun i => recordRescale_gradient_bound hV i z
  -- the advective term
  have hadv : adv (recordRescaleV M t0 x0 V) z = (M⁻¹ * (M⁻¹ * M⁻¹)) • adv V w := by
    simp only [adv, hds, recordRescaleV, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (M⁻¹ • V w) i = M⁻¹ * V w i := by simp
    rw [this, smul_smul, smul_smul]
    congr 1
    ring
  -- the pressure gradient
  have hdsP : ∀ i : Fin 3, dspace (recordRescaleP M t0 x0 P) i z
      = ((M ^ 2)⁻¹ * M⁻¹) • dspace P i w := by
    intro i
    have := dspace_rescale M t0 x0 ((M ^ 2)⁻¹) P hPd i z
    simpa [recordRescaleP, smul_eq_mul] using this
  have hgrad : grad (recordRescaleP M t0 x0 P) z = ((M ^ 2)⁻¹ * M⁻¹) • grad P w := by
    simp only [grad, hdsP, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact smul_assoc _ _ _
  -- the Laplacian
  have hlap : lap (recordRescaleV M t0 x0 V) z = (M⁻¹ * (M⁻¹ * M⁻¹)) • lap V w := by
    have hstep : ∀ i : Fin 3, dspace (fun u => dspace (recordRescaleV M t0 x0 V) i u) i z
        = (M⁻¹ * M⁻¹ * M⁻¹) • dspace (fun u => dspace V i u) i w := by
      intro i
      have hfun : (fun u => dspace (recordRescaleV M t0 x0 V) i u)
          = fun u => (M⁻¹ * M⁻¹) • dspace V i (rescMap M t0 x0 u) := by
        funext u; exact recordRescale_gradient_bound hV i u
      rw [hfun]
      have hdiff : Differentiable ℝ (fun u : STime => dspace V i u) := by
        have : ContDiff ℝ (⊤ : ℕ∞) (fun u : STime => dspace V i u) := by
          have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun u : STime => fderiv ℝ V u) :=
            hV.fderiv_right (by simp)
          exact (ContinuousLinearMap.apply ℝ E3 ((0 : ℝ), ee i)).contDiff.comp hfd
        exact this.differentiable (by simp)
      have := dspace_rescale M t0 x0 (M⁻¹ * M⁻¹) (fun u : STime => dspace V i u) hdiff i z
      rw [this]
    simp only [lap, hstep, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e1 : M⁻¹ * (M ^ 2)⁻¹ = M⁻¹ * M⁻¹ * M⁻¹ := by rw [hM2]; ring
  have e2 : M⁻¹ * (M⁻¹ * M⁻¹) = M⁻¹ * M⁻¹ * M⁻¹ := by ring
  have e3 : (M ^ 2)⁻¹ * M⁻¹ = M⁻¹ * M⁻¹ * M⁻¹ := by rw [hM2]
  rw [hdt, hadv, hgrad, hlap, e1, e2, e3]
  have hkey : (M⁻¹ * M⁻¹ * M⁻¹) • (dtime V w + adv V w)
      = (M⁻¹ * M⁻¹ * M⁻¹) • (- grad P w + nu • lap V w) := by rw [hmom]
  rw [smul_add, smul_add, smul_neg, smul_comm] at hkey
  exact hkey

/-- **The packaged inheritance statement.**  The record-normalised pair solves,
pointwise, the same incompressible Navier–Stokes system with the same
viscosity, and the velocity satisfies `‖U‖_∞ ≤ 1` on the backward interval with
`‖U(0,0)‖ = 1`.  Nothing else is claimed: no decay, no integrability, no
gradient bound. -/
theorem recordRescale_isNS {M t0 nu : ℝ} {x0 : E3} {V : STime → E3} {P : STime → ℝ}
    (hM : 0 < M) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hrec : ∀ z : STime, 0 ≤ z.1 → z.1 ≤ t0 → ‖V z‖ ≤ M)
    (hattain : ‖V (t0, x0)‖ = M) :
    ContDiff ℝ (⊤ : ℕ∞) (recordRescaleV M t0 x0 V)
      ∧ ContDiff ℝ (⊤ : ℕ∞) (recordRescaleP M t0 x0 P)
      ∧ (∀ z : STime, dtime (recordRescaleV M t0 x0 V) z + adv (recordRescaleV M t0 x0 V) z
          = - grad (recordRescaleP M t0 x0 P) z + nu • lap (recordRescaleV M t0 x0 V) z)
      ∧ (∀ z : STime, divg (recordRescaleV M t0 x0 V) z = 0)
      ∧ (∀ z : STime, z.1 ≤ 0 → 0 ≤ t0 + z.1 / M ^ 2 → ‖recordRescaleV M t0 x0 V z‖ ≤ 1)
      ∧ ‖recordRescaleV M t0 x0 V (0, 0)‖ = 1 := by
  refine ⟨contDiff_rescale M t0 x0 M⁻¹ hV, ?_, ?_, ?_, ?_, recordRescale_base_norm hM hattain⟩
  · have := contDiff_rescale (F := ℝ) M t0 x0 ((M ^ 2)⁻¹) hP
    simpa [recordRescaleP, smul_eq_mul] using this
  · intro z; exact recordRescale_momentum hM hV hP z (hmom _)
  · intro z; exact recordRescale_divg hV z (hdiv _)
  · intro z hz hz0; exact recordRescale_norm_le_one hM hrec hz hz0

/-! ## What the normalisation does *not* give -/

/-- A one-parameter family of smooth divergence-free shear fields with sup norm
at most one and arbitrarily large gradient: `V_n(y) = sin(n y₂) e₁`. -/
def shearProbe (n : ℝ) : E3 → E3 := fun y => Real.sin (n * y 1) • ee 0

lemma shearProbe_smooth (n : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (shearProbe n) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => Real.sin (n * y 1)) :=
    Real.contDiff_sin.comp (((EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ)).contDiff.const_smul n)
  exact h.smul contDiff_const

lemma hasFDerivAt_shearProbe (n : ℝ) (y : E3) :
    HasFDerivAt (shearProbe n)
      (((Real.cos (n * y 1)) • (n • (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ))).smulRight
        (ee 0)) y := by
  have hproj : HasFDerivAt (fun w : E3 => n * w 1)
      (n • (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ)) y := by
    simpa using ((EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt).const_smul n
  have hsin : HasFDerivAt (fun w : E3 => Real.sin (n * w 1))
      ((Real.cos (n * y 1)) • (n • (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ))) y := by
    simpa [Function.comp] using (Real.hasDerivAt_sin (n * y 1)).comp_hasFDerivAt y hproj
  exact hsin.smul_const (ee 0)

lemma shearProbe_norm_le_one (n : ℝ) (y : E3) : ‖shearProbe n y‖ ≤ 1 := by
  have h1 : ‖(ee 0 : E3)‖ = 1 := by simp [ee, EuclideanSpace.norm_single]
  have : ‖shearProbe n y‖ = |Real.sin (n * y 1)| * ‖(ee 0 : E3)‖ := by
    rw [shearProbe, norm_smul, Real.norm_eq_abs]
  rw [this, h1, mul_one]
  exact Real.abs_sin_le_one _

lemma shearProbe_fderiv_apply (n : ℝ) (y : E3) (i : Fin 3) :
    fderiv ℝ (shearProbe n) y (ee i)
      = (Real.cos (n * y 1) * (n * (ee i : E3) 1)) • (ee 0 : E3) := by
  rw [(hasFDerivAt_shearProbe n y).fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

lemma shearProbe_divSpace (n : ℝ) (y : E3) :
    (∑ i, (fderiv ℝ (shearProbe n) y (ee i)) i) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [shearProbe_fderiv_apply n y i]
  fin_cases i <;> simp [ee, EuclideanSpace.single_apply]

/-- **Not inherited: the sup bound gives no gradient bound.**  For every `C`
there is a smooth divergence-free field with `‖V‖_∞ ≤ 1` whose gradient at the
origin exceeds `C`.  Consequently the record normalisation `‖V‖_∞ ≤ 1` cannot,
by itself, bound any Dirichlet-type quantity (Gaussian weighted or local): all
such bills must be paid by the local energy inequality inherited through the
blow-up limit, never by the normalisation. -/
theorem sup_bound_not_gradient_bound (C : ℝ) :
    ∃ V : E3 → E3, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ y : E3, ‖V y‖ ≤ 1)
      ∧ (∀ y : E3, (∑ i, (fderiv ℝ V y (ee i)) i) = 0)
      ∧ C < ‖fderiv ℝ V 0 (ee 1)‖ := by
  refine ⟨shearProbe (|C| + 1), shearProbe_smooth _, shearProbe_norm_le_one _,
    shearProbe_divSpace _, ?_⟩
  have hval := shearProbe_fderiv_apply (|C| + 1) (0 : E3) 1
  have h0 : ((0 : E3) 1) = 0 := rfl
  have h1 : ((ee (1 : Fin 3) : E3) 1) = 1 := by simp [ee, EuclideanSpace.single_apply]
  rw [hval, h0, h1, mul_zero, Real.cos_zero, one_mul, mul_one, norm_smul]
  have hbase : ‖(ee 0 : E3)‖ = 1 := by simp [ee, EuclideanSpace.norm_single]
  rw [hbase, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < |C| + 1)]
  have := le_abs_self C
  linarith

end ClayNS
