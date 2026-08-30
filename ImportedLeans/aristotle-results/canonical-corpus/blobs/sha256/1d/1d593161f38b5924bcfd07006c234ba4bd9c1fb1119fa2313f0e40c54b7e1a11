/-
# An exact non-constant global smooth periodic solution.

`RequestProject/NavierStokes/ClayPeriodic.lean` contains the non-vacuity check
`ClayNS.isNSSolution_const`, which only exhibits constant fields.  This file
supplies a genuinely non-constant, dissipative, exactly solvable witness of the
analytic Navier–Stokes system used by the Clay statement: the decaying shear
wave

`u(t,x) = e^{-4π²νt} sin(2πx₃) e₁`,   `p = 0`.

Every clause is derived from Fréchet derivatives, not assumed:

* `ClayNS.isNSSolution_shearWave` — `(u, p)` is a global smooth `ℤ³`-periodic
  solution of the incompressible Navier–Stokes system with viscosity `ν`;
* `ClayNS.admissibleDatum_shearWave` — its time-zero trace is a Clay-admissible
  initial datum;
* `ClayNS.shearWave_ne_const` — the solution really is non-constant.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PressurePoisson

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Coordinate functionals on spacetime -/

/-- The time coordinate, as a continuous linear functional on spacetime. -/
def tc : STime →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E3

/-- The third space coordinate, as a continuous linear functional on
spacetime. -/
def zc : STime →L[ℝ] ℝ := (EuclideanSpace.proj (2 : Fin 3)).comp (ContinuousLinearMap.snd ℝ ℝ E3)

@[simp] lemma tc_apply (z : STime) : tc z = z.1 := rfl

@[simp] lemma zc_apply (z : STime) : zc z = z.2 2 := rfl

/-! ## Elementary derivatives of the building blocks -/

lemma hasFDerivAt_expLin (c : ℝ) (z : STime) :
    HasFDerivAt (fun w : STime => Real.exp (c * tc w)) ((c * Real.exp (c * tc z)) • tc) z := by
  have h0 : HasDerivAt (fun r : ℝ => c * r) c (tc z) := by
    simpa using (hasDerivAt_id (tc z)).const_mul c
  have h1 : HasDerivAt (fun r : ℝ => Real.exp (c * r)) (Real.exp (c * tc z) * c) (tc z) :=
    (Real.hasDerivAt_exp (c * tc z)).comp _ h0
  simpa [mul_comm] using h1.comp_hasFDerivAt z tc.hasFDerivAt

lemma hasFDerivAt_sinLin (c : ℝ) (z : STime) :
    HasFDerivAt (fun w : STime => Real.sin (c * zc w)) ((c * Real.cos (c * zc z)) • zc) z := by
  have h0 : HasDerivAt (fun r : ℝ => c * r) c (zc z) := by
    simpa using (hasDerivAt_id (zc z)).const_mul c
  have h1 : HasDerivAt (fun r : ℝ => Real.sin (c * r)) (Real.cos (c * zc z) * c) (zc z) :=
    (Real.hasDerivAt_sin (c * zc z)).comp _ h0
  simpa [mul_comm] using h1.comp_hasFDerivAt z zc.hasFDerivAt

lemma hasFDerivAt_cosLin (c : ℝ) (z : STime) :
    HasFDerivAt (fun w : STime => Real.cos (c * zc w))
      (-((c * Real.sin (c * zc z)) • zc)) z := by
  have h0 : HasDerivAt (fun r : ℝ => c * r) c (zc z) := by
    simpa using (hasDerivAt_id (zc z)).const_mul c
  have h1 : HasDerivAt (fun r : ℝ => Real.cos (c * r)) (-Real.sin (c * zc z) * c) (zc z) :=
    (Real.hasDerivAt_cos (c * zc z)).comp _ h0
  simpa [mul_comm, neg_smul, neg_mul, mul_neg] using h1.comp_hasFDerivAt z zc.hasFDerivAt

lemma contDiff_expLin (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => Real.exp (c * tc w)) :=
  Real.contDiff_exp.comp (contDiff_const.mul tc.contDiff)

lemma contDiff_sinLin (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => Real.sin (c * zc w)) :=
  Real.contDiff_sin.comp (contDiff_const.mul zc.contDiff)

lemma contDiff_cosLin (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : STime => Real.cos (c * zc w)) :=
  Real.contDiff_cos.comp (contDiff_const.mul zc.contDiff)

/-! ## The shear wave -/

/-- The spatial wave number `2π` of the unit-period shear wave. -/
def kk : ℝ := 2 * Real.pi

/-- The scalar profile `e^{-4π²νt} sin(2πx₃)` of the shear wave. -/
def shearScalar (nu : ℝ) : STime → ℝ :=
  fun w => Real.exp (-(kk ^ 2 * nu) * tc w) * Real.sin (kk * zc w)

/-- The third-direction derivative of the scalar profile. -/
def shearDz (nu : ℝ) : STime → ℝ :=
  fun w => Real.exp (-(kk ^ 2 * nu) * tc w) * (kk * Real.cos (kk * zc w))

/-- The shear-wave velocity field `u = e^{-4π²νt} sin(2πx₃) e₁`. -/
def shearVel (nu : ℝ) : STime → E3 := fun w => shearScalar nu w • ee 0

/-- The shear-wave pressure: identically zero. -/
def shearPres : STime → ℝ := fun _ => 0

lemma contDiff_shearScalar (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (shearScalar nu) :=
  (contDiff_expLin _).mul (contDiff_sinLin _)

lemma contDiff_shearDz (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (shearDz nu) :=
  (contDiff_expLin _).mul (contDiff_const.mul (contDiff_cosLin _))

lemma contDiff_shearVel (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (shearVel nu) :=
  (contDiff_shearScalar nu).smul contDiff_const

lemma hasFDerivAt_shearScalar (nu : ℝ) (z : STime) :
    HasFDerivAt (shearScalar nu)
      (Real.exp (-(kk ^ 2 * nu) * tc z) • ((kk * Real.cos (kk * zc z)) • zc)
        + Real.sin (kk * zc z) • ((-(kk ^ 2 * nu) * Real.exp (-(kk ^ 2 * nu) * tc z)) • tc)) z :=
  (hasFDerivAt_expLin _ z).mul (hasFDerivAt_sinLin _ z)

lemma hasFDerivAt_shearDz (nu : ℝ) (z : STime) :
    HasFDerivAt (shearDz nu)
      (Real.exp (-(kk ^ 2 * nu) * tc z) • ((kk : ℝ) • (-((kk * Real.sin (kk * zc z)) • zc)))
        + (kk * Real.cos (kk * zc z))
            • ((-(kk ^ 2 * nu) * Real.exp (-(kk ^ 2 * nu) * tc z)) • tc)) z :=
  (hasFDerivAt_expLin _ z).mul ((hasFDerivAt_cosLin _ z).const_smul (kk : ℝ))

/-! ## The derivatives of the shear wave -/

lemma dtime_shearScalar (nu : ℝ) (z : STime) :
    dtime (shearScalar nu) z = -(kk ^ 2 * nu) * shearScalar nu z := by
  rw [dtime, (hasFDerivAt_shearScalar nu z).fderiv]
  simp [shearScalar]
  ring

lemma dspace_shearScalar_zero (nu : ℝ) : dspace (shearScalar nu) 0 = fun _ => 0 := by
  funext z
  rw [dspace, (hasFDerivAt_shearScalar nu z).fderiv]
  simp [ee, EuclideanSpace.single_apply]

lemma dspace_shearScalar_one (nu : ℝ) : dspace (shearScalar nu) 1 = fun _ => 0 := by
  funext z
  rw [dspace, (hasFDerivAt_shearScalar nu z).fderiv]
  simp [ee, EuclideanSpace.single_apply]

lemma dspace_shearScalar_two (nu : ℝ) : dspace (shearScalar nu) 2 = shearDz nu := by
  funext z
  rw [dspace, (hasFDerivAt_shearScalar nu z).fderiv]
  simp [shearDz, ee, EuclideanSpace.single_apply]

lemma dspace_shearDz_two (nu : ℝ) (z : STime) :
    dspace (shearDz nu) 2 z = -(kk ^ 2) * shearScalar nu z := by
  rw [dspace, (hasFDerivAt_shearDz nu z).fderiv]
  simp [shearScalar, ee, EuclideanSpace.single_apply]
  ring

/-! ## Transfer to the vector field -/

lemma dspace_smul_const (f : STime → ℝ) (hf : Differentiable ℝ f) (c : E3) (i : Fin 3) :
    dspace (fun w => f w • c) i = fun z => (dspace f i z) • c := by
  funext z
  rw [dspace, (((hf z).hasFDerivAt).smul_const c).fderiv]
  rfl

lemma dtime_smul_const (f : STime → ℝ) (hf : Differentiable ℝ f) (c : E3) (z : STime) :
    dtime (fun w => f w • c) z = (dtime f z) • c := by
  rw [dtime, (((hf z).hasFDerivAt).smul_const c).fderiv]
  rfl

lemma dspace_shearVel_zero (nu : ℝ) : dspace (shearVel nu) 0 = fun _ => (0 : E3) := by
  have hV : shearVel nu = fun w => shearScalar nu w • ee 0 := rfl
  rw [hV, dspace_smul_const _
    (differentiable_of_contDiffTop (contDiff_shearScalar nu)) (ee 0) 0,
    dspace_shearScalar_zero]
  simp

lemma dspace_shearVel_one (nu : ℝ) : dspace (shearVel nu) 1 = fun _ => (0 : E3) := by
  have hV : shearVel nu = fun w => shearScalar nu w • ee 0 := rfl
  rw [hV, dspace_smul_const _
    (differentiable_of_contDiffTop (contDiff_shearScalar nu)) (ee 0) 1,
    dspace_shearScalar_one]
  simp

lemma dspace_shearVel_two (nu : ℝ) : dspace (shearVel nu) 2 = fun z => (shearDz nu z) • ee 0 := by
  have hV : shearVel nu = fun w => shearScalar nu w • ee 0 := rfl
  rw [hV, dspace_smul_const _
    (differentiable_of_contDiffTop (contDiff_shearScalar nu)) (ee 0) 2,
    dspace_shearScalar_two]

lemma dtime_shearVel (nu : ℝ) (z : STime) :
    dtime (shearVel nu) z = (-(kk ^ 2 * nu) * shearScalar nu z) • ee 0 := by
  have hV : shearVel nu = fun w => shearScalar nu w • ee 0 := rfl
  rw [hV, dtime_smul_const _ (differentiable_of_contDiffTop (contDiff_shearScalar nu))
    (ee 0) z, dtime_shearScalar]

lemma lap_shearVel (nu : ℝ) (z : STime) :
    lap (shearVel nu) z = (-(kk ^ 2) * shearScalar nu z) • ee 0 := by
  have h0 : dspace (fun w => dspace (shearVel nu) 0 w) 0 z = 0 := by
    have : (fun w => dspace (shearVel nu) 0 w) = fun _ : STime => (0 : E3) :=
      dspace_shearVel_zero nu
    rw [this, dspace]
    simp
  have h1 : dspace (fun w => dspace (shearVel nu) 1 w) 1 z = 0 := by
    have : (fun w => dspace (shearVel nu) 1 w) = fun _ : STime => (0 : E3) :=
      dspace_shearVel_one nu
    rw [this, dspace]
    simp
  have h2 : dspace (fun w => dspace (shearVel nu) 2 w) 2 z = (-(kk ^ 2) * shearScalar nu z) • ee 0 := by
    have hfun : (fun w => dspace (shearVel nu) 2 w) = fun w => (shearDz nu w) • ee 0 :=
      dspace_shearVel_two nu
    rw [hfun, dspace_smul_const _ (differentiable_of_contDiffTop (contDiff_shearDz nu)) (ee 0) 2]
    show dspace (shearDz nu) 2 z • ee 0 = (-(kk ^ 2) * shearScalar nu z) • ee 0
    rw [dspace_shearDz_two]
  rw [lap, Fin.sum_univ_three, h0, h1, h2]
  simp

lemma adv_shearVel (nu : ℝ) (z : STime) : adv (shearVel nu) z = 0 := by
  have hv1 : shearVel nu z 1 = 0 := by
    show (shearScalar nu z • ee 0) 1 = 0
    simp [ee, EuclideanSpace.single_apply]
  have hv2 : shearVel nu z 2 = 0 := by
    show (shearScalar nu z • ee 0) 2 = 0
    simp [ee, EuclideanSpace.single_apply]
  rw [adv, Fin.sum_univ_three, hv1, hv2, congrFun (dspace_shearVel_zero nu) z]
  simp

lemma divg_shearVel (nu : ℝ) (z : STime) : divg (shearVel nu) z = 0 := by
  have h0 : (dspace (shearVel nu) 0 z) 0 = 0 := by
    rw [congrFun (dspace_shearVel_zero nu) z]; simp
  have h1 : (dspace (shearVel nu) 1 z) 1 = 0 := by
    rw [congrFun (dspace_shearVel_one nu) z]; simp
  have h2 : (dspace (shearVel nu) 2 z) 2 = 0 := by
    rw [congrFun (dspace_shearVel_two nu) z]
    show (shearDz nu z • ee 0) 2 = 0
    simp [ee, EuclideanSpace.single_apply]
  rw [divg, Fin.sum_univ_three, h0, h1, h2]
  simp

lemma grad_shearPres (z : STime) : grad shearPres z = 0 := by
  have h : ∀ i : Fin 3, dspace shearPres i z = 0 := by
    intro i
    have hP : shearPres = fun _ : STime => (0 : ℝ) := rfl
    rw [dspace, hP]
    simp
  rw [grad]
  simp [h]

/-! ## Periodicity -/

lemma shearScalar_periodic (nu : ℝ) : SpacePeriodic (shearScalar nu) := by
  intro z j
  have hcoord : (z.2 + ee j) 2 = z.2 2 + (if (2 : Fin 3) = j then 1 else 0) := by
    show z.2 2 + (ee j) 2 = _
    simp [ee, EuclideanSpace.single_apply]
  show Real.exp (-(kk ^ 2 * nu) * z.1) * Real.sin (kk * ((z.2 + ee j) 2))
    = Real.exp (-(kk ^ 2 * nu) * z.1) * Real.sin (kk * (z.2 2))
  rw [hcoord]
  by_cases hj : (2 : Fin 3) = j
  · rw [if_pos hj]
    have : kk * (z.2 2 + 1) = kk * z.2 2 + 2 * Real.pi := by rw [kk]; ring
    rw [this, Real.sin_add_two_pi]
  · rw [if_neg hj]
    simp

lemma shearVel_periodic (nu : ℝ) : SpacePeriodic (shearVel nu) := by
  intro z j
  show shearScalar nu (z.1, z.2 + ee j) • ee 0 = shearScalar nu z • ee 0
  rw [shearScalar_periodic nu z j]

lemma shearPres_periodic : SpacePeriodic shearPres := fun _ _ => rfl

/-! ## The witness -/

/-- **An exact non-constant global smooth periodic solution.**  The decaying
shear wave `u(t,x) = e^{-4π²νt} sin(2πx₃) e₁` with zero pressure solves the
incompressible Navier–Stokes system with viscosity `ν`. -/
theorem isNSSolution_shearWave (nu : ℝ) : IsNSSolution nu (shearVel nu) shearPres where
  smoothVelocity := contDiff_shearVel nu
  smoothPressure := contDiff_const
  periodicVelocity := shearVel_periodic nu
  periodicPressure := shearPres_periodic
  momentum := by
    intro z _
    rw [dtime_shearVel, adv_shearVel, lap_shearVel, grad_shearPres, add_zero, neg_zero, zero_add,
      smul_smul]
    congr 1
    ring
  incompressible := fun z _ => divg_shearVel nu z

/-- The time-zero trace of the shear wave is a Clay-admissible initial datum. -/
theorem admissibleDatum_shearWave (nu : ℝ) :
    AdmissibleDatum (fun x : E3 => shearVel nu (0, x)) where
  smooth := (contDiff_shearVel nu).comp (contDiff_const.prodMk contDiff_id)
  periodic := by
    intro x j
    exact shearVel_periodic nu (0, x) j
  divergenceFree := by
    intro x
    have hsl : ∀ i : Fin 3, fderiv ℝ (fun y : E3 => shearVel nu (0, y)) x (ee i)
        = dspace (shearVel nu) i (0, x) := by
      intro i
      have hd : HasFDerivAt (fun y : E3 => shearVel nu (0, y))
          ((fderiv ℝ (shearVel nu) (0, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x := by
        have h1 : HasFDerivAt (shearVel nu) (fderiv ℝ (shearVel nu) (0, x)) ((0 : ℝ), x) :=
          ((differentiable_of_contDiffTop (contDiff_shearVel nu)) ((0 : ℝ), x)).hasFDerivAt
        have h2 : HasFDerivAt (fun y : E3 => ((0 : ℝ), y))
            (ContinuousLinearMap.inr ℝ ℝ E3) x :=
          (ContinuousLinearMap.inr ℝ ℝ E3).hasFDerivAt
        exact h1.comp x h2
      rw [hd.fderiv]
      rfl
    have hdiv := divg_shearVel nu (0, x)
    rw [divg] at hdiv
    calc (∑ i, (fderiv ℝ (fun y : E3 => shearVel nu (0, y)) x (ee i)) i)
        = ∑ i, (dspace (shearVel nu) i (0, x)) i :=
          Finset.sum_congr rfl fun i _ => by rw [hsl i]
      _ = 0 := hdiv

/-- The shear wave is genuinely non-constant: at time `0` its first component
takes the value `1` at `x₃ = 1/4` and the value `0` at `x₃ = 0`. -/
theorem shearWave_ne_const (nu : ℝ) :
    shearVel nu ((0 : ℝ), (0 : E3)) ≠ shearVel nu ((0 : ℝ), ((1 : ℝ) / 4) • ee 2) := by
  intro hcontra
  have h0 : shearVel nu ((0 : ℝ), (0 : E3)) 0 = 0 := by
    show (shearScalar nu ((0 : ℝ), (0 : E3)) • ee 0) 0 = 0
    have : shearScalar nu ((0 : ℝ), (0 : E3)) = 0 := by
      show Real.exp (-(kk ^ 2 * nu) * 0) * Real.sin (kk * ((0 : E3) 2)) = 0
      simp
    rw [this]
    simp
  have hcoord : (((1 : ℝ) / 4) • ee 2 : E3) 2 = 1 / 4 := by
    show (1 / 4 : ℝ) * (ee 2) 2 = 1 / 4
    simp [ee, EuclideanSpace.single_apply]
  have h1 : shearVel nu ((0 : ℝ), ((1 : ℝ) / 4) • ee 2) 0 = 1 := by
    show (shearScalar nu ((0 : ℝ), ((1 : ℝ) / 4) • ee 2) • ee 0) 0 = 1
    have hs : shearScalar nu ((0 : ℝ), ((1 : ℝ) / 4) • ee 2) = 1 := by
      show Real.exp (-(kk ^ 2 * nu) * 0) * Real.sin (kk * ((((1 : ℝ) / 4) • ee 2 : E3) 2)) = 1
      rw [hcoord]
      have : kk * (1 / 4) = Real.pi / 2 := by rw [kk]; ring
      rw [this]
      simp
    rw [hs]
    show (1 : ℝ) * (ee 0) 0 = 1
    simp [ee, EuclideanSpace.single_apply]
  rw [hcontra, h1] at h0
  norm_num at h0

end ClayNS
