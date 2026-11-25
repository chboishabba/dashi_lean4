import Integration.Paper9BracketCuspClosure

/-! Original upper-half-plane derivative transport, SOURCE-WRITTEN.
No global analytic extension of a modular transformation is assumed:
the equality used to differentiate holds on the original open half-plane.
All terms, including dependencies, still require elaboration/kernel replay. -/
namespace Integration.Paper9EulerMobiusTransport

open Complex Function Filter UpperHalfPlane ModularForm ModularFormClass
open SlashInvariantFormClass
open scoped MatrixGroups Topology Real Manifold

noncomputable section

open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure

def scaleD : ℂ := 2 * Real.pi * Complex.I

theorem scaleD_ne_zero : scaleD ≠ 0 := by
  unfold scaleD
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

def qExt (z : ℂ) : ℂ := Periodic.qParam 1 z

theorem qExtDeriv (z : ℂ) :
    HasDerivAt qExt (scaleD * qExt z) z := by
  have h := (Complex.hasDerivAt_exp (scaleD*z)).comp z
    ((hasDerivAt_id z).const_mul scaleD)
  simpa [qExt, Periodic.qParam, scaleD, mul_comm] using h

def formExt {k : ℤ} (f : ModularForm 𝒮ℒ k) (z : ℂ) : ℂ :=
  cuspFunction 1 f (qExt z)

def formEuler {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) : ℂ :=
  qExt τ * deriv (cuspFunction 1 f) (qExt τ)

theorem formExtAt {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    formExt f τ = f τ :=
  eq_cuspFunction f τ one_mem_strictPeriods_SL one_ne_zero

theorem formExtDeriv {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    HasDerivAt (formExt f) (scaleD * formEuler f τ) (τ : ℂ) := by
  have hf := (differentiableAt_cuspFunction f one_pos
    one_mem_strictPeriods_SL (qNorm τ)).hasDerivAt
  have h := hf.comp (τ : ℂ) (qExtDeriv τ)
  simpa [formExt, formEuler, Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using h

def linear (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)

def mobius (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / linear γ z

theorem linear_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : linear γ τ ≠ 0 := by
  simpa [linear, ModularGroup.denom_apply] using
    (UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ)

theorem mobiusAt (γ : SL(2, ℤ)) (τ : ℍ) :
    mobius γ τ = ((γ • τ : ℍ) : ℂ) := by
  rw [ModularGroup.sl_moeb, UpperHalfPlane.coe_smul_of_det_pos (by simp)]
  rfl

theorem matrixDetOne (γ : SL(2, ℤ)) :
    (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
  have h : Matrix.det (↑γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
    Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

theorem linearDeriv (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (linear γ) (γ 1 0 : ℂ) z := by
  simpa [linear] using
    (((hasDerivAt_id z).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ))

theorem mobiusDeriv (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (mobius γ) ((linear γ τ)^2)⁻¹ (τ : ℂ) := by
  have hn : HasDerivAt (fun z : ℂ => (γ 0 0 : ℂ)*z+(γ 0 1 : ℂ))
      (γ 0 0 : ℂ) (τ : ℂ) := by
    simpa using (((hasDerivAt_id (τ : ℂ)).const_mul (γ 0 0 : ℂ)).add_const
      (γ 0 1 : ℂ))
  have h := hn.div (linearDeriv γ τ) (linear_ne_zero γ τ)
  have hnum : (γ 0 0 : ℂ) * linear γ τ -
      ((γ 0 0 : ℂ)*(τ : ℂ)+(γ 0 1 : ℂ))*(γ 1 0 : ℂ) = 1 := by
    unfold linear
    linear_combination matrixDetOne γ
  simpa [mobius, hnum, one_div] using h

theorem formTransform (n : ℕ) (f : ModularForm 𝒮ℒ ((n+1 : ℕ) : ℤ))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (linear γ τ)^(n+1) * f τ := by
  have hg : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  have hs : (f : ℍ → ℂ) ∣[(((n+1 : ℕ) : ℤ))] γ = f := by
    simpa only [SL_slash] using f.slash_action_eq' _ hg
  have h := (slash_action_eq'_iff _ f γ τ).1 (congrFun hs τ)
  simpa [linear, zpow_natCast] using h

-- Equality only locally at actual H point. qExt is an analytic function
-- on C but modularity is not assumed outside H.
theorem formTransformLocal (n : ℕ)
    (f : ModularForm 𝒮ℒ ((n+1 : ℕ) : ℤ))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    (formExt f ∘ mobius γ) =ᶠ[𝓝 (τ : ℂ)]
      (fun z => (linear γ z)^(n+1) * formExt f z) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  let v : ℍ := ⟨z,hz⟩
  change formExt f (mobius γ (v : ℂ)) =
    (linear γ (v : ℂ))^(n+1)*formExt f v
  rw [mobiusAt, formExtAt, formExtAt, formTransform n f γ v]

-- Actual derivative transport of a positive-weight modular form,
-- with the anomaly retained, not assumed as a premise.
theorem eulerTransform (n : ℕ) (f : ModularForm 𝒮ℒ ((n+1 : ℕ) : ℤ))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    formEuler f (γ • τ) =
      (linear γ τ)^(n+3)*formEuler f τ +
      (n+1 : ℂ)*((γ 1 0 : ℂ)/scaleD)*(linear γ τ)^(n+2)*f τ := by
  let j := linear γ τ
  let c := (γ 1 0 : ℂ)
  let U := formEuler f τ
  let V := formEuler f (γ • τ)
  have hj : j ≠ 0 := linear_ne_zero γ τ
  have hf1 : HasDerivAt (formExt f) (scaleD*V) (mobius γ τ) := by
    rw [mobiusAt]
    exact formExtDeriv f (γ • τ)
  have hLeft := hf1.comp (τ : ℂ) (mobiusDeriv γ τ)
  have hRight := ((linearDeriv γ τ).pow (n+1)).mul (formExtDeriv f τ)
  have eq := (hLeft.congr_of_eventuallyEq (formTransformLocal n f γ τ).symm).unique hRight
  have heq : scaleD*V / j^2 =
      (n+1 : ℂ)*j^n*c*f τ + j^(n+1)*(scaleD*U) := by
    simpa [j,c,U,V,div_eq_mul_inv,formExtAt, Nat.add_sub_cancel,
      Nat.cast_add, mul_comm, mul_assoc, mul_left_comm] using eq
  change V = j^(n+3)*U + (n+1 : ℂ)*(c/scaleD)*j^(n+2)*f τ
  calc
    V = (j^2/scaleD)*(scaleD*V/j^2) := by
      field_simp [hj,scaleD_ne_zero] <;> ring
    _ = (j^2/scaleD)*((n+1 : ℂ)*j^n*c*f τ+j^(n+1)*(scaleD*U)) := by rw [heq]
    _ = _ := by
      simp only [pow_succ]
      field_simp [scaleD_ne_zero] <;> ring

theorem dxTransport (γ : SL(2, ℤ)) (τ : ℍ) :
    dx (γ • τ) = ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^6*dx τ +
      4*((γ 1 0 : ℂ)/(2*Real.pi*Complex.I))*
        ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^5*
        Integration.MoonshineEisensteinAnalytic.E4 τ := by
  simpa [formEuler, qExt, scaleD, linear, dx, x, euler] using
    eulerTransform 3 Integration.MoonshineEisensteinAnalytic.E4 γ τ

theorem dyTransport (γ : SL(2, ℤ)) (τ : ℍ) :
    dy (γ • τ) = ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^8*dy τ +
      6*((γ 1 0 : ℂ)/(2*Real.pi*Complex.I))*
        ((γ 1 0 : ℂ)*τ+(γ 1 1 : ℂ))^7*
        Integration.MoonshineEisensteinAnalytic.E6 τ := by
  simpa [formEuler, qExt, scaleD, linear, dy, y, euler] using
    eulerTransform 5 Integration.MoonshineEisensteinAnalytic.E6 γ τ

theorem originalBracketSlash :
    ∀ γ : SL(2, ℤ), bracketAt ∣[(12 : ℤ)] γ = bracketAt :=
  bracketSlashFromDerivativeTransport dxTransport dyTransport

-- Unconditional intended source proof (no analytic hypotheses beyond
-- actual pinned imports); not an accepted theorem until compiled.
theorem originalRamanujan46 (τ : ℍ) :
    3 * dx τ = e2 τ * Integration.MoonshineEisensteinAnalytic.E4 τ -
      Integration.MoonshineEisensteinAnalytic.E6 τ ∧
    2 * dy τ = e2 τ * Integration.MoonshineEisensteinAnalytic.E6 τ -
      Integration.MoonshineEisensteinAnalytic.E4 τ ^ 2 :=
  ramanujan46FromSlash originalBracketSlash τ


-- Use the SAME transport on normalized Delta (weight 12), not a
-- replacement E2 or assumed quasimodular transformation.
theorem e2AsEuler (τ : ℍ) :
    e2 τ =
      formEuler Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm τ /
      Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm τ := by
  rw [Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply]
  rfl

theorem originalE2Transform (γ : SL(2, ℤ)) (τ : ℍ) :
    e2 (γ • τ) = (linear γ τ)^2 * e2 τ +
      12 * ((γ 1 0 : ℂ)/scaleD) * linear γ τ := by
  let Δ := Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm
  have hΔ : Δ τ ≠ 0 := by
    change Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm τ ≠ 0
    rw [Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply]
    exact Integration.MoonshineDeltaFinalMinCut.normalizedDelta_ne_zero_canonical τ
  have hj := linear_ne_zero γ τ
  rw [e2AsEuler, e2AsEuler]
  change formEuler Δ (γ • τ) / Δ (γ • τ) =
    (linear γ τ)^2 * (formEuler Δ τ / Δ τ) +
      12*((γ 1 0 : ℂ)/scaleD)*linear γ τ
  rw [eulerTransform 11 Δ γ τ, formTransform 11 Δ γ τ]
  norm_num
  field_simp [hΔ,hj,scaleD_ne_zero] <;> ring

-- Once the actual derivative of the preceding transformation is
-- bound, this algebra pays the weight-four cancellation exactly.
-- It does NOT assert that the second derivative source is inhabited.
theorem e2CorrectedCovarianceAlgebra (e de x j c : ℂ) :
    12*(j^4*de + 2*c*j^3*e + 12*c^2*j^2) -
      (j^2*e + 12*c*j)^2 + j^4*x =
      j^4*(12*de-e^2+x) := by ring

end
end Integration.Paper9EulerMobiusTransport
