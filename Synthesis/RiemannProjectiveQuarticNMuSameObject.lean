import Synthesis.RiemannProjectivePhysicalMuNormalization
import Synthesis.RiemannProjectiveQuarticCompletedResidual
import Synthesis.RiemannProjectiveQuarticNegativeZeroWindow

/-!
# Exact quartic base + Gamma = one half of a literal N-mu pairing

For a physical rescaling g_r(u)=G(r u), the projective physical cosine kernel
obeys

  Phi_{g_r,r}(delta)
    = r^-2 Phi_{G,1}(delta/r).

For the quartic detector r=t/16 this is exactly the ordinate test already used
by the negative-window theorem:

  phi_t^Q(gamma)
    = r^-2 Phi_Q((gamma-t)/r).

Combining this with the generic projective mu normalization gives

  projectiveRvMMuSignedPair(g_t,t,r)
    = -(1/4) integral phi_t^Q(tau) mu(tau) d tau.

Hence, with the reflection-orbit factor on the zero side,

  quarticBaseMuResidual(W,t)
    = 1/2 *
      ( sum'_rho m_rho phi_t^Q(Im rho)
        - integral phi_t^Q(tau) mu(tau) d tau ).

This is the exact infinite signed discrepancy object for the quartic route.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23

theorem genericProjectiveBaseKernel_rescale
    {G : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r)
    (delta : ℝ) :
    genericProjectiveBaseKernel
        (projectiveRescaleProfile G r) r delta
      =
    (1/r^2) *
      genericProjectiveBaseKernel G 1 (delta/r) := by
  unfold genericProjectiveBaseKernel compactCosineTransform
  let F : ℝ → ℝ := fun x =>
    genericProjectivePhysicalProfile G 1 x
      * Real.cos ((delta/r)*x)
  have hscale := integral_rescale_mul (F := F) hr
  have hpoint :
      (fun u : ℝ =>
        genericProjectivePhysicalProfile
            (projectiveRescaleProfile G r) r u
          * Real.cos (delta*u))
        =
      fun u => (1/r) * F (r*u) := by
    funext u
    have hr0 := hr.ne'
    have hprof :
        genericProjectivePhysicalProfile
            (projectiveRescaleProfile G r) r u
          =
        (1/r) * genericProjectivePhysicalProfile G 1 (r*u) := by
      have h :=
        genericProjectivePhysicalProfile_rescale
          (G:=G) hr (r*u)
      have hru : (r*u)/r = u := by
        field_simp [hr0]
      simpa [hru] using h
    have hq :
        (delta/r)*(r*u) = delta*u := by
      field_simp [hr0]
    rw [hprof]
    dsimp [F]
    rw [hq]
  rw [hpoint, integral_const_mul, hscale]
  field_simp [hr.ne']
  ring

theorem quarticPhysicalBaseKernel_eq_ordinateTest
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (gamma : ℝ) :
    genericProjectiveBaseKernel
        (quarticPhysicalDetector W.R W.lam t)
        (t/16) (gamma-t)
      =
    quarticNegativeOrdinateTest W t gamma := by
  unfold quarticPhysicalDetector quarticNegativeOrdinateTest
    quarticNegativeWindowRadius
  rw [genericProjectiveBaseKernel_rescale
      (G := quarticThreeWindowProfile W.R W.lam)
      (r := t/16) (by positivity) (gamma-t)]
  ring

theorem quarticRvMMuSignedPair_eq_neg_quarter_ordinate_mu
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    projectiveRvMMuSignedPair
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      =
    -(1/4 : ℝ) *
      ∫ tau : ℝ,
        quarticNegativeOrdinateTest W t tau
          * Zeta23.mu tau := by
  rw [projectiveRvMMuSignedPair_eq_neg_quarter_base_mu_integral
      (quarticPhysicalDetector_contDiff W.Rpos).continuous
      (quarticPhysicalDetector_compact W.Rpos ht)
      (quarticPhysicalDetector_even W.R W.lam t)
      t (t/16)]
  apply congrArg (fun x : ℝ => -(1/4 : ℝ) * x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun tau => by
    rw [quarticPhysicalBaseKernel_eq_ordinateTest W ht tau]

theorem quarticBaseSourceTerm_eq_mult_mul_ordinateTest
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (sigma : Zeros) :
    quarticBaseSourceTerm W t sigma
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * quarticNegativeOrdinateTest W t (sigma : ℂ).im := by
  unfold quarticBaseSourceTerm quarticNegativeOrdinateTest
    quarticNegativeWindowRadius
  ring

/--
Exact infinite quartic N-mu discrepancy identity.
-/
theorem quarticBaseMuResidual_eq_half_full_N_minus_mu
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    quarticBaseMuResidual W t
      =
    (1/2 : ℝ) *
      ((∑' sigma : Zeros,
        ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
          * quarticNegativeOrdinateTest W t (sigma : ℂ).im)
        -
       ∫ tau : ℝ,
         quarticNegativeOrdinateTest W t tau
           * Zeta23.mu tau) := by
  unfold quarticBaseMuResidual
  rw [quarticRvMMuSignedPair_eq_neg_quarter_ordinate_mu W ht]
  have hsum :
      (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
        =
      ∑' sigma : Zeros,
        ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
          * quarticNegativeOrdinateTest W t (sigma : ℂ).im := by
    apply tsum_congr
    intro sigma
    exact quarticBaseSourceTerm_eq_mult_mul_ordinateTest W ht sigma
  rw [hsum]
  ring

end Synthesis
