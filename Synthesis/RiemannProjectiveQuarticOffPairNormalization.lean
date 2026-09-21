import Synthesis.RiemannProjectiveQuarticHighCutset
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Synthesis.RiemannProjectiveCircularHyperbolicDuality

/-!
# Exact normalized off-ordinate pair for the quartic detector

For any C² compact even taper g, one literal reflection-pair projective defect
is exactly

  m_rho * ∫ P_{g,r}(u) cosh(a_rho u) cos(delta_rho u) du,

where P_{g,r}=4 g B_r is the same physical projective profile whose circular
cosine transform is the q-only base kernel.

For a physical rescaling g_r(u)=G(r u), r>0,

  P_{g_r,r}(u) = r^{-1} P_{G,1}(r u),

and therefore

  D_pair(g_r;t,r,rho)
    = (m_rho/r²)
        ∫ P_{G,1}(x)
          cosh((a_rho/r)x)
          cos((delta_rho/r)x) dx.

Splitting cosh = 1 + (cosh-1) gives the exact normalized base/horizontal
decomposition for the new quartic detector.  No estimate enters.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def genericProjectiveHorizontalKernel
    (G : ℝ → ℝ) (alpha q : ℝ) : ℝ :=
  ∫ x : ℝ,
    genericProjectivePhysicalProfile G 1 x
      * (Real.cosh (alpha*x) - 1)
      * Real.cos (q*x)

def genericProjectivePairKernel
    (G : ℝ → ℝ) (alpha q : ℝ) : ℝ :=
  ∫ x : ℝ,
    genericProjectivePhysicalProfile G 1 x
      * Real.cosh (alpha*x)
      * Real.cos (q*x)

theorem genericProjectivePairKernel_eq_base_add_horizontal
    {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (alpha q : ℝ) :
    genericProjectivePairKernel G alpha q
      =
    genericProjectiveBaseKernel G 1 q
      + genericProjectiveHorizontalKernel G alpha q := by
  unfold genericProjectivePairKernel
    genericProjectiveBaseKernel
    genericProjectiveHorizontalKernel
    compactCosineTransform
  have hb : Integrable
      (fun x : ℝ =>
        genericProjectivePhysicalProfile G 1 x * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport
      ((genericProjectivePhysicalProfile_continuous hG 1).mul (by fun_prop))
      (genericProjectivePhysicalProfile_compact hGc 1).mul_right
  have hh : Integrable
      (fun x : ℝ =>
        genericProjectivePhysicalProfile G 1 x
          * (Real.cosh (alpha*x)-1) * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport
      (((genericProjectivePhysicalProfile_continuous hG 1).mul (by fun_prop)).mul
        (by fun_prop))
      ((genericProjectivePhysicalProfile_compact hGc 1).mul_right).mul_right
  rw [← integral_add hb hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/--
A generic literal reflection-pair projective defect is the projective physical
profile paired against cosh(horizontal height) and cos(ordinate gap).
-/
theorem literalPairProjectiveDefect_eq_projectiveProfileIntegral
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) (rho : Zeros) :
    literalPairProjectiveDefect g t r rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      *
    ∫ u : ℝ,
      genericProjectivePhysicalProfile g r u
        * Real.cosh (heightOf rho * u)
        * Real.cos (((rho : ℂ).im - t) * u) := by
  unfold literalPairProjectiveDefect
    literalPairRadiusChannel
    channelProjectiveDefect

  have h2 :=
    zeroConeValue_add_reflect_eq_integral
      hgs.continuous hgc heven t (2*r) rho
  have h1 :=
    zeroConeValue_add_reflect_eq_integral
      hgs.continuous hgc heven t r rho

  rw [h2, h1]
  let F : ℝ → ℝ := fun u =>
    reflectionPairWeight
      g (heightOf rho) ((rho : ℂ).im-t) u
  have hFc : Continuous F := by
    dsimp [F, reflectionPairWeight]
    fun_prop
  have hFk : HasCompactSupport F := by
    dsimp [F, reflectionPairWeight]
    exact ((hgc.mul_left.mul_right).mul_right)
  have hproj :=
    cosineChannelProjective
      hFc hFk g r
  have heq :
      (∫ u : ℝ, F u * Real.cos ((2*r)*u))
          * evenResp g 0 r
        -
      (∫ u : ℝ, F u * Real.cos (r*u))
          * evenResp g 0 (2*r)
        =
      ∫ u : ℝ,
        genericProjectivePhysicalProfile g r u
          * Real.cosh (heightOf rho*u)
          * Real.cos (((rho : ℂ).im-t)*u) := by
    rw [hproj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      unfold F reflectionPairWeight genericProjectivePhysicalProfile
      ring
  rw [heq]
  ring

theorem evenResp_rescale_zero
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (c : ℝ) :
    evenResp (projectiveRescaleProfile G r) 0 (c*r)
      =
    (1/r) * evenResp G 0 c := by
  exact evenResp_projectiveRescale hr c

theorem twoRadiusBracket_projectiveRescale
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (x : ℝ) :
    twoRadiusBracket
        (projectiveRescaleProfile G r) r (x/r)
      =
    (1/r) * twoRadiusBracket G 1 x := by
  have hr0 : r ≠ 0 := hr.ne'
  unfold twoRadiusBracket
  rw [show r = (1:ℝ)*r by ring,
      show 2*r = (2:ℝ)*r by ring,
      evenResp_rescale_zero hr 1,
      evenResp_rescale_zero hr 2]
  have h1 : r * (x/r) = x := by field_simp [hr0]
  have h2 : 2*r*(x/r) = 2*x := by field_simp [hr0]
  rw [h1,h2]
  ring

theorem genericProjectivePhysicalProfile_rescale
    {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (x : ℝ) :
    genericProjectivePhysicalProfile
        (projectiveRescaleProfile G r) r (x/r)
      =
    (1/r) * genericProjectivePhysicalProfile G 1 x := by
  unfold genericProjectivePhysicalProfile projectiveRescaleProfile
  have hr0 := hr.ne'
  have hx : r*(x/r)=x := by field_simp [hr0]
  rw [hx, twoRadiusBracket_projectiveRescale hr]
  ring

/--
Exact physical-to-normalized pair identity.
-/
theorem literalPairProjectiveDefect_rescale
    {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G)
    (hGeven : ∀ u, G (-u) = G u)
    {r : ℝ} (hr : 0 < r)
    (t : ℝ) (rho : Zeros) :
    literalPairProjectiveDefect
        (projectiveRescaleProfile G r) t r rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / r^2
      *
    genericProjectivePairKernel G
      (heightOf rho / r)
      (((rho : ℂ).im - t) / r) := by
  have hgr :
      ContDiff ℝ 2 (projectiveRescaleProfile G r) :=
    projectiveRescaleProfile_contDiff hG r
  have hgcr :
      HasCompactSupport (projectiveRescaleProfile G r) :=
    projectiveRescaleProfile_compact hGc hr.ne'
  have hger :
      ∀ u, projectiveRescaleProfile G r (-u)
        = projectiveRescaleProfile G r u :=
    projectiveRescaleProfile_even hGeven r

  rw [literalPairProjectiveDefect_eq_projectiveProfileIntegral
      hgr hgcr hger t r rho]
  unfold genericProjectivePairKernel

  let F : ℝ → ℝ := fun x =>
    genericProjectivePhysicalProfile G 1 x
      * Real.cosh ((heightOf rho/r)*x)
      * Real.cos ((((rho : ℂ).im-t)/r)*x)

  have hscale := integral_rescale_mul (F := F) hr

  have hpoint :
      (fun u : ℝ =>
        genericProjectivePhysicalProfile
            (projectiveRescaleProfile G r) r u
          * Real.cosh (heightOf rho*u)
          * Real.cos (((rho : ℂ).im-t)*u))
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
      have hru : (r*u)/r = u := by field_simp [hr0]
      simpa [hru] using h
    have ha : (heightOf rho/r)*(r*u)=heightOf rho*u := by
      field_simp [hr0]
    have hq :
        (((rho : ℂ).im-t)/r)*(r*u)
          = ((rho : ℂ).im-t)*u := by
      field_simp [hr0]
    rw [hprof]
    dsimp [F]
    rw [ha,hq]
    ring

  rw [hpoint, integral_const_mul, hscale]
  field_simp [hr.ne']
  ring

theorem literalPairProjectiveDefect_rescale_base_horizontal
    {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G)
    (hGeven : ∀ u, G (-u) = G u)
    {r : ℝ} (hr : 0 < r)
    (t : ℝ) (rho : Zeros) :
    literalPairProjectiveDefect
        (projectiveRescaleProfile G r) t r rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / r^2
      *
    (genericProjectiveBaseKernel G 1
        (((rho : ℂ).im-t)/r)
      +
     genericProjectiveHorizontalKernel G
        (heightOf rho/r)
        (((rho : ℂ).im-t)/r)) := by
  rw [literalPairProjectiveDefect_rescale
      hG hGc hGeven hr t rho]
  rw [genericProjectivePairKernel_eq_base_add_horizontal
      hG.continuous hGc]

end Synthesis
