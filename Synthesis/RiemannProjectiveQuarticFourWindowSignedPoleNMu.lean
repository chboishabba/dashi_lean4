import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleQuantitativeBand
import Synthesis.RiemannProjectiveQuarticNMuSameObject
import Synthesis.RiemannProjectiveRvMMuNamedGammaDefect
import Zeta23.ExplicitFormula.Bridge

/-!
# Exact signed four-window N-mu assembly

This is the missing same-object assembly lemma for the signed pole-cancelled
quartic route.

For each endpoint detector define the literal ordinate test

  phi(gamma) = r^-2 Phi((gamma-t)/r),  r=t/16,

where Phi is the normalized projective base kernel of the corresponding smooth
four-window profile.  Then

  Off + Gamma
    = 1/2 * (sum m_rho phi(Im rho) - integral phi mu)
      + H,

where H is exactly the off-ordinate horizontal source tsum.

The signed endpoint combination therefore satisfies

  P2 (Off_1 + Gamma_1) - P1 (Off_2 + Gamma_2)
    = 1/2 * <N-mu, Psi_t> + H_comb,

with

  Psi_t = P2 * phi_1 - P1 * phi_2.

The global signed N-mu scalar below is intentionally stored in endpoint-linear
normal form.  That avoids inserting an unnecessary theorem about exchanging
two already-convergent infinite representations merely to change syntax; the
pointwise test `signedOrdinateTest` is exposed explicitly for the analytic
consumer.

No estimate of the N-mu discrepancy or horizontal term is proved here.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.NearFarCarrierSplit

def quarticFourOrdinateTest
    (R lam mu t gamma : ℝ) : ℝ :=
  let r := t/16
  (1/r^2) *
    genericProjectiveBaseKernel
      (quarticFourWindowProfile R lam mu) 1
      ((gamma-t)/r)

def quarticFourBaseSourceTerm
    (R lam mu t : ℝ) (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * quarticFourOrdinateTest R lam mu t (sigma : ℂ).im

def quarticFourHorizontalSourceTerm
    (R lam mu t : ℝ) (sigma : Zeros) : ℝ :=
  literalPairProjectiveDefect
      (quarticFourPhysicalDetector R lam mu t)
      t (t/16) sigma
    - quarticFourBaseSourceTerm R lam mu t sigma

theorem quarticFourBaseSourceTerm_eq_normalizedKernel
    {R lam mu t : ℝ}
    (sigma : Zeros) :
    quarticFourBaseSourceTerm R lam mu t sigma
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
      *
    genericProjectiveBaseKernel
      (quarticFourWindowProfile R lam mu) 1
      (((sigma : ℂ).im-t)/(t/16)) := by
  unfold quarticFourBaseSourceTerm quarticFourOrdinateTest
  ring

theorem quarticFourBaseSourceTerm_eq_zero_of_sameOrd
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    {sigma : Zeros}
    (him : (sigma : ℂ).im = t) :
    quarticFourBaseSourceTerm R lam mu t sigma = 0 := by
  rw [quarticFourBaseSourceTerm_eq_normalizedKernel]
  have hr : t/16 ≠ 0 := by positivity
  have hq : (((sigma : ℂ).im-t)/(t/16)) = 0 := by
    rw [him]
    simp
  rw [hq,
    genericProjectiveBaseKernel_zero
      (quarticFourWindowProfile_continuous
        (lam:=lam) (mu:=mu) hR)
      (quarticFourWindowProfile_compact
        (lam:=lam) (mu:=mu) hR)
      1]
  ring

theorem quarticFourBaseSourceTerm_abs_le_tailTerm_of_far
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    (sigma : Zeros)
    (hfar : 1 <= |(sigma : ℂ).im-t|) :
    |quarticFourBaseSourceTerm R lam mu t sigma|
      <=
    genericProjectiveBaseCurvature
        (quarticFourWindowProfile R lam mu)
      * tailTerm t sigma := by
  let G := quarticFourWindowProfile R lam mu
  let r := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdelta : (sigma : ℂ).im-t ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hfar
    linarith
  have hq : (((sigma : ℂ).im-t)/r) ≠ 0 :=
    div_ne_zero hdelta hr.ne'
  have hdec :=
    genericProjectiveBaseKernel_abs_le_invSq
      (G:=G)
      (quarticFourWindowProfile_contDiff
        (lam:=lam) (mu:=mu) hR)
      (quarticFourWindowProfile_compact
        (lam:=lam) (mu:=mu) hR)
      hq
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hC :
      0 <= genericProjectiveBaseCurvature G :=
    genericProjectiveBaseCurvature_nonneg G
  rw [quarticFourBaseSourceTerm_eq_normalizedKernel]
  dsimp [G, r] at hdec ⊢
  rw [abs_mul,
      abs_of_nonneg (div_nonneg hm (sq_nonneg (t/16)))]
  have hscaled :
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
          *
        (genericProjectiveBaseCurvature G
          / (((sigma : ℂ).im-t)/(t/16))^2)
        =
      genericProjectiveBaseCurvature G
        * (((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
          / ((sigma : ℂ).im-t)^2) := by
    field_simp [hdelta, (by linarith : t ≠ 0)]
    ring
  have hmul :=
    mul_le_mul_of_nonneg_left hdec
      (div_nonneg hm (sq_nonneg (t/16)))
  rw [hscaled] at hmul
  unfold tailTerm
  rw [if_pos hfar]
  exact hmul

theorem quarticFourBaseSourceTerm_summable_full
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Summable (quarticFourBaseSourceTerm R lam mu t) := by
  classical
  let C :=
    genericProjectiveBaseCurvature
      (quarticFourWindowProfile R lam mu)
  have hmajor : Summable (fun sigma : Zeros => C * tailTerm t sigma) :=
    (summable_tailTerm t).mul_left C
  let S : Set Zeros := nearSet t 1
  have hSfin : S.Finite := nearSet_finite t 1
  have hev :
      ∀ᶠ sigma : Zeros in Filter.cofinite,
        ‖quarticFourBaseSourceTerm R lam mu t sigma‖
          <= C * tailTerm t sigma := by
    filter_upwards [hSfin.compl_mem_cofinite] with sigma hsigma
    have hfar : 1 <= |(sigma : ℂ).im-t| := by
      by_contra hlt
      apply hsigma
      exact not_le.1 hlt
    rw [Real.norm_eq_abs]
    exact quarticFourBaseSourceTerm_abs_le_tailTerm_of_far
      hR ht sigma hfar
  exact Summable.of_norm_bounded_eventually hmajor hev

theorem quarticFourBaseSourceTerm_summable_offOrd
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      quarticFourBaseSourceTerm R lam mu t (sigma : Zeros) :=
  (quarticFourBaseSourceTerm_summable_full hR ht).subtype _

theorem quarticFourPairDefect_summable_offOrd
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      literalPairProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16) (sigma : Zeros) := by
  exact literalPairProjectiveDefect_summable_offOrd
    (quarticFourPhysicalDetector_contDiff
      (lam:=lam) (mu:=mu) (t:=t) hR)
    (quarticFourPhysicalDetector_compact
      (lam:=lam) (mu:=mu) hR ht)
    (quarticFourPhysicalDetector_even R lam mu t)
    t (t/16)

theorem quarticFourHorizontalSourceTerm_summable_offOrd
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      quarticFourHorizontalSourceTerm
        R lam mu t (sigma : Zeros) := by
  exact
    (quarticFourPairDefect_summable_offOrd hR ht).sub
      (quarticFourBaseSourceTerm_summable_offOrd hR ht)

theorem quarticFourPairDefect_eq_base_add_horizontal
    (R lam mu t : ℝ) (sigma : Zeros) :
    literalPairProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16) sigma
      =
    quarticFourBaseSourceTerm R lam mu t sigma
      + quarticFourHorizontalSourceTerm R lam mu t sigma := by
  unfold quarticFourHorizontalSourceTerm
  ring

theorem quarticFour_offOrdProjectiveDefect_eq_base_add_horizontal
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    offOrdProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16)
      =
    (1/2 : ℝ) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        quarticFourBaseSourceTerm
          R lam mu t (sigma : Zeros))
      +
    (1/2 : ℝ) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        quarticFourHorizontalSourceTerm
          R lam mu t (sigma : Zeros)) := by
  rw [offOrdProjectiveDefect_eq_half_literalPair_tsum
      (quarticFourPhysicalDetector_contDiff
        (lam:=lam) (mu:=mu) (t:=t) hR)
      (quarticFourPhysicalDetector_compact
        (lam:=lam) (mu:=mu) hR ht)
      (quarticFourPhysicalDetector_even R lam mu t)
      t (t/16)]
  have hb := quarticFourBaseSourceTerm_summable_offOrd hR ht
  have hh := quarticFourHorizontalSourceTerm_summable_offOrd hR ht
  rw [show
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        literalPairProjectiveDefect
          (quarticFourPhysicalDetector R lam mu t)
          t (t/16) (sigma : Zeros))
        =
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        quarticFourBaseSourceTerm
          R lam mu t (sigma : Zeros)
          + quarticFourHorizontalSourceTerm
              R lam mu t (sigma : Zeros)) by
        apply tsum_congr
        intro sigma
        exact quarticFourPairDefect_eq_base_add_horizontal
          R lam mu t (sigma : Zeros)]
  rw [hb.tsum_add hh]
  ring

theorem tsum_full_quarticFourBase_eq_offOrd
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    (∑' sigma : Zeros,
      quarticFourBaseSourceTerm R lam mu t sigma)
      =
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      quarticFourBaseSourceTerm
        R lam mu t (sigma : Zeros)) := by
  have hfull := quarticFourBaseSourceTerm_summable_full hR ht
  have hsame := hfull.subtype (SameOrd t)
  have hoff := hfull.subtype ((SameOrd t)ᶜ)
  have hsame0 :
      (∑' sigma : SameOrd t,
        quarticFourBaseSourceTerm
          R lam mu t (sigma : Zeros)) = 0 := by
    apply tsum_eq_zero
    intro sigma
    exact quarticFourBaseSourceTerm_eq_zero_of_sameOrd
      hR ht sigma.property
  have hsplit := (Summable.tsum_add_tsum_compl hsame hoff).symm
  rw [hsame0, zero_add] at hsplit
  exact hsplit

theorem quarticFourPhysicalBaseKernel_eq_ordinateTest
    {R lam mu t : ℝ}
    (ht : 0 < t)
    (gamma : ℝ) :
    genericProjectiveBaseKernel
        (quarticFourPhysicalDetector R lam mu t)
        (t/16) (gamma-t)
      =
    quarticFourOrdinateTest R lam mu t gamma := by
  unfold quarticFourPhysicalDetector quarticFourOrdinateTest
  rw [genericProjectiveBaseKernel_rescale
      (G:=quarticFourWindowProfile R lam mu)
      (r:=t/16) (by positivity) (gamma-t)]

theorem quarticFourRvMMuSignedPair_eq_neg_quarter_ordinate_mu
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    projectiveRvMMuSignedPair
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16)
      =
    -(1/4 : ℝ) *
      ∫ tau : ℝ,
        quarticFourOrdinateTest R lam mu t tau
          * Zeta23.mu tau := by
  rw [projectiveRvMMuSignedPair_eq_neg_quarter_base_mu_integral
      (quarticFourPhysicalDetector_contDiff
        (lam:=lam) (mu:=mu) (t:=t) hR).continuous
      (quarticFourPhysicalDetector_compact
        (lam:=lam) (mu:=mu) hR ht)
      (quarticFourPhysicalDetector_even R lam mu t)
      t (t/16)]
  apply congrArg (fun x : ℝ => -(1/4 : ℝ) * x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun tau => by
    rw [quarticFourPhysicalBaseKernel_eq_ordinateTest ht tau]

def quarticFourFullNMinusMu
    (R lam mu t : ℝ) : ℝ :=
  (∑' sigma : Zeros,
    quarticFourBaseSourceTerm R lam mu t sigma)
    -
  ∫ tau : ℝ,
    quarticFourOrdinateTest R lam mu t tau
      * Zeta23.mu tau

def quarticFourHorizontalRemainder
    (R lam mu t : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      quarticFourHorizontalSourceTerm
        R lam mu t (sigma : Zeros))

def quarticFourCompletedRadius (t : ℝ) : ℝ :=
  16 * (Real.pi + 1) / t

theorem quarticFourCompletedRadius_pos
    {t : ℝ} (ht : 0 < t) :
    0 < quarticFourCompletedRadius t := by
  unfold quarticFourCompletedRadius
  positivity

theorem quarticFourPhysicalDetector_support_completedRadius
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 0 < t) :
    ∀ u,
      quarticFourPhysicalDetector R lam mu t u ≠ 0 ->
      |u| <= quarticFourCompletedRadius t := by
  intro u hu
  exact
    (quarticFourPhysicalDetector_support_abs_lt
      hR hRone ht hu).le

/--
One endpoint identity:
  Off + Gamma = 1/2 <N-mu,phi> + horizontal.
-/
theorem quarticFour_external_eq_half_NMu_add_horizontal
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 0 < t) :
    offOrdProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16)
      +
    gammaProjectiveDefect
        (quarticFourPhysicalDetector R lam mu t)
        t (t/16)
      =
    (1/2 : ℝ) * quarticFourFullNMinusMu R lam mu t
      + quarticFourHorizontalRemainder R lam mu t := by
  rw [quarticFour_offOrdProjectiveDefect_eq_base_add_horizontal
      hR ht]
  rw [← tsum_full_quarticFourBase_eq_offOrd hR ht]
  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
      (quarticFourPhysicalDetector_contDiff
        (lam:=lam) (mu:=mu) (t:=t) hR)
      (quarticFourPhysicalDetector_even R lam mu t)
      (quarticFourPhysicalDetector_support_completedRadius
        hR hRone ht)
      (quarticFourCompletedRadius_pos ht).le
      t (t/16)]
  rw [quarticFourRvMMuSignedPair_eq_neg_quarter_ordinate_mu
      hR ht]
  unfold quarticFourFullNMinusMu quarticFourHorizontalRemainder
  ring

def QuarticFourSignedPolePair.ordinateTestHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  quarticFourOrdinateTest W.R (1/2) W.muHalf t

def QuarticFourSignedPolePair.ordinateTestTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  quarticFourOrdinateTest W.R (2/3) W.muTwo t

/-- The exact signed test Psi_t seen by the remaining discrepancy theorem. -/
def QuarticFourSignedPolePair.signedOrdinateTest
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  fun tau =>
    W.poleTwo * W.ordinateTestHalf tau
      + (-W.poleHalf) * W.ordinateTestTwo tau

/--
The literal signed N-mu functional, retained in endpoint-linearized normal form.
The exposed pointwise test is `W.signedOrdinateTest`.
-/
def QuarticFourSignedPolePair.signedNMuPair
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo *
      quarticFourFullNMinusMu W.R (1/2) W.muHalf t
    +
  (-W.poleHalf) *
      quarticFourFullNMinusMu W.R (2/3) W.muTwo t

def QuarticFourSignedPolePair.signedHorizontalRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo *
      quarticFourHorizontalRemainder W.R (1/2) W.muHalf t
    +
  (-W.poleHalf) *
      quarticFourHorizontalRemainder W.R (2/3) W.muTwo t

/--
The literal four-window ordinate test is globally integrable against the exact
RvM density mu.

This is not a new tail estimate.  It is transported from
`Zeta23.EF.integrable_paperFT_mul_mu` through the exact projective
paperFT/base-kernel normalization and the physical rescaling theorem.
-/
theorem quarticFourOrdinateTest_mul_mu_integrable
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Integrable
      (fun tau : ℝ =>
        quarticFourOrdinateTest R lam mu t tau
          * Zeta23.mu tau) := by
  let g : ℝ -> ℝ :=
    quarticFourPhysicalDetector R lam mu t
  let k : ℝ -> ℂ :=
    literalProjectiveSampleTest g t (t/16)
  have hg2 : ContDiff ℝ 2 g := by
    dsimp [g]
    exact quarticFourPhysicalDetector_contDiff
      (lam:=lam) (mu:=mu) (t:=t) hR
  have hgc : HasCompactSupport g := by
    dsimp [g]
    exact quarticFourPhysicalDetector_compact
      (lam:=lam) (mu:=mu) hR ht
  have hk2 : ContDiff ℝ 2 k := by
    dsimp [k]
    exact sampleTest_contDiff hg2 t (t/16)
  have hkc : HasCompactSupport k := by
    dsimp [k]
    exact sampleTest_hasCompactSupport hgc t (t/16)
  have hiComplex :
      Integrable
        (fun tau : ℝ =>
          paperFT k tau * (Zeta23.mu tau : ℂ)) :=
    Zeta23.EF.integrable_paperFT_mul_mu
      hk2 hkc Zeta23.gammaFacts
  have hiReal :
      Integrable
        (fun tau : ℝ =>
          (1/4 : ℝ)
            * quarticFourOrdinateTest R lam mu t tau
            * Zeta23.mu tau) := by
    have hre := hiComplex.re
    have hfun :
        (fun tau : ℝ =>
          (paperFT k tau * (Zeta23.mu tau : ℂ)).re)
          =
        fun tau : ℝ =>
          (1/4 : ℝ)
            * quarticFourOrdinateTest R lam mu t tau
            * Zeta23.mu tau := by
      funext tau
      have hpaper :=
        paperFT_literalProjectiveSampleTest_eq_quarter_baseKernel
          hg2.continuous hgc
          (quarticFourPhysicalDetector_even R lam mu t)
          t (t/16) tau
      dsimp [k, g] at hpaper
      rw [hpaper,
        quarticFourPhysicalBaseKernel_eq_ordinateTest
          (R:=R) (lam:=lam) (mu:=mu) ht tau]
      simp
      ring
    rw [hfun] at hre
    exact hre
  have hscaled := hiReal.const_mul (4 : ℝ)
  simpa only [mul_assoc] using hscaled

/--
Both endpoint tests carried by a signed-pole witness are globally mu-integrable.
-/
theorem QuarticFourSignedPolePair.endpointMuIntegrable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun tau : ℝ =>
        quarticFourOrdinateTest W.R (1/2) W.muHalf t tau
          * Zeta23.mu tau)
    ∧
    Integrable
      (fun tau : ℝ =>
        quarticFourOrdinateTest W.R (2/3) W.muTwo t tau
          * Zeta23.mu tau) := by
  exact ⟨
    quarticFourOrdinateTest_mul_mu_integrable W.Rpos ht,
    quarticFourOrdinateTest_mul_mu_integrable W.Rpos ht
  ⟩

/--
Exact pointwise normal form for the global signed N-mu scalar.

The two endpoint mu-integrability facts are explicit hypotheses here.  They are
part of the remaining global-exhaustion assembly seam and must be discharged
from tail decay, not inferred from local derivative regularity.
-/
theorem QuarticFourSignedPolePair.signedNMuPair_eq_pointwise
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hiHalf :
      Integrable
        (fun tau : ℝ =>
          quarticFourOrdinateTest W.R (1/2) W.muHalf t tau
            * Zeta23.mu tau))
    (hiTwo :
      Integrable
        (fun tau : ℝ =>
          quarticFourOrdinateTest W.R (2/3) W.muTwo t tau
            * Zeta23.mu tau)) :
    W.signedNMuPair
      =
    (∑' sigma : Zeros,
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * W.signedOrdinateTest (sigma : ℂ).im)
      -
    ∫ tau : ℝ,
      W.signedOrdinateTest tau * Zeta23.mu tau := by
  have hs1 :=
    quarticFourBaseSourceTerm_summable_full
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf)
      W.Rpos ht
  have hs2 :=
    quarticFourBaseSourceTerm_summable_full
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo)
      W.Rpos ht
  have htsum :
      (∑' sigma : Zeros,
        ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
          * W.signedOrdinateTest (sigma : ℂ).im)
        =
      W.poleTwo *
        (∑' sigma : Zeros,
          quarticFourBaseSourceTerm
            W.R (1/2) W.muHalf t sigma)
        +
      (-W.poleHalf) *
        (∑' sigma : Zeros,
          quarticFourBaseSourceTerm
            W.R (2/3) W.muTwo t sigma) := by
    have hpoint :
        (fun sigma : Zeros =>
          ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
            * W.signedOrdinateTest (sigma : ℂ).im)
        =
        fun sigma =>
          W.poleTwo *
            quarticFourBaseSourceTerm
              W.R (1/2) W.muHalf t sigma
          +
          (-W.poleHalf) *
            quarticFourBaseSourceTerm
              W.R (2/3) W.muTwo t sigma := by
      funext sigma
      unfold QuarticFourSignedPolePair.signedOrdinateTest
        QuarticFourSignedPolePair.ordinateTestHalf
        QuarticFourSignedPolePair.ordinateTestTwo
        quarticFourBaseSourceTerm
      ring
    rw [hpoint, (hs1.mul_left W.poleTwo).tsum_add
      (hs2.mul_left (-W.poleHalf))]
    rw [tsum_mul_left, tsum_mul_left]
  have hint :
      (∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau)
        =
      W.poleTwo *
        (∫ tau : ℝ,
          quarticFourOrdinateTest W.R (1/2) W.muHalf t tau
            * Zeta23.mu tau)
        +
      (-W.poleHalf) *
        (∫ tau : ℝ,
          quarticFourOrdinateTest W.R (2/3) W.muTwo t tau
            * Zeta23.mu tau) := by
    unfold QuarticFourSignedPolePair.signedOrdinateTest
      QuarticFourSignedPolePair.ordinateTestHalf
      QuarticFourSignedPolePair.ordinateTestTwo
    have hpoint :
        (fun tau : ℝ =>
          (W.poleTwo *
              quarticFourOrdinateTest W.R (1/2) W.muHalf t tau
            +
            (-W.poleHalf) *
              quarticFourOrdinateTest W.R (2/3) W.muTwo t tau)
            * Zeta23.mu tau)
        =
        fun tau =>
          W.poleTwo *
            (quarticFourOrdinateTest W.R (1/2) W.muHalf t tau
              * Zeta23.mu tau)
          +
          (-W.poleHalf) *
            (quarticFourOrdinateTest W.R (2/3) W.muTwo t tau
              * Zeta23.mu tau) := by
      funext tau
      ring
    rw [hpoint,
      integral_add (hiHalf.const_mul _) (hiTwo.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold QuarticFourSignedPolePair.signedNMuPair
    quarticFourFullNMinusMu
  rw [htsum, hint]
  ring


/--
The actual combined signed test is globally integrable against mu.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_mul_mu_integrable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun tau : ℝ =>
        W.signedOrdinateTest tau * Zeta23.mu tau) := by
  obtain ⟨hiHalf, hiTwo⟩ := W.endpointMuIntegrable ht
  unfold QuarticFourSignedPolePair.signedOrdinateTest
    QuarticFourSignedPolePair.ordinateTestHalf
    QuarticFourSignedPolePair.ordinateTestTwo
  have h1 := hiHalf.const_mul W.poleTwo
  have h2 := hiTwo.const_mul (-W.poleHalf)
  have hadd := h1.add h2
  simpa only [mul_add, add_mul, neg_mul, mul_assoc] using hadd

/--
Hypothesis-free same-object weld for the actual combined Psi test.

The endpoint full-line mu-integrability obligations are discharged by the
Zeta23 explicit-formula bridge.
-/
theorem QuarticFourSignedPolePair.signedNMuPair_eq_pointwise_closed
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedNMuPair
      =
    (∑' sigma : Zeros,
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * W.signedOrdinateTest (sigma : ℂ).im)
      -
    ∫ tau : ℝ,
      W.signedOrdinateTest tau * Zeta23.mu tau := by
  obtain ⟨hiHalf, hiTwo⟩ := W.endpointMuIntegrable ht
  exact W.signedNMuPair_eq_pointwise ht hiHalf hiTwo


/--
The handoff's missing G2 assembly lemma.

The exact signed external scalar is one half of the literal signed N-mu
functional plus the signed horizontal remainder.  No pole term remains.
-/
theorem quarticFourSignedPole_external_eq_NMu_add_horizontal
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.poleTwo *
      (offOrdProjectiveDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          t (t/16)
        +
       gammaProjectiveDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          t (t/16))
      +
    (-W.poleHalf) *
      (offOrdProjectiveDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          t (t/16)
        +
       gammaProjectiveDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          t (t/16))
      =
    (1/2 : ℝ) * W.signedNMuPair
      + W.signedHorizontalRemainder := by
  have htpos : 0 < t := by linarith
  rw [quarticFour_external_eq_half_NMu_add_horizontal
      W.Rpos W.RltOne htpos,
      quarticFour_external_eq_half_NMu_add_horizontal
      W.Rpos W.RltOne htpos]
  unfold QuarticFourSignedPolePair.signedNMuPair
    QuarticFourSignedPolePair.signedHorizontalRemainder
  ring

/--
Terminal compiler after G2: the remaining theorem is exactly the strict bound
on signed N-mu plus signed horizontal remainder.
-/
theorem false_of_quarticFourSignedPole_NMu_horizontal_strict
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      (1/2 : ℝ) * W.signedNMuPair
        + W.signedHorizontalRemainder
      <
      2 * W.combinedZeroHeightDefect rho) :
    False := by
  apply false_of_quarticFourSignedPole_external_strict_quantitative
    ht W hhigh him hoff
  rw [quarticFourSignedPole_external_eq_NMu_add_horizontal ht W]
  exact hstrict


/--
The single completed scalar consumed by the Clay-facing G3 theorem.
-/
def QuarticFourSignedPolePair.completedSignedResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (1/2 : ℝ) * W.signedNMuPair
    + W.signedHorizontalRemainder

/--
Exact compiler identity: the completed G3 residual is the already-defined
combined cluster.  Therefore any strict G3 bound is genuinely new information,
not a consequence of further explicit-formula rearrangement.
-/
theorem QuarticFourSignedPolePair.completedSignedResidual_eq_combinedCluster
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.completedSignedResidual = W.combinedCluster := by
  unfold QuarticFourSignedPolePair.completedSignedResidual
  rw [W.combinedCluster_eq_offGamma ht]
  symm
  exact quarticFourSignedPole_external_eq_NMu_add_horizontal ht W

/--
Equivalent Clay-facing terminal theorem stated directly on the completed
residual object.
-/
theorem false_of_quarticFourSignedPole_completedResidual_strict
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      W.completedSignedResidual
        < 2 * W.combinedZeroHeightDefect rho) :
    False := by
  exact false_of_quarticFourSignedPole_NMu_horizontal_strict
    ht W hhigh him hoff hstrict

end Synthesis
