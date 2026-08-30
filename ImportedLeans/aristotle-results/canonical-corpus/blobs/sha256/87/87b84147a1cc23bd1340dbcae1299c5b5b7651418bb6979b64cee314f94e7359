/-
# The off-ordinate zero tail at determinant level

The old envelope `epsZero` bounded the off-ordinate channel *at each radius
separately*,

    |Z_off(s)| ≤ ∑_{Im σ ≠ t} |response_σ(s)|,

and then inserted the two bounds `s = r`, `s = 2r` into the triangle inequality.
The determinant

    𝔇_{Z_off}(r) = Z_off(2r) A_0(r) - Z_off(r) A_0(2r)

is thereby estimated by a quantity of size `O(1)`.

This module estimates it at determinant level instead.  Three steps.

1. **Each zero's two-sample cone response is a cosine transform** in the sampling
   radius: for a zero of height `a` and ordinate gap `δ`,

       C_σ(s) = ∫ g(u) · 2( cosh(au) cos(δu) + sinh(au) sin(δu) ) · cos(su) du
                                                                (`coneResp_eq_integral`).

2. **Per-zero transport.**  Hence its two-radius determinant is the *same* response
   read at sampling radius `0` with the taper replaced by the projective taper
   `h_r = g B_r`, and therefore

       d_σ(r) = C_σ(2r) A_0(r) - C_σ(r) A_0(2r) = 2 · reim(zeroTerm (sampleTest h_r t 0) σ)
                                                        (`singleOffOrdProjectiveDefect_eq`).

   The whole two-radius cancellation is carried by the single bracket `B_r`, which
   is `O(r²)`; nothing is discarded.

3. **Summation.**  The determinant commutes with the (absolutely convergent) zero
   sum, so

       𝔇_{Z_off}(r) = ∑_{Im σ ≠ t} d_σ(r) = 2 · reim(offOrdTerm (sampleTest h_r t 0) t)
                                                        (`offOrdProjectiveDefect_eq_tsum`),

   and the companion's own machinery — `[eq:hfbound]` for the test function,
   `zero_sum_inv_sq` for the zero side — gives the envelope

       |𝔇_{Z_off}(r)| ≤ 4 · stripConst (sampleTest h_r t 0) Λ · W(t)
                                                        (`offOrdProjectiveTailEnvelope`).

The quadratic gain is now entirely located in the strip constant of the projective
taper, which is bounded by `r²` times an explicit constant in
`LiteralWeilProjectiveStripConstant`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilProjectiveTaper

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOffOrdinateProjectiveTail

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper

/-! ## A single zero's two-sample cone response is a cosine transform -/

/-- The fixed weight through which a zero of height `a` and ordinate gap `δ` reads
the taper. -/
def zeroChannelWeight (g : ℝ → ℝ) (a δ : ℝ) : ℝ → ℝ := fun u =>
  g u * (2 * (Real.cosh (a * u) * Real.cos (δ * u) + Real.sinh (a * u) * Real.sin (δ * u)))

theorem zeroChannelWeight_continuous {g : ℝ → ℝ} (hg : Continuous g) (a δ : ℝ) :
    Continuous (zeroChannelWeight g a δ) := by
  unfold zeroChannelWeight; fun_prop

theorem zeroChannelWeight_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) (a δ : ℝ) :
    HasCompactSupport (zeroChannelWeight g a δ) :=
  hgc.mul_right

/-- The two-sample (`±s`) cone response of a single zero. -/
def coneResp (g : ℝ → ℝ) (a δ s : ℝ) : ℝ := zeroResp g a δ s + zeroResp g a δ (-s)

/-- **`coneResp_eq_integral`.**  The cone response is the cosine transform, in the
sampling radius, of a weight that does not depend on the radius. -/
theorem coneResp_eq_integral {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a δ s : ℝ) :
    coneResp g a δ s = ∫ u : ℝ, zeroChannelWeight g a δ u * Real.cos (s * u) := by
  have hie : ∀ x : ℝ, Integrable (fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos (x * u))) :=
    fun x => Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have hio : ∀ x : ℝ, Integrable (fun u : ℝ => g u * (Real.sinh (a * u) * Real.sin (x * u))) :=
    fun x => Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have hsplit : (∫ u : ℝ, zeroChannelWeight g a δ u * Real.cos (s * u))
      = ∫ u : ℝ, ((g u * (Real.cosh (a * u) * Real.cos ((s + δ) * u))
            + g u * (Real.sinh (a * u) * Real.sin ((s + δ) * u)))
          + (g u * (Real.cosh (a * u) * Real.cos ((-s + δ) * u))
            + g u * (Real.sinh (a * u) * Real.sin ((-s + δ) * u)))) := by
    congr 1
    funext u
    unfold zeroChannelWeight
    rw [show (s + δ) * u = s * u + δ * u by ring, show (-s + δ) * u = δ * u - s * u by ring,
      Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub]
    ring
  have hAB : Integrable (fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos ((s + δ) * u))
      + g u * (Real.sinh (a * u) * Real.sin ((s + δ) * u))) := (hie (s + δ)).add (hio (s + δ))
  have hCD : Integrable (fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos ((-s + δ) * u))
      + g u * (Real.sinh (a * u) * Real.sin ((-s + δ) * u))) := (hie (-s + δ)).add (hio (-s + δ))
  unfold coneResp zeroResp evenResp oddResp
  rw [hsplit, integral_add hAB hCD,
    integral_add (hie (s + δ)) (hio (s + δ)), integral_add (hie (-s + δ)) (hio (-s + δ))]

/-- **Per-zero transport.**  The two-radius determinant of a single zero's cone
response is that response read at sampling radius `0`, for the projective taper. -/
theorem coneResp_projective {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a δ r : ℝ) :
    coneResp g a δ (2 * r) * evenResp g 0 r - coneResp g a δ r * evenResp g 0 (2 * r)
      = coneResp (projTaper g r) a δ 0 := by
  have hFc : Continuous (zeroChannelWeight g a δ) := zeroChannelWeight_continuous hg a δ
  have hFk : HasCompactSupport (zeroChannelWeight g a δ) :=
    zeroChannelWeight_hasCompactSupport hgc a δ
  rw [coneResp_eq_integral hg hgc a δ (2 * r), coneResp_eq_integral hg hgc a δ r,
    cosineChannelProjective hFc hFk g r,
    coneResp_eq_integral (projTaper_continuous hg r) (projTaper_hasCompactSupport hgc r) a δ 0]
  congr 1
  funext u
  unfold zeroChannelWeight projTaper
  simp
  ring

/-! ## The cone value of a single zero, and its projective defect -/

/-- The two-sample cone value of a single zero at sampling radius `s`. -/
def zeroConeValue (g : ℝ → ℝ) (t s : ℝ) (ρ : Zeros) : ℝ :=
  reim (zeroTerm (sampleTest g t s) ρ) + reim (zeroTerm (sampleTest g t (-s)) ρ)

theorem zeroConeValue_eq_coneResp {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) (ρ : Zeros) :
    zeroConeValue g t s ρ
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * coneResp g (heightOf ρ) ((ρ : ℂ).im - t) s := by
  have hre : (ρ : ℂ).re = 1 / 2 + heightOf ρ := by unfold heightOf; ring
  unfold zeroConeValue coneResp
  rw [reim_zeroTerm_sampleTest hg hgc heven hre rfl t s,
    reim_zeroTerm_sampleTest hg hgc heven hre rfl t (-s)]
  ring

/-- **`singleOffOrdProjectiveDefect_eq`.**  The projective defect of a single zero
is that zero's response to the projective taper, at sampling radius `0`. -/
theorem singleOffOrdProjectiveDefect_eq {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) (ρ : Zeros) :
    zeroConeValue g t (2 * r) ρ * evenResp g 0 r - zeroConeValue g t r ρ * evenResp g 0 (2 * r)
      = 2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) ρ) := by
  have hpc : Continuous (projTaper g r) := projTaper_continuous hg r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hpe : ∀ u, projTaper g r (-u) = projTaper g r u := projTaper_even heven r
  have h0 : zeroConeValue (projTaper g r) t 0 ρ
      = 2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) ρ) := by
    unfold zeroConeValue
    rw [neg_zero]
    ring
  rw [zeroConeValue_eq_coneResp hg hgc heven t (2 * r) ρ,
    zeroConeValue_eq_coneResp hg hgc heven t r ρ]
  rw [show ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
        * coneResp g (heightOf ρ) ((ρ : ℂ).im - t) (2 * r) * evenResp g 0 r
      - ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
        * coneResp g (heightOf ρ) ((ρ : ℂ).im - t) r * evenResp g 0 (2 * r)
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
        * (coneResp g (heightOf ρ) ((ρ : ℂ).im - t) (2 * r) * evenResp g 0 r
          - coneResp g (heightOf ρ) ((ρ : ℂ).im - t) r * evenResp g 0 (2 * r)) by ring,
    coneResp_projective hg hgc (heightOf ρ) ((ρ : ℂ).im - t) r,
    ← zeroConeValue_eq_coneResp hpc hpk hpe t 0 ρ, h0]

/-! ## The off-ordinate channel as a zero sum -/

theorem offOrdChannel_eq_tsum {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t s : ℝ) :
    offOrdChannel g t s = ∑' σ : ((SameOrd t)ᶜ : Set Zeros), zeroConeValue g t s (σ : Zeros) := by
  have hs1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest g t s) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hgs t s) (sampleTest_hasCompactSupport hgc t s)).subtype _
  have hs2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest g t (-s)) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hgs t (-s))
      (sampleTest_hasCompactSupport hgc t (-s))).subtype _
  have hr1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      reim (zeroTerm (sampleTest g t s) (σ : Zeros)) := by
    have hre := (Complex.hasSum_re hs1.hasSum).summable
    have him := (Complex.hasSum_im hs1.hasSum).summable
    exact hre.add him
  have hr2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      reim (zeroTerm (sampleTest g t (-s)) (σ : Zeros)) := by
    have hre := (Complex.hasSum_re hs2.hasSum).summable
    have him := (Complex.hasSum_im hs2.hasSum).summable
    exact hre.add him
  have hval : offOrdChannel g t s
      = reim (offOrdTerm (sampleTest g t s) t) + reim (offOrdTerm (sampleTest g t (-s)) t) := rfl
  rw [hval, offOrdTerm, offOrdTerm, reim_tsum hs1, reim_tsum hs2, ← hr1.tsum_add hr2]
  rfl

/-! ## The projective defect of the whole off-ordinate tail -/

/-- **`offOrdProjectiveDefect_eq_tsum`.**  The determinant commutes with the zero
sum: the off-ordinate projective defect is the sum of the per-zero projective
defects, each of which already carries the two-radius cancellation. -/
theorem offOrdProjectiveDefect_eq_tsum {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    offOrdProjectiveDefect g t r
      = ∑' σ : ((SameOrd t)ᶜ : Set Zeros),
          (2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros))) := by
  have hg := hgs.continuous
  have hs1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroConeValue g t (2 * r) (σ : Zeros) := by
    have h1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
        zeroTerm (sampleTest g t (2 * r)) (σ : Zeros) :=
      (zeroTerm_summable (sampleTest_contDiff hgs t (2 * r))
        (sampleTest_hasCompactSupport hgc t (2 * r))).subtype _
    have h2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
        zeroTerm (sampleTest g t (-(2 * r))) (σ : Zeros) :=
      (zeroTerm_summable (sampleTest_contDiff hgs t (-(2 * r)))
        (sampleTest_hasCompactSupport hgc t (-(2 * r)))).subtype _
    have hr1 := ((Complex.hasSum_re h1.hasSum).summable).add ((Complex.hasSum_im h1.hasSum).summable)
    have hr2 := ((Complex.hasSum_re h2.hasSum).summable).add ((Complex.hasSum_im h2.hasSum).summable)
    exact hr1.add hr2
  have hs2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) => zeroConeValue g t r (σ : Zeros) := by
    have h1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
        zeroTerm (sampleTest g t r) (σ : Zeros) :=
      (zeroTerm_summable (sampleTest_contDiff hgs t r)
        (sampleTest_hasCompactSupport hgc t r)).subtype _
    have h2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
        zeroTerm (sampleTest g t (-r)) (σ : Zeros) :=
      (zeroTerm_summable (sampleTest_contDiff hgs t (-r))
        (sampleTest_hasCompactSupport hgc t (-r))).subtype _
    have hr1 := ((Complex.hasSum_re h1.hasSum).summable).add ((Complex.hasSum_im h1.hasSum).summable)
    have hr2 := ((Complex.hasSum_re h2.hasSum).summable).add ((Complex.hasSum_im h2.hasSum).summable)
    exact hr1.add hr2
  unfold offOrdProjectiveDefect channelProjectiveDefect
  rw [offOrdChannel_eq_tsum hgs hgc t (2 * r), offOrdChannel_eq_tsum hgs hgc t r,
    ← tsum_mul_right, ← tsum_mul_right,
    ← (hs1.mul_right (evenResp g 0 r)).tsum_sub (hs2.mul_right (evenResp g 0 (2 * r)))]
  exact tsum_congr fun σ => singleOffOrdProjectiveDefect_eq hg hgc heven t r (σ : Zeros)

/-- The same statement, packaged as a single sample of the projective taper. -/
theorem offOrdProjectiveDefect_eq_offOrdTerm {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    offOrdProjectiveDefect g t r
      = 2 * reim (offOrdTerm (sampleTest (projTaper g r) t 0) t) := by
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hsum : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hpd t 0)
      (sampleTest_hasCompactSupport hpk t 0)).subtype _
  rw [offOrdProjectiveDefect_eq_tsum hgs hgc heven t r, offOrdTerm, reim_tsum hsum,
    ← tsum_mul_left]

/-! ## The envelope -/

/-- **`offOrdProjectiveTailEnvelope`.**  The off-ordinate tail obeys an envelope
built from the *projective* taper: the companion's strip bound for the test
function `h_r`, times the companion's off-ordinate zero weight. -/
theorem offOrdProjectiveTailEnvelope {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    |offOrdProjectiveDefect g t r|
      ≤ 4 * stripConst (sampleTest (projTaper g r) t 0) Λ * offOrdWeight t := by
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hps : ∀ u, sampleTest (projTaper g r) t 0 u ≠ 0 → |u| ≤ Λ :=
    sampleTest_support_radius (projTaper_support hsupp r) _ _
  have henv := offOrdinateTailEnvelope (sampleTest_contDiff hpd t 0)
    (sampleTest_hasCompactSupport hpk t 0) hps hΛ t
  have hreim := abs_reim_le (offOrdTerm (sampleTest (projTaper g r) t 0) t)
  rw [offOrdProjectiveDefect_eq_offOrdTerm hgs hgc heven t r, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have hw := offOrdWeight_nonneg t
  nlinarith [norm_nonneg (offOrdTerm (sampleTest (projTaper g r) t 0) t),
    stripConst_nonneg (sampleTest (projTaper g r) t 0) Λ]

end LiteralWeilOffOrdinateProjectiveTail
end Zeta23Bridge
