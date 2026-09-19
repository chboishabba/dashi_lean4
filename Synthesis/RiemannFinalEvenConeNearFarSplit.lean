import Zeta23Bridge.LiteralWeilOffOrdinateEvenConeReflectionSymmetrization
import Zeta23Bridge.NearFarCarrierSplit

/-!
# Final universal even-cone near/far split

This file performs the cutoff decomposition directly on the final universal
even-cone off-ordinate channel. It does not identify that channel with the
rank-two/projective response.

For the literal sample radius s, absorb the sample cosine into the real taper:

    g_s(u) = g(u) cos(s u).

Then a functional-equation reflection pair in the final two-sample cone is
exactly the radius-zero signed pair response of g_s. Consequently the existing
oscillatory 1/delta^2 decay and zero-count tail theorem apply on the final
carrier itself.

The result is the consumer-faithful decomposition

    D_off^final(g,t,s)
      = 1/2 * sum_{sigma in I_near(t,J)} D_sigma(g,t,s) + R_J

with

    |R_J| <= 1/2 * C_s * farShellBound A |t| J,

where the finite core remains signed.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateEvenConeReflectionSymmetrization
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.FarShellCutoffTailBound
open Zeta23Bridge.NearFarCarrierSplit

def sampledCosTaper (g : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun u => g u * Real.cos (s * u)

theorem sampledCosTaper_contDiff {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (s : ℝ) :
    ContDiff ℝ 2 (sampledCosTaper g s) := by
  unfold sampledCosTaper
  fun_prop

theorem sampledCosTaper_hasCompactSupport {g : ℝ → ℝ}
    (hgc : HasCompactSupport g) (s : ℝ) :
    HasCompactSupport (sampledCosTaper g s) := by
  unfold sampledCosTaper
  exact hgc.mul_right

theorem sampledCosTaper_even {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u) (s : ℝ) :
    ∀ u, sampledCosTaper g s (-u) = sampledCosTaper g s u := by
  intro u
  unfold sampledCosTaper
  rw [heven, neg_mul, Real.cos_neg]

def finalPairTerm (g : ℝ → ℝ) (t s : ℝ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) : ℝ :=
  zeroConeValue g t s (sigma : Zeros)
    + zeroConeValue g t s
      ((reflectOffOrdEquiv t sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros)

theorem finalPairTerm_eq_sampledPairTerm {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t s : ℝ) (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    finalPairTerm g t s sigma
      = pairTerm (sampledCosTaper g s) t (sigma : Zeros) := by
  let rho : Zeros := (sigma : Zeros)
  have hfinal :=
    zeroConeValue_add_reflect_eq_integral hgs.continuous hgc heven t s rho
  have hsample :=
    zeroConeValue_add_reflect_eq_integral
      (sampledCosTaper_contDiff hgs s).continuous
      (sampledCosTaper_hasCompactSupport hgc s)
      (sampledCosTaper_even heven s)
      t 0 rho
  have hreflect :
      ((reflectOffOrdEquiv t sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros)
        = reflectZero rho := rfl
  rw [finalPairTerm, hreflect, hfinal]
  unfold pairTerm
  rw [hsample]
  simp only [zero_mul, Real.cos_zero, mul_one]
  congr 2
  apply integral_congr_ae
  filter_upwards with u
  unfold reflectionPairWeight sampledCosTaper
  ring

theorem summable_finalPairTerm {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t s : ℝ) :
    Summable (finalPairTerm g t s) := by
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ :=
    fun sigma => zeroConeValue g t s (sigma : Zeros)
  have hf : Summable f := zeroConeValue_summable hgs hgc t s
  have hfr : Summable (fun sigma => f (reflectOffOrdEquiv t sigma)) :=
    (reflectOffOrdEquiv t).summable_iff.mpr hf
  exact hf.add hfr

def finalNearOffSet (t : ℝ) (J : ℕ) :
    Set ((SameOrd t)ᶜ : Set Zeros) :=
  {sigma | |((sigma : Zeros) : ℂ).im - t| < (J : ℝ)}

theorem finalNearOffSet_finite (t : ℝ) (J : ℕ) :
    (finalNearOffSet t J).Finite := by
  have hfin := nearSet_finite t J
  have hinj : Set.InjOn
      (fun sigma : ((SameOrd t)ᶜ : Set Zeros) => (sigma : Zeros))
      ((fun sigma : ((SameOrd t)ᶜ : Set Zeros) => (sigma : Zeros)) ⁻¹'
        (nearSet t J)) :=
    fun x _ y _ h => Subtype.ext h
  exact (hfin.preimage hinj).subset (fun sigma hsigma => hsigma)

def finalNearOffFinset (t : ℝ) (J : ℕ) :
    Finset ((SameOrd t)ᶜ : Set Zeros) :=
  (finalNearOffSet_finite t J).toFinset

theorem mem_finalNearOffFinset_iff
    (t : ℝ) (J : ℕ) (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    sigma ∈ finalNearOffFinset t J
      ↔ |((sigma : Zeros) : ℂ).im - t| < (J : ℝ) := by
  unfold finalNearOffFinset
  rw [Set.Finite.mem_toFinset]
  rfl

theorem finalOffOrd_eq_half_pair_tsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (t s : ℝ) :
    evenConeFunctional (offOrdVec (sampleFam g t s) t)
      = (1 / 2 : ℝ) * ∑' sigma, finalPairTerm g t s sigma := by
  change offOrdChannel g t s = _
  exact offOrdChannel_eq_half_reflection_tsum hgs hgc t s

theorem abs_finalOffOrd_sub_finiteNear_le {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t s : ℝ) {A C : ℝ}
    (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ tau : ℝ,
      ((zetaZeroConfig).N tau (tau + 1) : ℝ)
        ≤ A * Real.log (|tau| + 3))
    (hC : ∀ rho : Zeros,
      pairWeightCurvature (sampledCosTaper g s) (heightOf rho) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) :
    |evenConeFunctional (offOrdVec (sampleFam g t s) t)
        - (1 / 2 : ℝ) * ∑ sigma ∈ finalNearOffFinset t J,
            finalPairTerm g t s sigma|
      ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J) := by
  classical
  have hsampleC2 := sampledCosTaper_contDiff hgs s
  have hsampleCompact := sampledCosTaper_hasCompactSupport hgc s
  have hsampleEven := sampledCosTaper_even heven s
  have hsum := summable_finalPairTerm hgs hgc t s
  have hweight :
      Summable (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        tailTermFrom t J (sigma : Zeros)) :=
    (summable_tailTermFrom hJ t).subtype _
  have hweightnn : ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
      0 ≤ tailTermFrom t J (sigma : Zeros) :=
    fun sigma => tailTermFrom_nonneg t J (sigma : Zeros)
  have hB :
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          tailTermFrom t J (sigma : Zeros)
        ≤ farShellBound A |t| J := by
    have hsub := Summable.tsum_subtype_le _ _
      (fun rho => tailTermFrom_nonneg t J rho)
      (summable_tailTermFrom hJ t)
    exact le_trans hsub (tsum_tailTermFrom_le hA1 hloc t J hJ)
  have hdom : ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
      sigma ∉ finalNearOffFinset t J →
      |finalPairTerm g t s sigma|
        ≤ C * tailTermFrom t J (sigma : Zeros) := by
    intro sigma hnot
    have hge : (J : ℝ) ≤ |((sigma : Zeros) : ℂ).im - t| := by
      by_contra hlt
      exact hnot ((mem_finalNearOffFinset_iff t J sigma).2 (not_le.1 hlt))
    rw [finalPairTerm_eq_sampledPairTerm hgs hgc heven t s sigma]
    exact abs_pairTerm_le hsampleC2 hsampleCompact hsampleEven t hC
      J (sigma : Zeros) hge hJ
  have hsplit := abs_tsum_sub_finset_le hC0 hsum hweight hweightnn
    (finalNearOffFinset t J) hdom hB
  rw [finalOffOrd_eq_half_pair_tsum hgs hgc t s, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left hsplit (by norm_num)

theorem exists_finalEvenCone_near_far_split {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 ≤ C ∧
      (∀ J : ℕ, 1 ≤ J →
        |evenConeFunctional (offOrdVec (sampleFam g t s) t)
            - (1 / 2 : ℝ) * ∑ sigma ∈ finalNearOffFinset t J,
                finalPairTerm g t s sigma|
          ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J))
      ∧ Filter.Tendsto
          (fun J : ℕ => (1 / 2 : ℝ) * (C * farShellBound A |t| J))
          Filter.atTop (nhds 0) := by
  obtain ⟨A, hA1, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hsampleC2 := sampledCosTaper_contDiff hgs s
  have hsampleCompact := sampledCosTaper_hasCompactSupport hgc s
  obtain ⟨C0, hC0⟩ :=
    exists_uniform_carrier_curvature_bound hsampleC2 hsampleCompact
  refine ⟨A, max C0 0, hA1, le_max_right _ _, ?_, ?_⟩
  · intro J hJ
    exact abs_finalOffOrd_sub_finiteNear_le hgs hgc heven t s hA1
      (le_max_right _ _) hloc
      (fun rho => le_trans (hC0 rho) (le_max_left _ _)) J hJ
  · have hlim :=
      ((farShellBound_tendsto_zero A |t|).const_mul (max C0 0)).const_mul
        (1 / 2 : ℝ)
    simpa [mul_assoc] using hlim

end Synthesis
