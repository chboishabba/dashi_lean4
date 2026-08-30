/-
# The literal off-ordinate carrier as a finite core plus an explicit far remainder

`LiteralWeilOffOrdinateReflectionSymmetrization` identifies the off-ordinate
projective defect with one half of the reflection-symmetrized sum over the
off-ordinate carrier,

    𝔇_off(g, t, r) = ½ ∑'_{Im σ ≠ t} (Z_σ + Z_{Rσ}) .

`FarShellCutoffTailBound` and `NearFarCarrierSplit` supply the cutoff machinery.
Putting them together, this module lands the decomposition on the literal object
`offOrdProjectiveDefect` itself: for every cutoff `J ≥ 1`,

    | 𝔇_off(g, t, r) − ½ ∑_{σ ∈ nearOffFinset t J} (Z_σ + Z_{Rσ}) |
        ≤ ½ · C · farShellBound A |t| J ,

where the near set `nearOffFinset t J` — the off-ordinate zeros with
`|Im σ − t| < J` — is a *finite* set, `C` is the uniform reflection-pair
curvature constant of the projected taper, and `A` is the constant of the
unconditional local zero count.  The remainder is explicit in `J` and tends to
zero, so the whole remaining content of the off-ordinate estimate is the signed
behaviour of a finite sum.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.NearFarCarrierSplit
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization

noncomputable section

open scoped Real
open Zeta23

namespace Zeta23Bridge
namespace OffOrdinateCutoffCarrier

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.FarShellCutoffTailBound
open Zeta23Bridge.NearFarCarrierSplit

/-! ## 1. The symmetrized off-ordinate summand -/

/-- The reflection-symmetrized projective response of an off-ordinate zero. -/
def offPairTerm (g : ℝ → ℝ) (t r : ℝ) (σ : ((SameOrd t)ᶜ : Set Zeros)) : ℝ :=
  (2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros)))
    + (2 * reim (zeroTerm (sampleTest (projTaper g r) t 0)
        ((LiteralWeilOffOrdinateReflectionSymmetrization.reflectOffOrdEquiv t σ :
          ((SameOrd t)ᶜ : Set Zeros)) : Zeros)))

theorem offPairTerm_eq_pairTerm (g : ℝ → ℝ) (t r : ℝ)
    (σ : ((SameOrd t)ᶜ : Set Zeros)) :
    offPairTerm g t r σ = pairTerm (projTaper g r) t (σ : Zeros) := by
  unfold offPairTerm pairTerm zeroConeValue
  simp only [neg_zero, two_mul]
  rfl

theorem summable_offPairTerm {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t r : ℝ) :
    Summable (offPairTerm g t r) := by
  have hf := projectiveZeroSummable hgs hgc t r
  have hfe := (LiteralWeilOffOrdinateReflectionSymmetrization.reflectOffOrdEquiv
    t).summable_iff.mpr hf
  exact hf.add hfe

/-- The off-ordinate projective defect is one half of the sum of the symmetrized
summands. -/
theorem offOrdProjectiveDefect_eq_half_tsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    offOrdProjectiveDefect g t r = (1 / 2 : ℝ) * ∑' σ, offPairTerm g t r σ :=
  offOrdProjectiveDefect_eq_half_reflection_tsum hgs hgc heven t r

/-! ## 2. The finite near off-ordinate core -/

/-- The off-ordinate zeros inside the cutoff. -/
def nearOffSet (t : ℝ) (J : ℕ) : Set ((SameOrd t)ᶜ : Set Zeros) :=
  {σ | |((σ : Zeros) : ℂ).im - t| < (J : ℝ)}

theorem nearOffSet_finite (t : ℝ) (J : ℕ) : (nearOffSet t J).Finite := by
  have hfin := nearSet_finite t J
  have hinj : Set.InjOn (fun σ : ((SameOrd t)ᶜ : Set Zeros) => (σ : Zeros))
      ((fun σ : ((SameOrd t)ᶜ : Set Zeros) => (σ : Zeros)) ⁻¹' (nearSet t J)) :=
    fun x _ y _ h => Subtype.ext h
  exact (hfin.preimage hinj).subset (fun σ hσ => hσ)

/-- The finite near off-ordinate core. -/
def nearOffFinset (t : ℝ) (J : ℕ) : Finset ((SameOrd t)ᶜ : Set Zeros) :=
  (nearOffSet_finite t J).toFinset

theorem mem_nearOffFinset_iff (t : ℝ) (J : ℕ) (σ : ((SameOrd t)ᶜ : Set Zeros)) :
    σ ∈ nearOffFinset t J ↔ |((σ : Zeros) : ℂ).im - t| < (J : ℝ) := by
  unfold nearOffFinset
  rw [Set.Finite.mem_toFinset]
  rfl

/-! ## 3. The cutoff decomposition of the literal off-ordinate defect -/

/-- **The off-ordinate carrier is a finite core plus an explicit far remainder.**

For a compactly supported `C²` real-even taper `g`, a radius `r` and a cutoff
`J ≥ 1`, the literal off-ordinate projective defect differs from one half of its
*finite* near-core sum by at most `½ C · farShellBound A |t| J`, where `C` is any
uniform bound for the reflection-pair curvature of the projected taper and `A`
the local zero-count constant. -/
theorem abs_offOrdProjectiveDefect_sub_nearCore_le {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) {A C : ℝ} (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (hC : ∀ ρ : Zeros, pairWeightCurvature (projTaper g r) (heightOf ρ) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) :
    |offOrdProjectiveDefect g t r
        - (1 / 2 : ℝ) * ∑ σ ∈ nearOffFinset t J, offPairTerm g t r σ|
      ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J) := by
  classical
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hpe : ∀ u, projTaper g r (-u) = projTaper g r u := projTaper_even heven r
  have hsum := summable_offPairTerm hgs hgc t r
  have hw : Summable (fun σ : ((SameOrd t)ᶜ : Set Zeros) => tailTermFrom t J (σ : Zeros)) :=
    (summable_tailTermFrom hJ t).subtype _
  have hwnn : ∀ σ : ((SameOrd t)ᶜ : Set Zeros), 0 ≤ tailTermFrom t J (σ : Zeros) :=
    fun σ => tailTermFrom_nonneg t J _
  have hB : ∑' σ : ((SameOrd t)ᶜ : Set Zeros), tailTermFrom t J (σ : Zeros)
      ≤ farShellBound A |t| J := by
    refine le_trans ?_ (tsum_tailTermFrom_le hA1 hloc t J hJ)
    exact Summable.tsum_subtype_le _ _ (fun ρ => tailTermFrom_nonneg t J ρ)
      (summable_tailTermFrom hJ t)
  have hdom : ∀ σ : ((SameOrd t)ᶜ : Set Zeros), σ ∉ nearOffFinset t J →
      |offPairTerm g t r σ| ≤ C * tailTermFrom t J (σ : Zeros) := by
    intro σ hnot
    have hge : (J : ℝ) ≤ |((σ : Zeros) : ℂ).im - t| := by
      by_contra hlt
      exact hnot ((mem_nearOffFinset_iff t J σ).2 (not_le.1 hlt))
    rw [offPairTerm_eq_pairTerm]
    exact abs_pairTerm_le hpd hpk hpe t hC J (σ : Zeros) hge hJ
  have key : |(∑' σ, offPairTerm g t r σ) - ∑ σ ∈ nearOffFinset t J, offPairTerm g t r σ|
      ≤ C * farShellBound A |t| J :=
    abs_tsum_sub_finset_le hC0 hsum hw hwnn _ hdom hB
  rw [offOrdProjectiveDefect_eq_half_tsum hgs hgc heven t r, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

/-- **The off-ordinate cutoff decomposition, with all constants supplied.** -/
theorem exists_offOrd_near_far_split {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 ≤ C ∧
      (∀ J : ℕ, 1 ≤ J →
        |offOrdProjectiveDefect g t r
            - (1 / 2 : ℝ) * ∑ σ ∈ nearOffFinset t J, offPairTerm g t r σ|
          ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J)) ∧
      Filter.Tendsto (fun J : ℕ => (1 / 2 : ℝ) * (C * farShellBound A |t| J))
        Filter.atTop (nhds 0) := by
  obtain ⟨A, hA1, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨C₀, hC₀⟩ := exists_uniform_carrier_curvature_bound
    (projTaper_contDiff hgs r) (projTaper_hasCompactSupport hgc r)
  refine ⟨A, max C₀ 0, hA1, le_max_right _ _, ?_, ?_⟩
  · intro J hJ
    exact abs_offOrdProjectiveDefect_sub_nearCore_le hgs hgc heven t r hA1
      (le_max_right _ _) hloc (fun ρ => le_trans (hC₀ ρ) (le_max_left _ _)) J hJ
  · have := ((farShellBound_tendsto_zero A |t|).const_mul (max C₀ 0)).const_mul (1 / 2 : ℝ)
    simpa using this

/-- **Cutoff selection for the off-ordinate carrier.**  For any accuracy `ε > 0`
the literal off-ordinate projective defect is within `ε` of one half of a finite
signed sum over the near off-ordinate shells. -/
theorem exists_cutoff_offOrd_near_far_split {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 1 ≤ J ∧
      |offOrdProjectiveDefect g t r
          - (1 / 2 : ℝ) * ∑ σ ∈ nearOffFinset t J, offPairTerm g t r σ| < ε := by
  obtain ⟨A, C, hA1, hC0, hbound, hlim⟩ := exists_offOrd_near_far_split hgs hgc heven t r
  have hev : ∀ᶠ J : ℕ in Filter.atTop,
      (1 / 2 : ℝ) * (C * farShellBound A |t| J) < ε := by
    simpa using hlim.eventually (eventually_lt_nhds hε)
  obtain ⟨J, hJ⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  exact ⟨J, hJ.2, lt_of_le_of_lt (hbound J hJ.2) hJ.1⟩

end OffOrdinateCutoffCarrier
end Zeta23Bridge
