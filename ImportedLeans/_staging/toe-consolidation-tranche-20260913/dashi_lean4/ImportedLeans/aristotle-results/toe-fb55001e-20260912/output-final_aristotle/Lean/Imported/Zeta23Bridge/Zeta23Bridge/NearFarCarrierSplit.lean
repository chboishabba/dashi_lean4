/-
# The finite signed near-shell carrier interface

`FarShellCutoffTailBound` pays the shells `|Im ρ − t| ≥ J` mechanically, with an
explicit bound that decays in the cutoff.  This module turns that into the
interface the signed analysis actually needs:

    signed far tail  =  a *finite* signed sum over the near shells
                        +  a remainder of size at most  C · farShellBound A |t| J .

Concretely, for a compactly supported `C²` real-even taper `g`,

    | ∑'_{|Im ρ − t| ≥ 1} (Z_ρ + Z_{Rρ})  −  ∑_{ρ ∈ nearFinset t J} (Z_ρ + Z_{Rρ}) |
        ≤ C · farShellBound A |t| J ,

where `Z_ρ = zeroConeValue g t 0 ρ`, `R` is the functional-equation reflection,
`C` is the uniform reflection-pair curvature constant of
`ReflectionPairCurvatureBound`, and `nearFinset t J` is the (proved finite) set
of carrier points with `|Im ρ − t| < J`.

That is the "finite difficult core + explicit summable tail" decomposition: no
qualitative limit is used, only the two proved explicit ingredients, and the
delicate signed/oscillatory analysis is confined to the finitely many shells
`1 ≤ |Im ρ − t| < J`.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.FarShellCutoffTailBound

noncomputable section

open scoped Real
open Zeta23

namespace Zeta23Bridge
namespace NearFarCarrierSplit

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.FarShellCutoffTailBound

/-! ## 0. A scalar helper -/

/-- `|∑' f| ≤ ∑' |f|` for an absolutely summable real family. -/
theorem abs_tsum_le_tsum_abs {ι : Type*} (f : ι → ℝ) (h : Summable (fun i => |f i|)) :
    |∑' i, f i| ≤ ∑' i, |f i| := by
  simpa [Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm (f := f) (by simpa [Real.norm_eq_abs] using h)


/-- **A generic near/far splitting bound.**  If a real family `f` is summable and,
off a finite set `s`, dominated by `C` times a nonnegative summable weight `w`
whose total mass is at most `B`, then the full sum differs from the finite sum
over `s` by at most `C * B`. -/
theorem abs_tsum_sub_finset_le {ι : Type*} {f w : ι → ℝ} {C B : ℝ}
    (hC0 : 0 ≤ C) (hf : Summable f) (hw : Summable w) (hwnn : ∀ i, 0 ≤ w i)
    (s : Finset ι) (hdom : ∀ i, i ∉ s → |f i| ≤ C * w i) (hB : ∑' i, w i ≤ B) :
    |(∑' i, f i) - ∑ i ∈ s, f i| ≤ C * B := by
  classical
  have hsplit := hf.sum_add_tsum_compl (s := s)
  have hdiff : (∑' i, f i) - ∑ i ∈ s, f i
      = ∑' i : ((↑s : Set ι)ᶜ : Set ι), f i := by
    rw [← hsplit]; ring
  rw [hdiff]
  have hdom' : ∀ i : ((↑s : Set ι)ᶜ : Set ι), |f (i : ι)| ≤ C * w (i : ι) := by
    rintro ⟨i, hi⟩
    exact hdom i (by simpa using hi)
  have hwC : Summable (fun i : ((↑s : Set ι)ᶜ : Set ι) => C * w (i : ι)) :=
    (hw.mul_left C).subtype _
  have habs : Summable (fun i : ((↑s : Set ι)ᶜ : Set ι) => |f (i : ι)|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hdom' hwC
  calc |∑' i : ((↑s : Set ι)ᶜ : Set ι), f i|
      ≤ ∑' i : ((↑s : Set ι)ᶜ : Set ι), |f (i : ι)| := abs_tsum_le_tsum_abs _ habs
    _ ≤ ∑' i : ((↑s : Set ι)ᶜ : Set ι), C * w (i : ι) := habs.tsum_le_tsum hdom' hwC
    _ ≤ ∑' i : ι, C * w i := by
        refine Summable.tsum_subtype_le _ _ (fun i => ?_) (hw.mul_left C)
        have := hwnn i
        positivity
    _ = C * ∑' i, w i := tsum_mul_left
    _ ≤ C * B := mul_le_mul_of_nonneg_left hB hC0

/-! ## 1. The signed reflection-pair carrier -/

/-- The signed two-sample cone response of a functional-equation pair. -/
def pairTerm (g : ℝ → ℝ) (t : ℝ) (ρ : Zeros) : ℝ :=
  zeroConeValue g t 0 ρ + zeroConeValue g t 0 (reflectZero ρ)

/-- The signed far carrier: the pair responses at ordinate distance at least `1`. -/
def signedFarTerm (g : ℝ → ℝ) (t : ℝ) (ρ : Zeros) : ℝ :=
  if 1 ≤ |(ρ : ℂ).im - t| then pairTerm g t ρ else 0

theorem abs_signedFarTerm_eq (g : ℝ → ℝ) (t : ℝ) (ρ : Zeros) :
    |signedFarTerm g t ρ|
      = if 1 ≤ |(ρ : ℂ).im - t| then |pairTerm g t ρ| else 0 := by
  unfold signedFarTerm
  split
  · rfl
  · simp

theorem summable_abs_signedFarTerm {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t : ℝ) :
    Summable (fun ρ : Zeros => |signedFarTerm g t ρ|) := by
  have h := summable_reflection_far_tail_uniform hg hgc heven t
  refine h.congr (fun ρ => ?_)
  rw [abs_signedFarTerm_eq]
  rfl

theorem summable_signedFarTerm {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t : ℝ) :
    Summable (signedFarTerm g t) :=
  Summable.of_abs (summable_abs_signedFarTerm hg hgc heven t)

/-! ## 2. The near shells form a finite set -/

/-- The carrier points inside the cutoff. -/
def nearSet (t : ℝ) (J : ℕ) : Set Zeros := {ρ : Zeros | |(ρ : ℂ).im - t| < (J : ℝ)}

theorem nearSet_finite (t : ℝ) (J : ℕ) : (nearSet t J).Finite := by
  have hfin : ((zetaZeroConfig).window (t - (J : ℝ)) (t + (J : ℝ))).Finite :=
    zetaZeroConfig.finite_window _ _
  have hinj : Set.InjOn (fun ρ : Zeros => (ρ : ℂ))
      ((fun ρ : Zeros => (ρ : ℂ)) ⁻¹' ((zetaZeroConfig).window (t - (J : ℝ)) (t + (J : ℝ)))) :=
    fun x _ y _ h => Subtype.ext h
  have hpre := hfin.preimage hinj
  refine hpre.subset (fun ρ hρ => ?_)
  have hlt : |(ρ : ℂ).im - t| < (J : ℝ) := hρ
  have h1 : t - (J : ℝ) < (ρ : ℂ).im := by
    have := neg_lt_of_abs_lt hlt; linarith
  have h2 : (ρ : ℂ).im ≤ t + (J : ℝ) := by
    have := lt_of_abs_lt hlt; linarith
  exact ⟨ρ.2, h1, h2⟩

/-- The near shells, as a `Finset`. -/
def nearFinset (t : ℝ) (J : ℕ) : Finset Zeros := (nearSet_finite t J).toFinset

theorem mem_nearFinset_iff (t : ℝ) (J : ℕ) (ρ : Zeros) :
    ρ ∈ nearFinset t J ↔ |(ρ : ℂ).im - t| < (J : ℝ) := by
  unfold nearFinset
  rw [Set.Finite.mem_toFinset]
  rfl

/-! ## 3. Beyond the cutoff, the signed carrier is dominated by the shell weight -/

theorem abs_pairTerm_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) {C : ℝ} (hC : ∀ ρ : Zeros, pairWeightCurvature g (heightOf ρ) ≤ C)
    (J : ℕ) (ρ : Zeros) (hρ : (J : ℝ) ≤ |(ρ : ℂ).im - t|) (hJ : 1 ≤ J) :
    |pairTerm g t ρ| ≤ C * tailTermFrom t J ρ := by
  have hJ1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hge1 : (1:ℝ) ≤ |(ρ : ℂ).im - t| := le_trans hJ1 hρ
  have hδ : ((ρ : ℂ).im - t) ≠ 0 := by
    intro h; rw [h] at hge1; simp at hge1; linarith
  have h1 := abs_zeroConeValue_add_reflect_le hg hgc heven t ρ hδ
  have hsq : (0:ℝ) < ((ρ : ℂ).im - t) ^ 2 := by positivity
  have hmul : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)
        * (pairWeightCurvature g (heightOf ρ) / ((ρ : ℂ).im - t) ^ 2)
      ≤ C * tailTermFrom t J ρ := by
    unfold tailTermFrom
    rw [if_pos hρ]
    have hnum : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) * pairWeightCurvature g (heightOf ρ)
        ≤ C * ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) := by
      have hm : (0:ℝ) ≤ ((zetaZeroConfig).mult (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hC ρ]
    have e1 : ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)
          * (pairWeightCurvature g (heightOf ρ) / ((ρ : ℂ).im - t) ^ 2)
        = (((zetaZeroConfig).mult (ρ : ℂ) : ℝ) * pairWeightCurvature g (heightOf ρ))
          / ((ρ : ℂ).im - t) ^ 2 := by ring
    have e2 : C * (((zetaZeroConfig).mult (ρ : ℂ) : ℝ) / ((ρ : ℂ).im - t) ^ 2)
        = (C * ((zetaZeroConfig).mult (ρ : ℂ) : ℝ)) / ((ρ : ℂ).im - t) ^ 2 := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hnum hsq.le
  exact le_trans h1 hmul

/-! ## 4. The near/far split of the signed carrier -/

/-- **The finite signed near-shell carrier interface.**

The signed reflection-symmetrized far carrier of the literal zeta zeros differs
from its *finite* restriction to the near shells `|Im ρ − t| < J` by at most
`C · farShellBound A |t| J`, an explicit quantity that decays in the cutoff.
Delicate signed analysis is therefore needed only on the finite near-shell
carrier `nearFinset t J`. -/
theorem abs_signedFarTerm_sub_nearFinset_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) {A C : ℝ} (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (hC : ∀ ρ : Zeros, pairWeightCurvature g (heightOf ρ) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) :
    |(∑' ρ : Zeros, signedFarTerm g t ρ) - ∑ ρ ∈ nearFinset t J, signedFarTerm g t ρ|
      ≤ C * farShellBound A |t| J := by
  classical
  have hsum := summable_signedFarTerm hg hgc heven t
  have hdom : ∀ ρ : Zeros, ρ ∉ nearFinset t J →
      |signedFarTerm g t ρ| ≤ C * tailTermFrom t J ρ := by
    intro ρ hnot
    have hge : (J : ℝ) ≤ |(ρ : ℂ).im - t| := by
      by_contra hlt
      exact hnot ((mem_nearFinset_iff t J ρ).2 (not_le.1 hlt))
    have hJ1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    have heq : |signedFarTerm g t ρ| = |pairTerm g t ρ| := by
      unfold signedFarTerm
      rw [if_pos (le_trans hJ1 hge)]
    rw [heq]
    exact abs_pairTerm_le hg hgc heven t hC J ρ hge hJ
  exact abs_tsum_sub_finset_le hC0 hsum (summable_tailTermFrom hJ t)
    (fun ρ => tailTermFrom_nonneg t J ρ) _ hdom (tsum_tailTermFrom_le hA1 hloc t J hJ)

/-- **The interface, with all constants supplied.**

For every compactly supported `C²` real-even taper and every sample ordinate
there are explicit constants `A ≥ 1` (the local zero count) and `C ≥ 0` (the
uniform reflection-pair curvature) such that, for every cutoff `J ≥ 1`, the
signed far carrier is a finite signed near-shell sum plus a remainder of size at
most `C · farShellBound A |t| J`, and the remainder tends to `0` as `J → ∞`. -/
theorem exists_near_far_split {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t : ℝ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 ≤ C ∧
      (∀ J : ℕ, 1 ≤ J →
        |(∑' ρ : Zeros, signedFarTerm g t ρ) - ∑ ρ ∈ nearFinset t J, signedFarTerm g t ρ|
          ≤ C * farShellBound A |t| J) ∧
      Filter.Tendsto (fun J : ℕ => C * farShellBound A |t| J) Filter.atTop (nhds 0) := by
  obtain ⟨A, hA1, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨C₀, hC₀⟩ := exists_uniform_carrier_curvature_bound hg hgc
  refine ⟨A, max C₀ 0, hA1, le_max_right _ _, ?_, ?_⟩
  · intro J hJ
    exact abs_signedFarTerm_sub_nearFinset_le hg hgc heven t hA1 (le_max_right _ _) hloc
      (fun ρ => le_trans (hC₀ ρ) (le_max_left _ _)) J hJ
  · have := (farShellBound_tendsto_zero A |t|).const_mul (max C₀ 0)
    simpa using this

/-- **Cutoff selection for the signed carrier.**  Given any accuracy `ε > 0`,
the signed far carrier is within `ε` of a finite signed sum over the near
shells. -/
theorem exists_cutoff_near_far_split {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 1 ≤ J ∧
      |(∑' ρ : Zeros, signedFarTerm g t ρ) - ∑ ρ ∈ nearFinset t J, signedFarTerm g t ρ| < ε := by
  obtain ⟨A, C, hA1, hC0, hbound, hlim⟩ := exists_near_far_split hg hgc heven t
  have hev : ∀ᶠ J : ℕ in Filter.atTop, C * farShellBound A |t| J < ε := by
    simpa using hlim.eventually (eventually_lt_nhds hε)
  obtain ⟨J, hJ⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  exact ⟨J, hJ.2, lt_of_le_of_lt (hbound J hJ.2) hJ.1⟩

end NearFarCarrierSplit
end Zeta23Bridge
