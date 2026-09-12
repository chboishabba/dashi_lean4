/-
# A gamma budget for the pole-quotient lane, linear in the taper strip constant

`LiteralWeilGammaConeBound.lean` proves that the gamma cone value of the literal
Weil balance is bounded by the explicit envelope `epsGamma g t r`, defined as the
`L¹` norm of the smoothed gamma bracket.  That envelope is finite, but it is
stated as an integral of the taper's own transform: it says nothing about how the
budget scales with the taper or with the ordinate.

This module makes that scaling explicit.  Combining

* the strip envelope `|ĝ(x + s − t)| ≤ stripConst(k_s, Λ)/(1 + x²)`
  (`abs_cosFT_le`, the companion's `[eq:hfbound]` at a real point), and
* the square-root growth `|B(x)| ≤ A + B√|x|` of the gamma bracket
  (`exists_gammaBracket_bound`, from the companion's *proved* Stirling clause),

the whole `x`-integral factorises: the taper contributes only through its strip
constant, and the gamma bracket contributes an absolute number

    cΓ = ∫ (A + B√|x|)/(1 + x²) dx           (`gammaTailConstant`, finite),

so that, for every compactly supported even `C²` taper, every ordinate and every
radius,

    |ℓ(Q_Γ)| ≤ CΓ · (stripConst(k_r, Λ) + stripConst(k_{−r}, Λ))

with `CΓ = cΓ/2π` an absolute constant (`exists_gamma_budget_linear_in_stripConst`).

This is the `B_Γ` the pole-quotient lane asks for, at literal strength and
uniform in `t`.  What it is *not* is small: `stripConst(k, Λ) = e^{Λ/2}(‖k‖₁ +
‖k''‖₁)`, and for the high-ordinate taper of `exists_positive_taper_poleEven_zero`
the second-derivative term grows quadratically as the support shrinks.  Section
29 of `FRONTIER.md` records the accuracy the lane actually needs — relative
`O(|t|^{-2})` against the height-free cluster baseline — which this budget does
not meet, and nothing here claims otherwise.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilGammaConeBound

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace PoleQuotientGammaBudget

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilGammaConeBound

/-! ## The absolute gamma tail constant -/

/-- The majorant of the gamma integrand after the taper has been factored out. -/
def gammaMajorant (A B : ℝ) : ℝ → ℝ := fun x => (A + B * Real.sqrt |x|) / (1 + x ^ 2)

/-- **The majorant is integrable**, by the same Japanese-bracket domination that
makes the gamma integrand integrable: quadratic decay against square-root growth. -/
theorem integrable_gammaMajorant {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Integrable (gammaMajorant A B) := by
  have hdom : Integrable (fun x : ℝ => (8 * (A + B)) * (1 + ‖x‖) ^ (-((3 : ℝ) / 2))) := by
    refine Integrable.const_mul ?_ _
    refine integrable_one_add_norm ?_
    simp [Module.finrank_self]
    norm_num
  have hmeas : AEStronglyMeasurable (gammaMajorant A B) := by
    have : Continuous (gammaMajorant A B) := by
      unfold gammaMajorant
      exact (continuous_const.add (continuous_const.mul
        (Real.continuous_sqrt.comp continuous_abs))).div
          (by fun_prop) (fun x => by positivity)
    exact this.aestronglyMeasurable
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with x
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hxsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hgrow := sqrt_growth_le hA hB (abs_nonneg x)
  have hbpos : (0 : ℝ) < (1 + |x|) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hnn : (0 : ℝ) ≤ A + B * Real.sqrt |x| := by positivity
  have hnormrw : (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) = ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
  rw [Real.norm_eq_abs, hnormrw, gammaMajorant, abs_div, abs_of_pos hpos,
    abs_of_nonneg hnn, div_le_iff₀ hpos]
  have hkey : (A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2)
      ≤ 8 * (A + B) * (1 + x ^ 2) := by rw [← hxsq]; exact hgrow
  have hinv : (0 : ℝ) < ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by positivity
  have h' := mul_le_mul_of_nonneg_right hkey hinv.le
  calc A + B * Real.sqrt |x|
      = (A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2)
          * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by field_simp
    _ ≤ 8 * (A + B) * (1 + x ^ 2) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := h'
    _ = 8 * (A + B) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ * (1 + x ^ 2) := by ring

/-- The absolute constant carried by the gamma bracket. -/
def gammaTailConstant (A B : ℝ) : ℝ := ∫ x : ℝ, gammaMajorant A B x

theorem gammaTailConstant_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ gammaTailConstant A B := by
  refine integral_nonneg (fun x => ?_)
  unfold gammaMajorant
  positivity

/-! ## The factorised gamma budget -/

/-- **The `L¹` norm of the gamma integrand factorises**: the taper enters only
through its strip constant. -/
theorem integral_abs_gammaIntegrand_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t s : ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : ∀ x : ℝ, |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x|) :
    (∫ x : ℝ, |gammaIntegrand g t s x|)
      ≤ stripConst (sampleTest g t s) Λ * gammaTailConstant A B := by
  set M : ℝ := stripConst (sampleTest g t s) Λ with hM
  have hM0 : 0 ≤ M := stripConst_nonneg _ _
  have hint1 : Integrable (fun x : ℝ => |gammaIntegrand g t s x|) :=
    (integrable_gammaIntegrand hgs hgc heven hsupp hΛ t s).abs
  have hint2 : Integrable (fun x : ℝ => M * gammaMajorant A B x) :=
    (integrable_gammaMajorant hA hB).const_mul M
  have hstep : ∀ x : ℝ, |gammaIntegrand g t s x| ≤ M * gammaMajorant A B x := by
    intro x
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have h1 : |cosFT g (x + s - t)| ≤ M / (1 + x ^ 2) :=
      abs_cosFT_le hgs hgc heven hsupp hΛ t s x
    have h2 : |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x| := hAB x
    have : |gammaIntegrand g t s x| ≤ (M / (1 + x ^ 2)) * (A + B * Real.sqrt |x|) := by
      rw [gammaIntegrand, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |gammaIntegrand g t s x|
        ≤ (M / (1 + x ^ 2)) * (A + B * Real.sqrt |x|) := this
      _ = M * gammaMajorant A B x := by unfold gammaMajorant; field_simp
  have hmono := integral_mono hint1 hint2 hstep
  rwa [integral_const_mul, ← gammaTailConstant] at hmono

/-- **`exists_gamma_budget_linear_in_stripConst` — the gamma budget `B_Γ`.**  There
is an absolute constant `CΓ` such that, for every compactly supported even `C²`
taper supported in `|u| ≤ Λ`, every target ordinate `t` and every sampling radius
`r`, the gamma cone value of the literal Weil balance obeys

    |ℓ(Q_Γ)| ≤ CΓ · (stripConst(k_r, Λ) + stripConst(k_{−r}, Λ)).

The constant depends only on the gamma bracket of the explicit formula — not on
the taper, the ordinate or the radius. -/
theorem exists_gamma_budget_linear_in_stripConst :
    ∃ CΓ : ℝ, 0 ≤ CΓ ∧ ∀ (g : ℝ → ℝ) (Λ t r : ℝ), ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ u, g (-u) = g u) → (∀ u, g u ≠ 0 → |u| ≤ Λ) → 0 ≤ Λ →
      |evenConeFunctional (gammaVec (sampleFam g t r))|
        ≤ CΓ * (stripConst (sampleTest g t r) Λ + stripConst (sampleTest g t (-r)) Λ) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_gammaBracket_bound
  have hc0 : 0 ≤ gammaTailConstant A B := gammaTailConstant_nonneg hA hB
  have hpi : (0 : ℝ) < 2 * π := by positivity
  refine ⟨(1 / (2 * π)) * gammaTailConstant A B, by positivity, ?_⟩
  intro g Λ t r hgs hgc heven hsupp hΛ
  have henv : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ epsGamma g t r :=
    gammaConeEnvelope hgs.continuous hgc heven t r
  have h1 := integral_abs_gammaIntegrand_le hgs hgc heven hsupp hΛ t r hA hB hAB
  have h2 := integral_abs_gammaIntegrand_le hgs hgc heven hsupp hΛ t (-r) hA hB hAB
  have hsum : epsGamma g t r
      ≤ (1 / (2 * π)) * ((stripConst (sampleTest g t r) Λ
          + stripConst (sampleTest g t (-r)) Λ) * gammaTailConstant A B) := by
    unfold epsGamma
    have hnn : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
    have := add_le_add h1 h2
    calc (1 / (2 * π)) * ((∫ x : ℝ, |gammaIntegrand g t r x|)
            + ∫ x : ℝ, |gammaIntegrand g t (-r) x|)
        ≤ (1 / (2 * π)) * (stripConst (sampleTest g t r) Λ * gammaTailConstant A B
            + stripConst (sampleTest g t (-r)) Λ * gammaTailConstant A B) :=
          mul_le_mul_of_nonneg_left this hnn
      _ = (1 / (2 * π)) * ((stripConst (sampleTest g t r) Λ
            + stripConst (sampleTest g t (-r)) Λ) * gammaTailConstant A B) := by ring
  calc |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ epsGamma g t r := henv
    _ ≤ (1 / (2 * π)) * ((stripConst (sampleTest g t r) Λ
          + stripConst (sampleTest g t (-r)) Λ) * gammaTailConstant A B) := hsum
    _ = (1 / (2 * π)) * gammaTailConstant A B
          * (stripConst (sampleTest g t r) Λ + stripConst (sampleTest g t (-r)) Λ) := by ring

end PoleQuotientGammaBudget
end Zeta23Bridge
