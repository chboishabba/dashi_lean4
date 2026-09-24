/-
# The gamma channel at determinant level

The radiuswise envelope bounded the gamma contribution to the two-radius
determinant by

    |Γ(2r)| |A₀(r)| + |Γ(r)| |A₀(2r)|,

which is `O(1)`: it throws away the cancellation between the two radii.  This
module estimates the gamma projective defect

    𝔇_Γ(r) = Γ(2r) A₀(r) - Γ(r) A₀(2r)

directly.

The gamma channel is *not* the cosine transform of an `L¹` weight — its weight is
the gamma bracket, which grows like `√|x|` — so the transport of
`LiteralWeilProjectiveTaper` cannot be applied to it wholesale.  It can, however,
be applied *under the `x`-integral*: for each frequency `x` the two-sample cone
value of the taper transform,

    ĝ(x + s - t) + ĝ(x - s - t) = ∫ 2 g(u) cos((x-t)u) cos(su) du,

*is* a cosine transform in the sampling radius `s` of a fixed compactly supported
weight.  Hence, frequency by frequency,

    [ĝ(y+2r) + ĝ(y-2r)] A₀(r) - [ĝ(y+r) + ĝ(y-r)] A₀(2r) = 2 ĥ_r(y),   h_r = g B_r,

(`cosFT_cone_projective`), and integrating against the gamma bracket gives the
exact identity

    𝔇_Γ(r) = -2 · gammaResp (projTaper g r) t 0                (`gammaProjectiveDefect_eq`).

The Japanese-bracket domination of `LiteralWeilGammaConeBound` — quadratic decay of
the taper transform against square-root growth of the gamma bracket — then bounds
this by the strip constant of the projective taper, which
`LiteralWeilProjectiveStripConstant` shows is `O(r²)`.  So

    |𝔇_Γ(r)| ≤ r² · projStripCoeff g Λ t · C_Γ          (`exists_gammaProjectiveEnvelope`)

with an absolute constant `C_Γ`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilProjectiveStripConstant

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilGammaProjectiveBound

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

/-! ## The two-sample cone value of the taper transform is a cosine transform -/

/-- The fixed weight through which the frequency `y` reads the taper. -/
def coneWeight (g : ℝ → ℝ) (y : ℝ) : ℝ → ℝ := fun u => 2 * (g u * Real.cos (y * u))

theorem coneWeight_continuous {g : ℝ → ℝ} (hg : Continuous g) (y : ℝ) :
    Continuous (coneWeight g y) := by
  unfold coneWeight; fun_prop

theorem coneWeight_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) (y : ℝ) :
    HasCompactSupport (coneWeight g y) := by
  have h : HasCompactSupport (fun u : ℝ => g u * Real.cos (y * u)) := hgc.mul_right
  have hrw : coneWeight g y = fun u : ℝ => (g u * Real.cos (y * u)) * 2 := by
    funext u; unfold coneWeight; ring
  rw [hrw]
  exact h.mul_right

/-- **`cosFT_cone`.**  The two-sample cone value of the taper transform is the
cosine transform, in the sampling radius, of a weight that does not depend on it. -/
theorem cosFT_cone {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (y s : ℝ) :
    cosFT g (y + s) + cosFT g (y - s) = ∫ u : ℝ, coneWeight g y u * Real.cos (s * u) := by
  have hi1 : Integrable (fun u : ℝ => g u * Real.cos ((y + s) * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have hi2 : Integrable (fun u : ℝ => g u * Real.cos ((y - s) * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  unfold cosFT
  rw [← integral_add hi1 hi2]
  congr 1
  funext u
  unfold coneWeight
  rw [show (y + s) * u = y * u + s * u by ring, show (y - s) * u = y * u - s * u by ring,
    Real.cos_add, Real.cos_sub]
  ring

/-- **`cosFT_cone_projective`.**  Frequency by frequency, the two-radius determinant
of the taper transform is the transform of the *projective* taper. -/
theorem cosFT_cone_projective {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y r : ℝ) :
    (cosFT g (y + 2 * r) + cosFT g (y - 2 * r)) * evenResp g 0 r
        - (cosFT g (y + r) + cosFT g (y - r)) * evenResp g 0 (2 * r)
      = 2 * cosFT (projTaper g r) y := by
  have hFc : Continuous (coneWeight g y) := coneWeight_continuous hg y
  have hFk : HasCompactSupport (coneWeight g y) := coneWeight_hasCompactSupport hgc y
  rw [cosFT_cone hg hgc y (2 * r), cosFT_cone hg hgc y r, cosineChannelProjective hFc hFk g r]
  calc (∫ u : ℝ, coneWeight g y u * twoRadiusBracket g r u)
      = ∫ u : ℝ, 2 * (projTaper g r u * Real.cos (y * u)) := by
        congr 1
        funext u
        unfold coneWeight projTaper
        ring
    _ = 2 * ∫ u : ℝ, projTaper g r u * Real.cos (y * u) := integral_const_mul _ _
    _ = 2 * cosFT (projTaper g r) y := rfl

/-! ## The exact projective identity for the gamma channel -/

/-- The pointwise (in the frequency `x`) determinant identity for the gamma
integrand. -/
theorem gammaIntegrand_projective {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (t r x : ℝ) :
    evenResp g 0 r * (gammaIntegrand g t (2 * r) x + gammaIntegrand g t (-(2 * r)) x)
        - evenResp g 0 (2 * r) * (gammaIntegrand g t r x + gammaIntegrand g t (-r) x)
      = 2 * gammaIntegrand (projTaper g r) t 0 x := by
  have hkey := cosFT_cone_projective hg hgc (x - t) r
  unfold gammaIntegrand
  rw [show x + 2 * r - t = x - t + 2 * r by ring, show x + -(2 * r) - t = x - t - 2 * r by ring,
    show x + r - t = x - t + r by ring, show x + -r - t = x - t - r by ring,
    show x + 0 - t = x - t by ring]
  linear_combination Zeta23.EF.gammaBracket x * hkey

/-- **`gammaCone_projective`.**  The two-radius determinant of the two-sample gamma
cone value is that value read at sampling radius `0`, for the projective taper. -/
theorem gammaCone_projective {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    (gammaResp g t (2 * r) + gammaResp g t (-(2 * r))) * evenResp g 0 r
        - (gammaResp g t r + gammaResp g t (-r)) * evenResp g 0 (2 * r)
      = 2 * gammaResp (projTaper g r) t 0 := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hhd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hhc : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hhe : ∀ u, projTaper g r (-u) = projTaper g r u := projTaper_even heven r
  have hhs : ∀ u, projTaper g r u ≠ 0 → |u| ≤ Λ := projTaper_support hsupp r
  have i1 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t (2 * r)
  have i2 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t (-(2 * r))
  have i3 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t r
  have i4 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t (-r)
  have i5 := integrable_gammaIntegrand hhd hhc hhe hhs hΛ t 0
  have iA : Integrable (fun x : ℝ =>
      evenResp g 0 r * (gammaIntegrand g t (2 * r) x + gammaIntegrand g t (-(2 * r)) x)) :=
    (i1.add i2).const_mul _
  have iB : Integrable (fun x : ℝ =>
      evenResp g 0 (2 * r) * (gammaIntegrand g t r x + gammaIntegrand g t (-r) x)) :=
    (i3.add i4).const_mul _
  have hsplit : (∫ x : ℝ,
        (evenResp g 0 r * (gammaIntegrand g t (2 * r) x + gammaIntegrand g t (-(2 * r)) x)
          - evenResp g 0 (2 * r) * (gammaIntegrand g t r x + gammaIntegrand g t (-r) x)))
      = evenResp g 0 r * ((∫ x : ℝ, gammaIntegrand g t (2 * r) x)
            + ∫ x : ℝ, gammaIntegrand g t (-(2 * r)) x)
        - evenResp g 0 (2 * r) * ((∫ x : ℝ, gammaIntegrand g t r x)
            + ∫ x : ℝ, gammaIntegrand g t (-r) x) := by
    rw [integral_sub iA iB, integral_const_mul, integral_const_mul, integral_add i1 i2,
      integral_add i3 i4]
  have hcong : (∫ x : ℝ,
        (evenResp g 0 r * (gammaIntegrand g t (2 * r) x + gammaIntegrand g t (-(2 * r)) x)
          - evenResp g 0 (2 * r) * (gammaIntegrand g t r x + gammaIntegrand g t (-r) x)))
      = ∫ x : ℝ, 2 * gammaIntegrand (projTaper g r) t 0 x := by
    congr 1
    funext x
    exact gammaIntegrand_projective hgs.continuous hgc t r x
  rw [hcong, integral_const_mul] at hsplit
  unfold gammaIntegrand at hsplit
  unfold gammaResp
  linear_combination (-(1 / (2 * π))) * hsplit

/-- **`gammaProjectiveDefect_eq`.**  The gamma projective defect is minus twice the
gamma response of the projective taper at sampling radius `0`. -/
theorem gammaProjectiveDefect_eq {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    gammaProjectiveDefect g t r = -2 * gammaResp (projTaper g r) t 0 := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hkey := gammaCone_projective hgs heven hsupp hΛ t r
  unfold gammaProjectiveDefect channelProjectiveDefect gammaChannel
  rw [gammaConeValue_exact hgs.continuous hgc heven t (2 * r),
    gammaConeValue_exact hgs.continuous hgc heven t r]
  linarith [hkey]

/-! ## The quadratic envelope -/

/-- The pointwise Japanese-bracket domination of the gamma integrand, with the
growth constants of the gamma bracket as explicit parameters. -/
theorem abs_gammaIntegrand_le {g : ℝ → ℝ} {Λ A B : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : ∀ x : ℝ, |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x|) (t s x : ℝ) :
    |gammaIntegrand g t s x|
      ≤ stripConst (sampleTest g t s) Λ * (8 * (A + B)) * (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) := by
  set M : ℝ := stripConst (sampleTest g t s) Λ with hM
  have hM0 : 0 ≤ M := stripConst_nonneg _ _
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : |cosFT g (x + s - t)| ≤ M / (1 + x ^ 2) :=
    abs_cosFT_le hgs hgc heven hsupp hΛ t s x
  have h2 : |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x| := hAB x
  have hstep : |gammaIntegrand g t s x| ≤ (M / (1 + x ^ 2)) * (A + B * Real.sqrt |x|) := by
    rw [gammaIntegrand, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hgrow := sqrt_growth_le hA hB (abs_nonneg x)
  have hxsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hnormrw : (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) = ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
  have hbpos : (0 : ℝ) < (1 + |x|) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [hnormrw]
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hkey : (A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2)
      ≤ 8 * (A + B) * (1 + x ^ 2) := by rw [← hxsq]; exact hgrow
  have hinv0 : (0 : ℝ) < ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by positivity
  have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hM0) hinv0.le
  calc M * (A + B * Real.sqrt |x|)
      = M * ((A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2))
          * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by field_simp
    _ ≤ M * (8 * (A + B) * (1 + x ^ 2)) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := h'
    _ = M * (8 * (A + B)) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ * (1 + x ^ 2) := by ring

theorem integrable_japanese : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-((3 : ℝ) / 2))) := by
  refine integrable_one_add_norm ?_
  simp [Module.finrank_self]
  norm_num

/-- The `L¹` norm of the gamma integrand is controlled by the strip constant. -/
theorem integral_abs_gammaIntegrand_le {g : ℝ → ℝ} {Λ A B : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : ∀ x : ℝ, |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x|) (t s : ℝ) :
    (∫ x : ℝ, |gammaIntegrand g t s x|)
      ≤ stripConst (sampleTest g t s) Λ * (8 * (A + B))
          * ∫ x : ℝ, (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) := by
  have hL : Integrable (fun x : ℝ => |gammaIntegrand g t s x|) :=
    (integrable_gammaIntegrand hgs hgc heven hsupp hΛ t s).abs
  have hR : Integrable (fun x : ℝ =>
      stripConst (sampleTest g t s) Λ * (8 * (A + B)) * (1 + ‖x‖) ^ (-((3 : ℝ) / 2))) :=
    integrable_japanese.const_mul _
  calc (∫ x : ℝ, |gammaIntegrand g t s x|)
      ≤ ∫ x : ℝ, stripConst (sampleTest g t s) Λ * (8 * (A + B))
          * (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) :=
        integral_mono hL hR
          (fun x => abs_gammaIntegrand_le hgs hgc heven hsupp hΛ hA hB hAB t s x)
    _ = stripConst (sampleTest g t s) Λ * (8 * (A + B))
          * ∫ x : ℝ, (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) := integral_const_mul _ _

/-- **`exists_gammaProjectiveEnvelope`.**  There is an absolute constant `C_Γ` for
which the gamma projective defect of *every* admissible taper is `O(r²)`.  The
radiuswise envelope `|Γ(2r)||A₀(r)| + |Γ(r)||A₀(2r)|` is only `O(1)`. -/
theorem exists_gammaProjectiveEnvelope :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ}, ContDiff ℝ 2 g → (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) → 0 ≤ Λ → ∀ t r : ℝ,
          |gammaProjectiveDefect g t r| ≤ r ^ 2 * (projStripCoeff g Λ t * CG) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_gammaBracket_bound
  set J : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-((3 : ℝ) / 2)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  refine ⟨(1 / π) * (8 * (A + B) * J), by positivity, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hhd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hhc : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hhe : ∀ u, projTaper g r (-u) = projTaper g r u := projTaper_even heven r
  have hhs : ∀ u, projTaper g r u ≠ 0 → |u| ≤ Λ := projTaper_support hsupp r
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hstrip := stripConst_projTaper_le hgs hsupp hΛ t r
  have hstrip0 : 0 ≤ stripConst (sampleTest (projTaper g r) t 0) Λ := stripConst_nonneg _ _
  have hL1 := integral_abs_gammaIntegrand_le hhd hhc hhe hhs hΛ hA hB hAB t 0
  have habs := abs_gammaResp_le (projTaper g r) t 0
  have hid := gammaProjectiveDefect_eq hgs heven hsupp hΛ t r
  have hbase : |gammaProjectiveDefect g t r| = 2 * |gammaResp (projTaper g r) t 0| := by
    rw [hid, abs_mul]
    norm_num
  have hchain : |gammaProjectiveDefect g t r|
      ≤ 2 * ((1 / (2 * π)) * (stripConst (sampleTest (projTaper g r) t 0) Λ
          * (8 * (A + B)) * J)) := by
    rw [hbase]
    have hstep : (1 / (2 * π)) * (∫ x : ℝ, |gammaIntegrand (projTaper g r) t 0 x|)
        ≤ (1 / (2 * π)) * (stripConst (sampleTest (projTaper g r) t 0) Λ
            * (8 * (A + B)) * J) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    linarith [habs, hstep]
  have hfin : 2 * ((1 / (2 * π)) * (stripConst (sampleTest (projTaper g r) t 0) Λ
        * (8 * (A + B)) * J))
      ≤ 2 * ((1 / (2 * π)) * ((r ^ 2 * projStripCoeff g Λ t) * (8 * (A + B)) * J)) := by
    have hc : (0 : ℝ) ≤ 8 * (A + B) * J := by positivity
    have h1 : stripConst (sampleTest (projTaper g r) t 0) Λ * (8 * (A + B)) * J
        ≤ (r ^ 2 * projStripCoeff g Λ t) * (8 * (A + B)) * J := by
      have := mul_le_mul_of_nonneg_right hstrip hc
      nlinarith [this]
    have h2 : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
    nlinarith [h1, h2]
  have heq : 2 * ((1 / (2 * π)) * ((r ^ 2 * projStripCoeff g Λ t) * (8 * (A + B)) * J))
      = r ^ 2 * (projStripCoeff g Λ t * ((1 / π) * (8 * (A + B) * J))) := by
    field_simp
  linarith [hchain, hfin, heq.le, heq.ge]

end LiteralWeilGammaProjectiveBound
end Zeta23Bridge
