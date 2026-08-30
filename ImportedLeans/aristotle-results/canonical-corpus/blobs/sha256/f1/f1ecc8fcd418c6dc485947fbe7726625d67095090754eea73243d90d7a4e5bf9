/-
# The gamma channel in the even cone: an exact value and a finite envelope

Step 4 of the programme.  `LiteralWeilOffOrdinateTail.lean` left the balance in the
form

    0 < ℓ(Q_cluster) ≤ ε_zero + |ℓ(Q_prime)| + |ℓ(Q_Γ)|.

The gamma channel is deterministic, and this module treats it accordingly.

* `gammaConeValue_exact` — **not** a norm estimate but an identity: the even cone
  functional reads the gamma channel as exactly

      ℓ(Q_Γ) = -(gammaResp g t r + gammaResp g t (-r)) = -2 · gammaEvenResp g t r,

  the two-point symmetrisation of the taper-smoothed gamma bracket.

* `integrable_gammaIntegrand` — the smoothed bracket really is an absolutely
  convergent integral.  This combines two decays: the companion's `[eq:hfbound]`
  gives `|ĝ(x + s - t)| ≤ C/(1 + x²)` (the strip envelope at a *real* point), and
  the companion's unconditional `Zeta23.gammaFacts` — whose Stirling clause is
  proved, not assumed — gives `|Γ-bracket(x)| ≤ A + B√|x|`.  Their product is
  dominated by the Japanese bracket `(1 + |x|)^{-3/2}`.

* `gammaConeEnvelope` — hence `|ℓ(Q_Γ)| ≤ ε_Γ(g, t, r)` with the explicit

      ε_Γ = (1/2π) ( ∫ |ĝ(x + r - t) Γ-bracket(x)| dx
                     + ∫ |ĝ(x - r - t) Γ-bracket(x)| dx ),

  a genuinely finite number by the integrability above.

* `clusterConeBoundedByPrimeChannel` — the sharpened balance

      0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + ε_Γ(g, t, r)
                          + |ℓ(Q_prime)|,

  in which the only uncontrolled channel left is the prime one.

**What is not claimed.**  Neither `ε_zero` nor `ε_Γ` is shown to be small compared
with `ℓ(Q_cluster)`.  They are explicit finite envelopes, nothing more.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateTail
import Zeta23Bridge.LiteralWeilGammaChannel
import Zeta23.GammaFacts.Complete

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilGammaConeBound

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail

/-! ## The gamma bracket has at most square-root growth -/

/-- The explicit-formula gamma bracket is `2π` times the companion's `μ`. -/
theorem gammaBracket_eq_mu (x : ℝ) : Zeta23.EF.gammaBracket x = 2 * π * Zeta23.mu x := by
  unfold Zeta23.EF.gammaBracket Zeta23.mu
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp

theorem continuous_gammaBracket : Continuous Zeta23.EF.gammaBracket := by
  have h : Zeta23.EF.gammaBracket = fun x => 2 * π * Zeta23.mu x := funext gammaBracket_eq_mu
  rw [h]
  exact continuous_const.mul (Zeta23.gammaFacts).smooth.continuous

/-- **Square-root growth of the gamma bracket.**  Off a compact set this is the
Stirling clause of the companion's *proved* `Zeta23.gammaFacts` (`|μ(x) −
log(|x|/2π)/2π| ≤ C/x²`) together with `log y ≤ 2√y`; on the compact set it is
continuity.  No numerical input. -/
theorem exists_gammaBracket_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ x : ℝ, |Zeta23.EF.gammaBracket x| ≤ A + B * Real.sqrt |x| := by
  obtain ⟨C, hC⟩ := (Zeta23.gammaFacts).stirling
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := Zeta23.EF.gammaBracket) continuous_gammaBracket.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0 (by norm_num))
  have hpi : (1 : ℝ) < 2 * π := by nlinarith [Real.pi_gt_three]
  have hlog2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg hpi.le
  have hpi0 : (0 : ℝ) < 2 * π := by linarith
  refine ⟨M₀ + 2 * π * |C| + Real.log (2 * π), 2, by positivity, by norm_num, fun x => ?_⟩
  rcases le_or_gt |x| 1 with hx | hx
  · have hmem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    have := hM₀ x hmem
    rw [Real.norm_eq_abs] at this
    have : |Zeta23.EF.gammaBracket x| ≤ M₀ := this
    nlinarith [Real.sqrt_nonneg |x|, abs_nonneg C]
  · -- |x| > 1
    have hx1 : (1 : ℝ) ≤ |x| := hx.le
    have hxsq : (1 : ℝ) ≤ x ^ 2 := by nlinarith [sq_abs x]
    have hst := hC x hx1
    -- log |x| ≤ 2 √|x|
    have hlog : Real.log |x| ≤ 2 * Real.sqrt |x| := by
      have h := Real.log_le_rpow_div (x := |x|) (abs_nonneg x) (by norm_num : (0:ℝ) < 1 / 2)
      rw [Real.sqrt_eq_rpow]
      linarith [h]
    have hlognn : 0 ≤ Real.log |x| := Real.log_nonneg hx1
    -- | log (|x| / 2π) | ≤ log |x| + log 2π
    have hdiv : Real.log (|x| / (2 * π)) = Real.log |x| - Real.log (2 * π) := by
      rw [Real.log_div (by positivity) (ne_of_gt hpi0)]
    have habslog : |Real.log (|x| / (2 * π))| ≤ Real.log |x| + Real.log (2 * π) := by
      rw [hdiv, abs_le]; constructor <;> linarith
    -- C / x² ≤ |C|
    have hCx : C / x ^ 2 ≤ |C| := by
      have h1 : C ≤ |C| := le_abs_self C
      rcases le_or_gt C 0 with h | h
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg h (by positivity)) (abs_nonneg C)
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hmu : |Zeta23.mu x| ≤ |C| + (1 / (2 * π)) * (Real.log |x| + Real.log (2 * π)) := by
      have h1 : |Zeta23.mu x| ≤ |Zeta23.mu x - (1 / (2 * π)) * Real.log (|x| / (2 * π))|
          + |(1 / (2 * π)) * Real.log (|x| / (2 * π))| := by
        have := abs_add_le (Zeta23.mu x - (1 / (2 * π)) * Real.log (|x| / (2 * π)))
          ((1 / (2 * π)) * Real.log (|x| / (2 * π)))
        simpa using this
      have h2 : |(1 / (2 * π)) * Real.log (|x| / (2 * π))|
          ≤ (1 / (2 * π)) * (Real.log |x| + Real.log (2 * π)) := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
        exact mul_le_mul_of_nonneg_left habslog (by positivity)
      linarith [hst.trans hCx]
    have hgb : |Zeta23.EF.gammaBracket x| = 2 * π * |Zeta23.mu x| := by
      rw [gammaBracket_eq_mu, abs_mul, abs_of_pos hpi0]
    rw [hgb]
    have hfac : 2 * π * ((1 / (2 * π)) * (Real.log |x| + Real.log (2 * π)))
        = Real.log |x| + Real.log (2 * π) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hmu hpi0.le]

/-! ## The strip envelope of the taper on the real axis -/

/-- The cosine transform is continuous. -/
theorem continuous_cosFT {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (cosFT g) := by
  refine continuous_of_dominated (bound := fun u => |g u|) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact ((hg.mul (by fun_prop)).aestronglyMeasurable)
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (g u), Real.abs_cos_le_one (x * u), abs_nonneg (Real.cos (x * u))]
  · exact hg.abs.integrable_of_hasCompactSupport hgc.abs
  · filter_upwards with u; fun_prop

/-- **The taper decays quadratically on the real axis**, by the strip envelope of
the companion's `[eq:hfbound]` applied at a real point. -/
theorem abs_cosFT_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t s x : ℝ) :
    |cosFT g (x + s - t)| ≤ stripConst (sampleTest g t s) Λ / (1 + x ^ 2) := by
  have h := norm_paperFT_le_stripConst_div (sampleTest_contDiff hgs t s)
    (sampleTest_hasCompactSupport hgc t s) (sampleTest_support_radius hsupp t s) hΛ
    (z := (x : ℂ)) (by simp)
  rw [paperFT_sampleTest_real hgs.continuous hgc heven] at h
  have hns : Complex.normSq ((x : ℝ) : ℂ) = x ^ 2 := by
    rw [Complex.normSq_ofReal]; ring
  rwa [Complex.norm_real, Real.norm_eq_abs, hns] at h

/-! ## The Japanese-bracket domination -/

theorem pow_le_one_add_pow_four {s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ 4) :
    s ^ k ≤ 1 + s ^ 4 := by
  rcases le_or_gt s 1 with h | h
  · have : s ^ k ≤ 1 := pow_le_one₀ hs h
    nlinarith [pow_nonneg hs 4]
  · have : s ^ k ≤ s ^ 4 := pow_le_pow_right₀ h.le hk
    linarith

/-- The elementary inequality behind the domination: `(A + B√y)(1 + y)^{3/2} ≤
8(A+B)(1 + y²)`. -/
theorem sqrt_growth_le {A B y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : 0 ≤ y) :
    (A + B * Real.sqrt y) * (1 + y) ^ ((3 : ℝ) / 2) ≤ 8 * (A + B) * (1 + y ^ 2) := by
  set s : ℝ := Real.sqrt y with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg y
  have hs2 : s ^ 2 = y := Real.sq_sqrt hy
  have hs4 : s ^ 4 = y ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs2]
  have hcube : (1 + y) ^ ((3 : ℝ) / 2) ≤ (1 + s) ^ 3 := by
    have h1 : (1 : ℝ) + y ≤ (1 + s) ^ 2 := by nlinarith
    have h2 : ((1 + s) ^ 2 : ℝ) ^ ((3 : ℝ) / 2) = (1 + s) ^ 3 := by
      rw [← Real.rpow_natCast (1 + s) 2, ← Real.rpow_mul (by linarith),
        show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + y) ^ ((3 : ℝ) / 2)
        ≤ ((1 + s) ^ 2 : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      _ = (1 + s) ^ 3 := h2
  have hnn : 0 ≤ A + B * s := by positivity
  have hkey : (A + B * s) * (1 + s) ^ 3 ≤ 8 * (A + B) * (1 + s ^ 4) := by
    have h1 : s ^ 1 ≤ 1 + s ^ 4 := pow_le_one_add_pow_four hs (by norm_num)
    have h2 : s ^ 2 ≤ 1 + s ^ 4 := pow_le_one_add_pow_four hs (by norm_num)
    have h3 : s ^ 3 ≤ 1 + s ^ 4 := pow_le_one_add_pow_four hs (by norm_num)
    have h4 : s ^ 4 ≤ 1 + s ^ 4 := pow_le_one_add_pow_four hs (by norm_num)
    simp only [pow_one] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hA,
      mul_le_mul_of_nonneg_left h3 hA, mul_le_mul_of_nonneg_left h1 hB,
      mul_le_mul_of_nonneg_left h2 hB, mul_le_mul_of_nonneg_left h3 hB,
      mul_le_mul_of_nonneg_left h4 hB, pow_nonneg hs 4]
  calc (A + B * s) * (1 + y) ^ ((3 : ℝ) / 2)
      ≤ (A + B * s) * (1 + s) ^ 3 := mul_le_mul_of_nonneg_left hcube hnn
    _ ≤ 8 * (A + B) * (1 + s ^ 4) := hkey
    _ = 8 * (A + B) * (1 + y ^ 2) := by rw [hs4]

/-! ## The gamma integrand -/

/-- The integrand of the gamma term for the sample test at radius `s`. -/
def gammaIntegrand (g : ℝ → ℝ) (t s : ℝ) : ℝ → ℝ :=
  fun x => cosFT g (x + s - t) * Zeta23.EF.gammaBracket x

theorem gammaResp_eq_integral (g : ℝ → ℝ) (t s : ℝ) :
    gammaResp g t s = (1 / (2 * π)) * ∫ x : ℝ, gammaIntegrand g t s x := rfl

theorem continuous_gammaIntegrand {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (t s : ℝ) : Continuous (gammaIntegrand g t s) :=
  ((continuous_cosFT hg hgc).comp (by fun_prop)).mul continuous_gammaBracket

/-- **The gamma integrand is absolutely integrable.**  Quadratic decay of the taper
transform (companion `[eq:hfbound]`) beats the square-root growth of the gamma
bracket (companion `gammaFacts`), with the Japanese bracket `(1+|x|)^{-3/2}` as
the dominating function. -/
theorem integrable_gammaIntegrand {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t s : ℝ) :
    Integrable (gammaIntegrand g t s) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_gammaBracket_bound
  set M : ℝ := stripConst (sampleTest g t s) Λ with hM
  have hM0 : 0 ≤ M := stripConst_nonneg _ _
  set D : ℝ := M * (8 * (A + B)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hdom : Integrable (fun x : ℝ => D * (1 + ‖x‖) ^ (-((3 : ℝ) / 2))) := by
    refine Integrable.const_mul ?_ D
    refine integrable_one_add_norm ?_
    simp [Module.finrank_self]
    norm_num
  refine Integrable.mono' hdom (continuous_gammaIntegrand hgs.continuous hgc t s).aestronglyMeasurable ?_
  filter_upwards with x
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
  rw [Real.norm_eq_abs, hnormrw]
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos, hD]
  have hkey : (A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2)
      ≤ 8 * (A + B) * (1 + x ^ 2) := by rw [← hxsq]; exact hgrow
  have hfin : M * ((A + B * Real.sqrt |x|))
      ≤ M * (8 * (A + B)) * ((1 + x ^ 2) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hkey hM0
    have hinv0 : (0 : ℝ) < ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by positivity
    have h' := mul_le_mul_of_nonneg_right h hinv0.le
    calc M * (A + B * Real.sqrt |x|)
        = M * ((A + B * Real.sqrt |x|) * (1 + |x|) ^ ((3 : ℝ) / 2))
            * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := by
          field_simp
      _ ≤ M * (8 * (A + B) * (1 + x ^ 2)) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ := h'
      _ = M * (8 * (A + B)) * ((1 + x ^ 2) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹) := by ring
  calc M * (A + B * Real.sqrt |x|)
      ≤ M * (8 * (A + B)) * ((1 + x ^ 2) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹) := hfin
    _ = M * (8 * (A + B)) * ((1 + |x|) ^ ((3 : ℝ) / 2))⁻¹ * (1 + x ^ 2) := by ring

/-! ## The gamma channel in the even cone -/

/-- **`gammaConeValue_exact`.**  An identity, not an estimate: the even cone
functional evaluates the gamma channel to minus the two-point symmetrisation of the
smoothed gamma bracket. -/
theorem gammaConeValue_exact {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    evenConeFunctional (gammaVec (sampleFam g t r))
      = -(gammaResp g t r + gammaResp g t (-r)) := by
  have h0 : reim (gammaTerm (sampleTest g t r)) = gammaResp g t r :=
    reim_gammaTerm_sampleTest hg hgc heven t r
  have h1 : reim (gammaTerm (sampleTest g t (-r))) = gammaResp g t (-r) :=
    reim_gammaTerm_sampleTest hg hgc heven t (-r)
  show -reim (gammaTerm (sampleTest g t r)) + -reim (gammaTerm (sampleTest g t (-r)))
      = -(gammaResp g t r + gammaResp g t (-r))
  rw [h0, h1]; ring

/-- **`epsGamma`** — the explicit gamma envelope. -/
def epsGamma (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  (1 / (2 * π)) * ((∫ x : ℝ, |gammaIntegrand g t r x|)
    + ∫ x : ℝ, |gammaIntegrand g t (-r) x|)

theorem abs_gammaResp_le (g : ℝ → ℝ) (t s : ℝ) :
    |gammaResp g t s| ≤ (1 / (2 * π)) * ∫ x : ℝ, |gammaIntegrand g t s x| := by
  rw [gammaResp_eq_integral, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := norm_integral_le_integral_norm (μ := (volume : Measure ℝ)) (gammaIntegrand g t s)
  simpa [Real.norm_eq_abs] using this

/-- **`gammaConeEnvelope`.**  `|ℓ(Q_Γ)| ≤ ε_Γ(g, t, r)`. -/
theorem gammaConeEnvelope {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ epsGamma g t r := by
  rw [gammaConeValue_exact hg hgc heven, abs_neg]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_gammaResp_le g t r
  have h2 := abs_gammaResp_le g t (-r)
  unfold epsGamma
  linarith [h1, h2]

/-! ## The sharpened balance: only the prime channel is uncontrolled -/

/-- **`clusterConeBoundedByPrimeChannel`.**  For an actual nontrivial zero of
`riemannZeta` at a nonzero ordinate, the strictly positive same-ordinate cluster
value is bounded by the off-ordinate envelope, the gamma envelope — both explicit
and, in the gamma case, an absolutely convergent integral — and the prime channel:

    0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + ε_Γ(g, t, r) + |ℓ(Q_prime)|.

The prime channel is the only one left uncontrolled.  Nothing here asserts that the
right-hand side is smaller than the left. -/
theorem clusterConeBoundedByPrimeChannel {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ) ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ Integrable (gammaIntegrand g t r) ∧ Integrable (gammaIntegrand g t (-r))
      ∧ 0 < evenConeFunctional (clusterVec (sampleFam g t r) t)
      ∧ |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ epsZero g Λ t r
      ∧ |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ epsGamma g t r
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ epsZero g Λ t r + epsGamma g t r
            + |evenConeFunctional (primeVec (sampleFam g t r))| := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, -, -, hpole, hA, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  obtain ⟨Λ, hΛ, hsupp⟩ := exists_support_radius hgc
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hpos : 0 < evenConeFunctional (clusterVec (sampleFam g t r) t) :=
    sameOrdinateClusterConePositive hgs hgc heven hA ⟨ρstar, him⟩
  have hoff := offOrdinateConeEnvelope hgs hgc hsupp hΛ t r
  have hgam := gammaConeEnvelope hgs.continuous hgc heven t r
  have hlin : evenConeFunctional (clusterVec (sampleFam g t r) t)
      + evenConeFunctional (offOrdVec (sampleFam g t r) t)
      + evenConeFunctional (primeVec (sampleFam g t r))
      + evenConeFunctional (gammaVec (sampleFam g t r))
      + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  have hpolezero : evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    have hmem := poleVec_mem_poleSpace hgs.continuous hgc heven t r
    simpa using evenConeFunctional_poleSpace_le_ker (g := g) (t := t) (r := r) hpole hmem
  rw [hpolezero, add_zero] at hlin
  refine ⟨g, r, Λ, hgs, hgc, heven, hrpos, hΛ, hsupp, hpole, hA,
    integrable_gammaIntegrand hgs hgc heven hsupp hΛ t r,
    integrable_gammaIntegrand hgs hgc heven hsupp hΛ t (-r), hpos, hoff, hgam, ?_⟩
  have h1 := abs_le.mp hoff
  have h2 := abs_le.mp hgam
  have h3 := neg_abs_le (evenConeFunctional (primeVec (sampleFam g t r)))
  linarith [h1.1, h2.1]

end LiteralWeilGammaConeBound
end Zeta23Bridge
