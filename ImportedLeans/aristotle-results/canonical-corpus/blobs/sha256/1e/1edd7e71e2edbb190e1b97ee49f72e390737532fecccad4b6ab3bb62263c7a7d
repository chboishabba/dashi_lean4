/-
# The pole-quotient complement margin: what the final contradiction really needs

The even-cone / pole-quotient lane of `LiteralWeilPrimeEvenCone.lean` ends in the
unconditional inequality

    0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + ε_Γ(g, t, r),   Q_prime = 0,

for a nontrivial zero of `riemannZeta` at a high ordinate `t`.  The contradiction
architecture that consumes it is *ordered algebra*: with

    D_cluster = ℓ(Q_cluster),  D_off = ℓ(Q_offOrd),  D_Γ = ℓ(Q_Γ),

the literal balance is `D_cluster + D_off + D_Γ = 0`, so any pair of budgets

    |D_off| ≤ B_off,   |D_Γ| ≤ B_Γ

together with a margin `M ≤ D_cluster` and the strict comparison
`B_off + B_Γ < M` is contradictory.  That compiler is `false_of_split_budget`
(generic) and `false_of_evenCone_split_budget` (on the literal channels).

The point of this module is **not** the compiler — it is one line — but the two
exact quantitative constraints the compiler places on the margin, both of which
are proved here for the tapers the programme actually constructs.

## 1. The margin cannot be height-free

The cluster value is read off the fibre as `∑ 2 m_ρ A_{a_ρ}(r)` with
`A_a(r) = ∫ g(u) cosh(au) cos(ru) du` the even response at height `a`.  For a
nonnegative taper whose support lies inside the window `2r|u| < π/2` the even
response is *monotone in the height*: `A_0(r) ≤ A_a(r)`
(`evenResp_zero_le_evenResp`).  Hence the fibre of **any** zero at the ordinate
— on the critical line or not — already forces

    2 A_0(r) ≤ ℓ(Q_cluster) ≤ B_off + B_Γ                (`baseline_le_budget`),

so a margin bounded below by the height-free quantity `2 A_0(r)` cannot be
attained; a proof of one would exclude every zero at that ordinate, including
on-line ones (`no_zero_at_ordinate_of_heightFree_margin`).  The strict comparison
must therefore be paid entirely out of the *height surplus*
`A_a(r) − A_0(r)`.

## 2. The height surplus is quantitatively tiny

For a nonnegative taper supported in `|u| ≤ Λ`,

    A_a(r) − A_0(r) ≤ (cosh(|a|Λ) − 1) ∫ g            (`heightSurplus_le`),

and inside the same window `∫ g ≤ √2 A_0(r)` (`taperMass_le_evenResp_zero`), so

    A_a(r) ≤ A_0(r) (1 + √2 (cosh(|a|Λ) − 1))         (`evenResp_le_baseline_mul`).

The high-ordinate taper of `exists_positive_taper_poleEven_zero` is supported in
`|u| < 9π/(4|t|)`, and every zero of the strip has `|a| ≤ 1/2`, so the surplus
factor is at most `√2 (cosh(9π/(8|t|)) − 1) = O(|t|^{-2})`.  Consequently the
whole cluster value sits in the window

    B_baseline ≤ ℓ(Q_cluster) ≤ (1 + √2(cosh(9π/(8|t|)) − 1)) · B_baseline,
    B_baseline = ∑ 2 m_ρ A_0(r)

(`poleQuotientMarginWindow`).  Any admissible pair of budgets must land in the
half-open interval `[B_baseline, (1 + O(|t|^{-2})) B_baseline)`: the two
complement channels have to be evaluated to *relative* accuracy `O(|t|^{-2})`,
not merely bounded.  That is the exact shape of the remaining obligation for the
off-ordinate and gamma budgets in this lane.

Nothing here asserts that such budgets exist, and nothing here weakens or assumes
the Riemann Hypothesis.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilPrimeEvenCone

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace PoleQuotientComplementMargin

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone

/-! ## 1. The split-budget contradiction compiler -/

/-- **The compiler, generically.**  A balanced triple whose two complement
channels are paid by budgets summing strictly below a lower bound for the first
channel is contradictory.  Pure ordered algebra: no analytic content, and no
analytic estimate is manufactured. -/
theorem false_of_split_budget {Dcluster Doff Dgamma Boff Bgamma M : ℝ}
    (hbal : Dcluster + Doff + Dgamma = 0) (hM : M ≤ Dcluster)
    (hoff : |Doff| ≤ Boff) (hgamma : |Dgamma| ≤ Bgamma)
    (hmargin : Boff + Bgamma < M) : False := by
  have h1 := (abs_le.mp hoff).1
  have h2 := (abs_le.mp hgamma).1
  linarith

/-! ## 2. The literal three-channel balance of the even cone -/

/-- **The literal balance in the even cone, once the prime channel vanishes.**
The pole channel is killed by the parity quotient (`poleEvenResp g t r = 0`), so
the cluster, off-ordinate and gamma cone values sum to zero. -/
theorem evenCone_three_channel_balance {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0) :
    evenConeFunctional (clusterVec (sampleFam g t r) t)
      + evenConeFunctional (offOrdVec (sampleFam g t r) t)
      + evenConeFunctional (gammaVec (sampleFam g t r)) = 0 := by
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hlin : evenConeFunctional (clusterVec (sampleFam g t r) t)
      + evenConeFunctional (offOrdVec (sampleFam g t r) t)
      + evenConeFunctional (primeVec (sampleFam g t r))
      + evenConeFunctional (gammaVec (sampleFam g t r))
      + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  have hpolezero : evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    have hmem := poleVec_mem_poleSpace hgs.continuous hgc heven t r
    simpa using evenConeFunctional_poleSpace_le_ker (g := g) (t := t) (r := r) hpole hmem
  have hprimezero : evenConeFunctional (primeVec (sampleFam g t r)) = 0 := by
    rw [hprime, map_zero]
  rw [hpolezero, hprimezero, add_zero, add_zero] at hlin
  exact hlin

/-- **The compiler on the literal channels.** -/
theorem false_of_evenCone_split_budget {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma M : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (hM : M ≤ evenConeFunctional (clusterVec (sampleFam g t r) t))
    (hmargin : Boff + Bgamma < M) : False :=
  false_of_split_budget (evenCone_three_channel_balance hgs hgc heven hpole hprime)
    hM hoff hgamma hmargin

/-- **The cluster value never exceeds the complement budget.**  This is the
inequality the compiler contradicts; it holds for every taper for which the pole
and prime channels vanish. -/
theorem clusterValue_le_budget {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma) :
    evenConeFunctional (clusterVec (sampleFam g t r) t) ≤ Boff + Bgamma := by
  have hbal := evenCone_three_channel_balance hgs hgc heven hpole hprime
  have h1 := (abs_le.mp hoff).1
  have h2 := (abs_le.mp hgamma).1
  linarith

/-! ## 3. The height-free baseline and the height surplus of the even response -/

/-- Inside the sampling window the base cosine factor is nonnegative. -/
theorem cos_nonneg_of_window {r u : ℝ} (hr : 0 < r) (hu : 2 * r * |u| < π / 2) :
    0 ≤ Real.cos (r * u) := by
  have habs : |r * u| < π / 2 := by
    rw [abs_mul, abs_of_pos hr]
    nlinarith [abs_nonneg u, mul_nonneg hr.le (abs_nonneg u)]
  have h := abs_lt.mp habs
  exact Real.cos_nonneg_of_mem_Icc ⟨h.1.le, h.2.le⟩

/-- Inside the sampling window the base cosine factor is at least `√2/2`. -/
theorem cos_ge_of_window {r u : ℝ} (hr : 0 < r) (hu : 2 * r * |u| < π / 2) :
    Real.sqrt 2 / 2 ≤ Real.cos (r * u) := by
  have hpi := Real.pi_pos
  have habs : |r * u| ≤ π / 4 := by
    rw [abs_mul, abs_of_pos hr]
    nlinarith [abs_nonneg u, mul_nonneg hr.le (abs_nonneg u)]
  have hmono : Real.cos (π / 4) ≤ Real.cos |r * u| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
  have hcos : Real.cos |r * u| = Real.cos (r * u) := by
    rcases abs_cases (r * u) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Real.cos_neg]
  rw [Real.cos_pi_div_four] at hmono
  rwa [hcos] at hmono

/-- The even-response integrand is integrable for a continuous compactly
supported taper. -/
theorem evenResp_integrable {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y s : ℝ) : Integrable (fun u : ℝ => g u * (Real.cosh (y * u) * Real.cos (s * u))) :=
  taper_integrable hg hgc (by fun_prop)

/-- **Height monotonicity of the even response.**  For a nonnegative taper
supported inside the sampling window, the response at height `a` is at least the
response on the critical line.  This is what makes the cluster value *height
blind* from below. -/
theorem evenResp_zero_le_evenResp {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (a : ℝ) :
    evenResp g 0 r ≤ evenResp g a r := by
  refine integral_mono (evenResp_integrable hg hgc 0 r) (evenResp_integrable hg hgc a r)
    (fun u => ?_)
  by_cases hgu : g u = 0
  · simp [hgu]
  · have hc : 0 ≤ Real.cos (r * u) := cos_nonneg_of_window hr (hwin u hgu)
    have h1 : Real.cosh (0 * u) = 1 := by rw [zero_mul, Real.cosh_zero]
    have h2 : (1 : ℝ) ≤ Real.cosh (a * u) := Real.one_le_cosh _
    have hgu' : 0 ≤ g u := hnn u
    rw [h1]
    have : (1 : ℝ) * Real.cos (r * u) ≤ Real.cosh (a * u) * Real.cos (r * u) :=
      mul_le_mul_of_nonneg_right h2 hc
    exact mul_le_mul_of_nonneg_left this hgu'

/-- **The height surplus is at most the taper mass times `cosh(|a|Λ) − 1`.** -/
theorem heightSurplus_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (a r : ℝ) :
    evenResp g a r - evenResp g 0 r ≤ (Real.cosh (|a| * Λ) - 1) * ∫ u : ℝ, g u := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hsub : evenResp g a r - evenResp g 0 r
      = ∫ u : ℝ, (g u * (Real.cosh (a * u) * Real.cos (r * u))
          - g u * (Real.cosh (0 * u) * Real.cos (r * u))) := by
    simp only [evenResp]
    rw [← integral_sub (evenResp_integrable hg hgc a r) (evenResp_integrable hg hgc 0 r)]
  have hmass : (Real.cosh (|a| * Λ) - 1) * ∫ u : ℝ, g u
      = ∫ u : ℝ, g u * (Real.cosh (|a| * Λ) - 1) := by
    rw [integral_mul_const]; ring
  rw [hsub, hmass]
  refine integral_mono
    (((evenResp_integrable hg hgc a r).sub (evenResp_integrable hg hgc 0 r)))
    (hint.mul_const _) (fun u => ?_)
  by_cases hgu : g u = 0
  · simp [hgu]
  · have hgu' : 0 ≤ g u := hnn u
    have hΛ : |u| ≤ Λ := hsupp u hgu
    have h1 : Real.cosh (0 * u) = 1 := by rw [zero_mul, Real.cosh_zero]
    have hch : (1 : ℝ) ≤ Real.cosh (a * u) := Real.one_le_cosh _
    have hmono : Real.cosh (a * u) ≤ Real.cosh (|a| * Λ) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_abs]
      have h0 : (0 : ℝ) ≤ |a| := abs_nonneg a
      have hΛ0 : (0 : ℝ) ≤ |Λ| := abs_nonneg Λ
      have : |u| ≤ |Λ| := le_trans hΛ (le_abs_self Λ)
      exact mul_le_mul_of_nonneg_left this h0
    have hcosle : Real.cos (r * u) ≤ 1 := Real.cos_le_one _
    have hcosge : (-1 : ℝ) ≤ Real.cos (r * u) := Real.neg_one_le_cos _
    rw [h1, one_mul]
    have hfac : Real.cosh (a * u) * Real.cos (r * u) - Real.cos (r * u)
        ≤ Real.cosh (|a| * Λ) - 1 := by
      nlinarith [hch, hmono, hcosle, hcosge]
    nlinarith [hgu', hfac]

/-- **The taper mass is controlled by the height-free baseline response.**
Inside the sampling window the base cosine factor is at least `√2/2`. -/
theorem taperMass_le_evenResp_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) :
    (∫ u : ℝ, g u) ≤ Real.sqrt 2 * evenResp g 0 r := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : (∫ u : ℝ, g u * (Real.sqrt 2 / 2)) ≤ evenResp g 0 r := by
    refine integral_mono (hint.mul_const _) (evenResp_integrable hg hgc 0 r) (fun u => ?_)
    by_cases hgu : g u = 0
    · simp [hgu]
    · have hgu' : 0 ≤ g u := hnn u
      have hc : Real.sqrt 2 / 2 ≤ Real.cos (r * u) := cos_ge_of_window hr (hwin u hgu)
      have h1 : Real.cosh (0 * u) = 1 := by rw [zero_mul, Real.cosh_zero]
      rw [h1, one_mul]
      exact mul_le_mul_of_nonneg_left hc hgu'
  rw [integral_mul_const] at hkey
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 2 * ((∫ u : ℝ, g u) * (Real.sqrt 2 / 2))
      ≤ Real.sqrt 2 * evenResp g 0 r := mul_le_mul_of_nonneg_left hkey hs2.le
  have h4 : Real.sqrt 2 * ((∫ u : ℝ, g u) * (Real.sqrt 2 / 2)) = ∫ u : ℝ, g u := by
    have hrw : Real.sqrt 2 * ((∫ u : ℝ, g u) * (Real.sqrt 2 / 2))
        = (Real.sqrt 2 * Real.sqrt 2) / 2 * ∫ u : ℝ, g u := by ring
    rw [hrw, hmul]; ring
  linarith

/-- **The relative height window.**  The even response at any height exceeds the
height-free baseline by a *relative* factor at most `√2 (cosh(|a|Λ) − 1)`. -/
theorem evenResp_le_baseline_mul {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {Λ r : ℝ} (hr : 0 < r)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (a : ℝ) :
    evenResp g a r ≤ evenResp g 0 r * (1 + Real.sqrt 2 * (Real.cosh (|a| * Λ) - 1)) := by
  have h1 := heightSurplus_le hg hgc hnn hsupp a r
  have h2 := taperMass_le_evenResp_zero hg hgc hnn hr hwin
  have hch : (0 : ℝ) ≤ Real.cosh (|a| * Λ) - 1 := by
    have := Real.one_le_cosh (|a| * Λ); linarith
  nlinarith [h1, h2, hch]

/-- Every zero of the critical strip is at distance at most `1/2` from the
critical line. -/
theorem abs_heightOf_le_half (ρ : Zeros) : |heightOf ρ| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := (Zeta23.zetaZeroConfig).strip (ρ : ℂ) ρ.2
  unfold heightOf
  rw [abs_le]
  constructor <;> linarith

/-- The height-free baseline response of a nonnegative taper is nonnegative. -/
theorem evenResp_zero_nonneg {g : ℝ → ℝ}
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) : 0 ≤ evenResp g 0 r := by
  have hint : (0 : ℝ) ≤ ∫ u : ℝ, g u * (Real.cosh (0 * u) * Real.cos (r * u)) := by
    refine integral_nonneg (fun u => ?_)
    by_cases hgu : g u = 0
    · simp [hgu]
    · have hc : 0 ≤ Real.cos (r * u) := cos_nonneg_of_window hr (hwin u hgu)
      have h1 : Real.cosh (0 * u) = 1 := by rw [zero_mul, Real.cosh_zero]
      rw [h1, one_mul]
      exact mul_nonneg (hnn u) hc
  simpa [evenResp] using hint

/-! ## 4. The margin cannot be height-free -/

/-- **The height-free baseline is already paid by the complement budget.**  For a
zero at the target ordinate — on the critical line or not — the cluster value is
at least `2 A_0(r)`, hence so is any admissible complement budget. -/
theorem baseline_le_budget {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u) {t r : ℝ} (hr : 0 < r)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hA : ∀ a : ℝ, 0 < evenResp g a r)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (ρ : SameOrd t) :
    2 * evenResp g 0 r ≤ Boff + Bgamma := by
  have hcl : coneWeight g r (ρ : Zeros)
      ≤ evenConeFunctional (clusterVec (sampleFam g t r) t) :=
    clusterDominatesZero hgs hgc heven hA ρ
  have hbud := clusterValue_le_budget hgs hgc heven hpole hprime hoff hgamma
  have hm : 1 ≤ (Zeta23.zetaZeroConfig).mult (ρ : Zeros) :=
    (Zeta23.zetaZeroConfig).one_le_mult ((ρ : Zeros) : ℂ) (ρ : Zeros).2
  have hmR : (1 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by exact_mod_cast hm
  have hmono : evenResp g 0 r ≤ evenResp g (heightOf (ρ : Zeros)) r :=
    evenResp_zero_le_evenResp hgs.continuous hgc hnn hr hwin _
  have hA0 : 0 < evenResp g 0 r := hA 0
  have hbase : 2 * evenResp g 0 r ≤ coneWeight g r (ρ : Zeros) := by
    unfold coneWeight
    nlinarith [hmR, hmono, hA0]
  linarith

/-- **`no_zero_at_ordinate_of_heightFree_margin` — the height-blindness no-go.**
A strict margin based on the *height-free* baseline `2 A_0(r)` would exclude every
zero at the ordinate `t`, on the critical line as well as off it.  So the strict
comparison of the final contradiction cannot be produced from a height-free lower
bound for the cluster: it must be paid out of the height surplus. -/
theorem no_zero_at_ordinate_of_heightFree_margin {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hA : ∀ a : ℝ, 0 < evenResp g a r)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (hmargin : Boff + Bgamma < 2 * evenResp g 0 r) :
    ∀ ρ : Zeros, (ρ : ℂ).im ≠ t := by
  intro ρ him
  have := baseline_le_budget hgs hgc heven hnn hr hwin hA hpole hprime hoff hgamma ⟨ρ, him⟩
  linarith

/-! ## 5. The exact budget window of the pole-quotient lane -/

/-- The height-free cluster baseline: the same fibre sum with every height set to
zero. -/
def baselineCluster (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  ∑' ρ : SameOrd t, 2 * (((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) * evenResp g 0 r)

theorem summable_baselineCluster {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) :
    Summable fun ρ : SameOrd t =>
      2 * (((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) * evenResp g 0 r) := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
    (summable_coneWeight hgs hgc heven t r)
  · have hA0 : 0 ≤ evenResp g 0 r := evenResp_zero_nonneg hnn hr hwin
    have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
    positivity
  · have hmono : evenResp g 0 r ≤ evenResp g (heightOf (ρ : Zeros)) r :=
      evenResp_zero_le_evenResp hgs.continuous hgc hnn hr hwin _
    have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
    unfold coneWeight
    nlinarith [hmono, hmR]

/-- **The cluster value dominates its height-free baseline.** -/
theorem baselineCluster_le_clusterValue {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) :
    baselineCluster g t r ≤ evenConeFunctional (clusterVec (sampleFam g t r) t) := by
  rw [clusterVec_cone_value hgs hgc heven t r]
  refine (summable_baselineCluster hgs hgc heven hnn hr hwin).tsum_le_tsum (fun ρ => ?_)
    (summable_coneWeight hgs hgc heven t r)
  have hmono : evenResp g 0 r ≤ evenResp g (heightOf (ρ : Zeros)) r :=
    evenResp_zero_le_evenResp hgs.continuous hgc hnn hr hwin _
  have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
  unfold coneWeight
  nlinarith [hmono, hmR]

/-- **The cluster value lies inside a relative window above its height-free
baseline**, of relative width `√2 (cosh(|a|Λ) − 1)` where `Λ` is the taper support
radius and `|a| ≤ 1/2` bounds the heights of the strip. -/
theorem clusterValue_le_baselineCluster_mul {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r Λ : ℝ} (hr : 0 < r) (hΛ : 0 ≤ Λ) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) :
    evenConeFunctional (clusterVec (sampleFam g t r) t)
      ≤ baselineCluster g t r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) := by
  have hfac : (0 : ℝ) ≤ 1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1) := by
    have h1 : (1 : ℝ) ≤ Real.cosh (Λ / 2) := Real.one_le_cosh _
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  rw [clusterVec_cone_value hgs hgc heven t r, baselineCluster, ← tsum_mul_right]
  refine (summable_coneWeight hgs hgc heven t r).tsum_le_tsum (fun ρ => ?_)
    ((summable_baselineCluster hgs hgc heven hnn hr hwin).mul_right _)
  -- pointwise: the cone weight of one zero against its own baseline
  have hheight : |heightOf (ρ : Zeros)| ≤ 1 / 2 := abs_heightOf_le_half _
  have hstep := evenResp_le_baseline_mul hgs.continuous hgc hnn hr hsupp hwin
    (heightOf (ρ : Zeros))
  have hmonoc : Real.cosh (|heightOf (ρ : Zeros)| * Λ) ≤ Real.cosh (Λ / 2) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_abs, abs_of_nonneg hΛ, abs_of_nonneg (by linarith : (0:ℝ) ≤ Λ / 2)]
    nlinarith [abs_nonneg (heightOf (ρ : Zeros)), hheight, hΛ]
  have hA0 : 0 ≤ evenResp g 0 r := evenResp_zero_nonneg hnn hr hwin
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
  have hle1 : evenResp g 0 r * (1 + Real.sqrt 2 * (Real.cosh (|heightOf (ρ : Zeros)| * Λ) - 1))
      ≤ evenResp g 0 r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0
    have := mul_le_mul_of_nonneg_left hmonoc hs2
    linarith
  have hA : evenResp g (heightOf (ρ : Zeros)) r
      ≤ evenResp g 0 r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) := le_trans hstep hle1
  have hmul2 : (0 : ℝ) ≤ 2 * ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
  calc coneWeight g r (ρ : Zeros)
      = 2 * ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ)
          * evenResp g (heightOf (ρ : Zeros)) r := by unfold coneWeight; ring
    _ ≤ 2 * ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ)
          * (evenResp g 0 r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1))) :=
        mul_le_mul_of_nonneg_left hA hmul2
    _ = 2 * (((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) * evenResp g 0 r)
          * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) := by ring

/-- **`poleQuotientMarginWindow` — the exact remaining obligation of the
pole-quotient lane.**  For a nontrivial zero of `riemannZeta` at a high ordinate
the programme's own taper gives, unconditionally:

* the pole channel is killed by the parity quotient and the prime channel is the
  zero vector;
* every admissible pair of complement budgets satisfies
  `baselineCluster ≤ B_off + B_Γ`;
* while the cluster value itself is at most
  `(1 + √2 (cosh(9π/(8|t|)) − 1)) · baselineCluster`.

So the strict comparison `B_off + B_Γ < ℓ(Q_cluster)` that the contradiction
compiler consumes forces the two budgets into a half-open interval of *relative*
width `√2 (cosh(9π/(8|t|)) − 1) = O(|t|^{-2})` above the height-free baseline.
Nothing here claims such budgets exist. -/
theorem poleQuotientMarginWindow {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 < Λ ∧ Λ ≤ 9 * π / (4 * |t|) ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ)
      ∧ poleEvenResp g t r = 0 ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ 0 < baselineCluster g t r
      ∧ (∀ Boff Bgamma : ℝ, primeVec (sampleFam g t r) = 0 →
          |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff →
          |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma →
          baselineCluster g t r ≤ Boff + Bgamma)
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ baselineCluster g t r * (1 + Real.sqrt 2 * (Real.cosh (9 * π / (8 * |t|)) - 1)) := by
  have hpi := Real.pi_pos
  have htabs : 0 < |t| := abs_pos.mpr ht
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, hwin, -, hpole, hA, hrad⟩ :=
    exists_positive_taper_poleEven_zero ht
  set Λ : ℝ := 9 * π / (4 * |t|) with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ := fun u hu => (hrad u hu).le
  -- positivity of the baseline cluster
  have hbasepos : 0 < baselineCluster g t r := by
    have hsum := summable_baselineCluster hgs hgc heven hnn hrpos hwin (t := t)
    have hterm : ∀ ρ : SameOrd t,
        0 ≤ 2 * (((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) * evenResp g 0 r) := by
      intro ρ
      have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by positivity
      have := (hA 0).le
      positivity
    have hstar : (0 : ℝ) < 2 * (((Zeta23.zetaZeroConfig).mult
        ((⟨ρstar, him⟩ : SameOrd t) : Zeros) : ℝ) * evenResp g 0 r) := by
      have hm : 1 ≤ (Zeta23.zetaZeroConfig).mult (ρstar : ℂ) :=
        (Zeta23.zetaZeroConfig).one_le_mult (ρstar : ℂ) ρstar.2
      have hmR : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult (ρstar : ℂ) : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
      have := hA 0
      simpa using mul_pos (by norm_num : (0:ℝ) < 2) (mul_pos hmR this)
    exact Summable.tsum_pos hsum hterm ⟨ρstar, him⟩ hstar
  refine ⟨g, r, Λ, hgs, hgc, heven, hrpos, hΛpos, le_refl _, hsupp, hpole, hA, hbasepos,
    ?_, ?_⟩
  · intro Boff Bgamma hprime hoff hgamma
    exact le_trans (baselineCluster_le_clusterValue hgs hgc heven hnn hrpos hwin)
      (clusterValue_le_budget hgs hgc heven hpole hprime hoff hgamma)
  · have := clusterValue_le_baselineCluster_mul hgs hgc heven hnn (t := t) hrpos hΛpos.le
      hsupp hwin
    have hΛhalf : Λ / 2 = 9 * π / (8 * |t|) := by
      rw [hΛdef]; field_simp; ring
    rwa [hΛhalf] at this

/-! ## 6. The window is quantitatively `O(|t|^{-2})` -/

/-- An elementary quadratic bound for `cosh` near the origin, proved from the
exponential remainder estimate: `cosh x - 1 ≤ x²` for `|x| ≤ 1`. -/
theorem cosh_sub_one_le_sq {x : ℝ} (hx : |x| ≤ 1) : Real.cosh x - 1 ≤ x ^ 2 := by
  have h1 := Real.exp_bound hx (n := 2) (by norm_num)
  have h2 := Real.exp_bound (x := -x) (by rwa [abs_neg]) (n := 2) (by norm_num)
  have hsum : ∀ y : ℝ, (∑ i ∈ Finset.range 2, y ^ i / (Nat.factorial i : ℝ)) = 1 + y := by
    intro y
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h1
  rw [hsum] at h2
  have hb1 := (abs_le.mp h1).2
  have hb2 := (abs_le.mp h2).2
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  have hnum : ((2 : ℝ) + 1) / ((Nat.factorial 2 : ℝ) * 2) = 3 / 4 := by
    norm_num [Nat.factorial]
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  rw [Real.cosh_eq]
  have hval1 : Real.exp x ≤ 1 + x + |x| ^ 2 * (((2 : ℕ).succ : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
    linarith
  have hval2 : Real.exp (-x)
      ≤ 1 + -x + |(-x)| ^ 2 * (((2 : ℕ).succ : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
    linarith
  have hcoeff : (((2 : ℕ).succ : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) = 3 / 4 := by
    norm_num [Nat.factorial]
  rw [hcoeff] at hval1 hval2
  rw [abs_neg, habs] at hval2
  rw [habs] at hval1
  linarith

/-- **`poleQuotientMarginWindow_quantitative`.**  The same window with the
`cosh` factor evaluated: at a high ordinate the cluster value exceeds its
height-free baseline by a relative factor of at most `√2 (9π/(8|t|))²`.  So the
final strict comparison of the pole-quotient lane needs the off-ordinate and
gamma budgets to be known to relative accuracy `O(|t|^{-2})`. -/
theorem poleQuotientMarginWindow_quantitative {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 < Λ ∧ Λ ≤ 9 * π / (4 * |t|) ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ)
      ∧ poleEvenResp g t r = 0 ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ 0 < baselineCluster g t r
      ∧ (∀ Boff Bgamma : ℝ, primeVec (sampleFam g t r) = 0 →
          |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff →
          |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma →
          baselineCluster g t r ≤ Boff + Bgamma)
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ baselineCluster g t r * (1 + Real.sqrt 2 * (9 * π / (8 * |t|)) ^ 2) := by
  have hpi := Real.pi_pos
  have htabs : 0 < |t| := abs_pos.mpr ht
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  have htbig : 9 * π / 4 ≤ |t| := by
    have h1 : 4 * |t| * Real.log 2 ≤ 4 * |t| := by nlinarith
    have : 9 * π ≤ 4 * |t| := le_trans hheight h1
    linarith
  have hxle : 9 * π / (8 * |t|) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hxpos : 0 < 9 * π / (8 * |t|) := by positivity
  obtain ⟨g, r, Λ, hgs, hgc, heven, hrpos, hΛpos, hΛle, hsupp, hpole, hA, hbase, hbud, hwin⟩ :=
    poleQuotientMarginWindow him ht
  refine ⟨g, r, Λ, hgs, hgc, heven, hrpos, hΛpos, hΛle, hsupp, hpole, hA, hbase, hbud, ?_⟩
  refine le_trans hwin ?_
  have hcosh : Real.cosh (9 * π / (8 * |t|)) - 1 ≤ (9 * π / (8 * |t|)) ^ 2 :=
    cosh_sub_one_le_sq (by rw [abs_of_pos hxpos]; exact hxle)
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hmul : Real.sqrt 2 * (Real.cosh (9 * π / (8 * |t|)) - 1)
      ≤ Real.sqrt 2 * (9 * π / (8 * |t|)) ^ 2 := mul_le_mul_of_nonneg_left hcosh hs2
  exact mul_le_mul_of_nonneg_left (by linarith) hbase.le

/-- **`complementChannels_pinned`.**  The literal statement of what the two
complement channels of the pole-quotient lane actually do, with no budget
hypothesis at all: at a zero of the target ordinate their negated sum is pinned
inside the same narrow window,

    baselineCluster ≤ −(ℓ(Q_offOrd) + ℓ(Q_Γ))
                    ≤ baselineCluster · (1 + √2 (cosh(Λ/2) − 1)).

So the off-ordinate and gamma channels cancel the height-free baseline exactly,
up to a relative `O(Λ²)` correction, and the entire content of the final
contradiction is the *sign* of that correction. -/
theorem complementChannels_pinned {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r Λ : ℝ} (hr : 0 < r) (hΛ : 0 ≤ Λ) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0) :
    baselineCluster g t r
      ≤ -(evenConeFunctional (offOrdVec (sampleFam g t r) t)
          + evenConeFunctional (gammaVec (sampleFam g t r)))
    ∧ -(evenConeFunctional (offOrdVec (sampleFam g t r) t)
          + evenConeFunctional (gammaVec (sampleFam g t r)))
        ≤ baselineCluster g t r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) := by
  have hbal := evenCone_three_channel_balance hgs hgc heven hpole hprime
  have hlow := baselineCluster_le_clusterValue hgs hgc heven hnn hr hwin (t := t)
  have hhigh := clusterValue_le_baselineCluster_mul hgs hgc heven hnn hr hΛ hsupp hwin (t := t)
  constructor <;> linarith

end PoleQuotientComplementMargin
end Zeta23Bridge
