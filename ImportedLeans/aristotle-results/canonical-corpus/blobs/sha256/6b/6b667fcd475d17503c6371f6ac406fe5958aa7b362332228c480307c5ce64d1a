/-
# `M_cluster^pole`: an explicit lower margin for the cluster value

`PoleQuotientComplementMargin.lean` proved the two *upper* constraints of the
pole-quotient lane: the margin consumed by the split-budget compiler cannot be
height-free (`no_zero_at_ordinate_of_heightFree_margin`), and the whole height
surplus of the cluster is at most a relative `√2 (cosh(|a|Λ) − 1)` above the
height-free baseline (`clusterValue_le_baselineCluster_mul`).

What was missing is the matching *lower* bound: is the admissible window for the
two complement budgets

    [ baselineCluster , baselineCluster + surplus )

actually non-empty, and how wide is it?  This module answers that with an
explicit, unconditional second-moment margin.  For a nonnegative taper supported
inside the sampling window `2r|u| < π/2`,

    A_a(r) − A_0(r) ≥ (√2/4) a² ∫ g(u) u² du        (`heightSurplus_ge`),

the exact quantitative counterpart of `heightSurplus_le`.  Together the two give
the two-sided estimate

    (√2/4) a² ∫ g u² ≤ A_a(r) − A_0(r) ≤ (cosh(|a|Λ) − 1) ∫ g   (`heightSurplus_two_sided`),

and since `∫ g u² ≥ 0` and `cosh(|a|Λ) − 1 ≤ (aΛ)²` for `|a|Λ ≤ 1`, both sides are
of order `(aΛ)²`: the height surplus is *exactly* quadratic in the distance of the
zero from the critical line, no better and no worse.

At fibre level this instantiates the socket `M_cluster^pole`:

    baselineCluster + (√2/2) a_*² ∫ g u²  ≤  ℓ(Q_cluster)
                                              (`clusterValue_ge_baseline_add_margin`),

for `a_* = Re ρ_* − 1/2` the height of any zero of the target ordinate; and hence
every admissible pair of complement budgets must already satisfy

    baselineCluster + (√2/2) a_*² ∫ g u²  ≤  B_off + B_Γ
                                              (`budget_exceeds_baseline_plus_margin`).

Combined with §29.3 this pins the required accuracy of the two complement
channels from *both* sides.  The margin is strictly positive as soon as the taper
has positive mass and the zero is off the critical line
(`clusterMargin_pos_of_offLine`), so the target interval of the lane is non-empty
— but its width is only of order `(a_* Λ)²`, which for the high-ordinate taper
(`Λ ≤ 9π/(4|t|)`) is `O(|t|^{-2})` relative to the baseline.

Nothing here asserts that budgets of that accuracy exist, nothing here uses or
weakens the Riemann Hypothesis, and no numerical evidence is involved.

No `sorry`, no `axiom`.
-/
import Zeta23Bridge.PoleQuotientComplementMargin

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace PoleQuotientClusterMargin

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.PoleQuotientComplementMargin

/-! ## 1. A quadratic lower bound for `cosh` -/

/-- `cosh x ≥ 1 + x²/2`, from `cosh (2y) = 1 + 2 sinh² y` and `sinh y ≥ y`. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hx : Real.cosh x = Real.cosh |x| := by
    rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Real.cosh_neg]
  have hy0 : (0 : ℝ) ≤ |x| / 2 := by positivity
  have hs : |x| / 2 ≤ Real.sinh (|x| / 2) := Real.self_le_sinh_iff.mpr hy0
  have h2 : Real.cosh (2 * (|x| / 2)) = Real.cosh (|x| / 2) ^ 2 + Real.sinh (|x| / 2) ^ 2 :=
    Real.cosh_two_mul _
  have h3 : Real.cosh (|x| / 2) ^ 2 = Real.sinh (|x| / 2) ^ 2 + 1 := Real.cosh_sq _
  have habs : 2 * (|x| / 2) = |x| := by ring
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [habs] at h2
  rw [hx, h2, h3, hsq]
  nlinarith [hs, hy0]

/-! ## 2. The second moment of the taper -/

/-- The second moment `∫ g(u) u² du` of the taper. -/
def secondMoment (g : ℝ → ℝ) : ℝ := ∫ u : ℝ, g u * u ^ 2

theorem integrable_secondMoment {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun u : ℝ => g u * u ^ 2) :=
  taper_integrable hg hgc (by fun_prop)

theorem secondMoment_nonneg {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) : 0 ≤ secondMoment g := by
  refine integral_nonneg (fun u => ?_)
  exact mul_nonneg (hnn u) (by positivity)

/-! ## 3. The height surplus is at least quadratic in the height -/

/-- **`heightSurplus_ge` — the quantitative counterpart of `heightSurplus_le`.**
For a nonnegative taper supported inside the sampling window the even response at
height `a` exceeds the height-free baseline by at least `(√2/4) a² ∫ g u² du`. -/
theorem heightSurplus_ge {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (a : ℝ) :
    Real.sqrt 2 / 4 * (a ^ 2 * secondMoment g) ≤ evenResp g a r - evenResp g 0 r := by
  have hsub : evenResp g a r - evenResp g 0 r
      = ∫ u : ℝ, (g u * (Real.cosh (a * u) * Real.cos (r * u))
          - g u * (Real.cosh (0 * u) * Real.cos (r * u))) := by
    simp only [evenResp]
    rw [← integral_sub (evenResp_integrable hg hgc a r) (evenResp_integrable hg hgc 0 r)]
  have hconst : Real.sqrt 2 / 4 * (a ^ 2 * secondMoment g)
      = ∫ u : ℝ, (Real.sqrt 2 / 4 * a ^ 2) * (g u * u ^ 2) := by
    rw [integral_const_mul]
    unfold secondMoment
    ring
  rw [hsub, hconst]
  refine integral_mono (((integrable_secondMoment hg hgc).const_mul _))
    (((evenResp_integrable hg hgc a r).sub (evenResp_integrable hg hgc 0 r))) (fun u => ?_)
  by_cases hgu : g u = 0
  · simp [hgu]
  · have hgu' : 0 ≤ g u := hnn u
    have hc : Real.sqrt 2 / 2 ≤ Real.cos (r * u) := cos_ge_of_window hr (hwin u hgu)
    have hch : 1 + (a * u) ^ 2 / 2 ≤ Real.cosh (a * u) := one_add_sq_div_two_le_cosh _
    have h1 : Real.cosh (0 * u) = 1 := by rw [zero_mul, Real.cosh_zero]
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    rw [h1, one_mul]
    have hkey : Real.sqrt 2 / 4 * a ^ 2 * u ^ 2
        ≤ Real.cosh (a * u) * Real.cos (r * u) - Real.cos (r * u) := by
      have hfac : Real.cosh (a * u) - 1 ≥ (a * u) ^ 2 / 2 := by linarith
      have hcosnn : 0 ≤ Real.cos (r * u) := by nlinarith
      have hprod : ((a * u) ^ 2 / 2) * (Real.sqrt 2 / 2)
          ≤ (Real.cosh (a * u) - 1) * Real.cos (r * u) := by
        have h5 : (0 : ℝ) ≤ (a * u) ^ 2 / 2 := by positivity
        nlinarith [hfac, hc, h5]
      nlinarith [hprod]
    nlinarith [hgu', hkey]

/-- **The two-sided height surplus estimate.**  Both bounds are quadratic in the
height, so the surplus is of exact order `(aΛ)²`. -/
theorem heightSurplus_two_sided {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r Λ : ℝ} (hr : 0 < r) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (a : ℝ) :
    Real.sqrt 2 / 4 * (a ^ 2 * secondMoment g) ≤ evenResp g a r - evenResp g 0 r
      ∧ evenResp g a r - evenResp g 0 r ≤ (Real.cosh (|a| * Λ) - 1) * ∫ u : ℝ, g u :=
  ⟨heightSurplus_ge hg hgc hnn hr hwin a, heightSurplus_le hg hgc hnn hsupp a r⟩

/-! ## 4. The cluster margin at fibre level -/

/-- The margin the cluster value has over its height-free baseline, as read off a
single zero of the target ordinate. -/
def clusterMargin (g : ℝ → ℝ) (ρ : Zeros) : ℝ :=
  Real.sqrt 2 / 2 * (heightOf ρ ^ 2 * secondMoment g)

theorem clusterMargin_nonneg {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) (ρ : Zeros) :
    0 ≤ clusterMargin g ρ := by
  have := secondMoment_nonneg (g := g) hnn
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  unfold clusterMargin
  positivity

/-- The margin is strictly positive exactly when the zero is off the critical line
and the taper has positive second moment. -/
theorem clusterMargin_pos_of_offLine {g : ℝ → ℝ} (ρ : Zeros)
    (hρ : heightOf ρ ≠ 0) (hm : 0 < secondMoment g) : 0 < clusterMargin g ρ := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : 0 < heightOf ρ ^ 2 := by positivity
  unfold clusterMargin
  positivity

/-- **`M_cluster^pole`, instantiated.**  The cluster value exceeds its height-free
baseline by at least the explicit second-moment margin of any single zero of the
target ordinate. -/
theorem clusterValue_ge_baseline_add_margin {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (ρstar : SameOrd t) :
    baselineCluster g t r + clusterMargin g (ρstar : Zeros)
      ≤ evenConeFunctional (clusterVec (sampleFam g t r) t) := by
  classical
  set base : SameOrd t → ℝ := fun ρ =>
    2 * (((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) * evenResp g 0 r) with hbase
  have hsumBase : Summable base := summable_baselineCluster hgs hgc heven hnn hr hwin
  have hsumCone : Summable fun ρ : SameOrd t => coneWeight g r (ρ : Zeros) :=
    summable_coneWeight hgs hgc heven t r
  have hsumDiff : Summable fun ρ : SameOrd t => coneWeight g r (ρ : Zeros) - base ρ :=
    hsumCone.sub hsumBase
  -- each term of the difference is nonnegative
  have hterm : ∀ ρ : SameOrd t, clusterMargin g (ρ : Zeros)
      ≤ coneWeight g r (ρ : Zeros) - base ρ := by
    intro ρ
    have hsurp := heightSurplus_ge hgs.continuous hgc hnn hr hwin (heightOf (ρ : Zeros))
    have hm : 1 ≤ (Zeta23.zetaZeroConfig).mult (ρ : Zeros) :=
      (Zeta23.zetaZeroConfig).one_le_mult ((ρ : Zeros) : ℂ) (ρ : Zeros).2
    have hmR : (1 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ) := by exact_mod_cast hm
    have hnn' : 0 ≤ Real.sqrt 2 / 4 * (heightOf (ρ : Zeros) ^ 2 * secondMoment g) := by
      have := secondMoment_nonneg (g := g) hnn
      have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      positivity
    have hdiff : coneWeight g r (ρ : Zeros) - base ρ
        = 2 * ((Zeta23.zetaZeroConfig).mult (ρ : Zeros) : ℝ)
            * (evenResp g (heightOf (ρ : Zeros)) r - evenResp g 0 r) := by
      unfold coneWeight; rw [hbase]; ring
    rw [hdiff]
    unfold clusterMargin
    nlinarith [hsurp, hmR, hnn']
  have hnnDiff : ∀ ρ : SameOrd t, 0 ≤ coneWeight g r (ρ : Zeros) - base ρ := fun ρ =>
    le_trans (clusterMargin_nonneg hnn _) (hterm ρ)
  have hle : clusterMargin g (ρstar : Zeros)
      ≤ ∑' ρ : SameOrd t, (coneWeight g r (ρ : Zeros) - base ρ) :=
    le_trans (hterm ρstar) (hsumDiff.le_tsum ρstar (fun j _ => hnnDiff j))
  have hsplit : ∑' ρ : SameOrd t, (coneWeight g r (ρ : Zeros) - base ρ)
      = (∑' ρ : SameOrd t, coneWeight g r (ρ : Zeros)) - ∑' ρ : SameOrd t, base ρ :=
    hsumCone.tsum_sub hsumBase
  rw [clusterVec_cone_value hgs hgc heven t r]
  have hbaseline : baselineCluster g t r = ∑' ρ : SameOrd t, base ρ := rfl
  rw [hbaseline]
  rw [hsplit] at hle
  linarith

/-- The second moment of a taper supported in `|u| ≤ Λ` is at most `Λ² ∫ g`. -/
theorem secondMoment_le_sq_mul_mass {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ}
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) :
    secondMoment g ≤ Λ ^ 2 * ∫ u : ℝ, g u := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hrw : Λ ^ 2 * ∫ u : ℝ, g u = ∫ u : ℝ, g u * Λ ^ 2 := by
    rw [integral_mul_const]; ring
  rw [hrw]
  refine integral_mono (integrable_secondMoment hg hgc) (hint.mul_const _) (fun u => ?_)
  by_cases hgu : g u = 0
  · simp [hgu]
  · have hu : |u| ≤ Λ := hsupp u hgu
    have hsq : u ^ 2 ≤ Λ ^ 2 := by
      have h1 : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith [abs_nonneg u, hu]
    exact mul_le_mul_of_nonneg_left hsq (hnn u)

/-- **The margin is quadratically small.**  Against the height-free baseline
response it is at most `a² Λ²`: for the high-ordinate taper (`Λ ≤ 9π/(4|t|)`,
`|a| ≤ 1/2`) this is `O(|t|^{-2})`. -/
theorem clusterMargin_le_sq_mul_baseline {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r Λ : ℝ} (hr : 0 < r)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (ρ : Zeros) :
    clusterMargin g ρ ≤ heightOf ρ ^ 2 * Λ ^ 2 * evenResp g 0 r := by
  have h1 := secondMoment_le_sq_mul_mass hg hgc hnn hsupp
  have h2 := taperMass_le_evenResp_zero hg hgc hnn hr hwin
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq : (0 : ℝ) ≤ heightOf ρ ^ 2 := sq_nonneg _
  have hΛsq : (0 : ℝ) ≤ Λ ^ 2 := sq_nonneg _
  have hchain : secondMoment g ≤ Λ ^ 2 * (Real.sqrt 2 * evenResp g 0 r) := by
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_left h2 hΛsq
  have hkey : heightOf ρ ^ 2 * secondMoment g
      ≤ heightOf ρ ^ 2 * (Λ ^ 2 * (Real.sqrt 2 * evenResp g 0 r)) :=
    mul_le_mul_of_nonneg_left hchain hsq
  have hfinal : Real.sqrt 2 / 2 * (heightOf ρ ^ 2 * secondMoment g)
      ≤ Real.sqrt 2 / 2 * (heightOf ρ ^ 2 * (Λ ^ 2 * (Real.sqrt 2 * evenResp g 0 r))) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  unfold clusterMargin
  calc Real.sqrt 2 / 2 * (heightOf ρ ^ 2 * secondMoment g)
      ≤ Real.sqrt 2 / 2 * (heightOf ρ ^ 2 * (Λ ^ 2 * (Real.sqrt 2 * evenResp g 0 r))) := hfinal
    _ = (Real.sqrt 2 * Real.sqrt 2) / 2 * (heightOf ρ ^ 2 * Λ ^ 2 * evenResp g 0 r) := by ring
    _ = heightOf ρ ^ 2 * Λ ^ 2 * evenResp g 0 r := by rw [hs2]; ring

/-- **The complement budgets must already pay the baseline plus the margin.**
Unconditional: the literal balance forces `ℓ(Q_cluster) ≤ B_off + B_Γ`, and the
cluster value is at least the baseline plus the explicit second-moment margin of
any zero of the target ordinate. -/
theorem budget_exceeds_baseline_plus_margin {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (ρstar : SameOrd t) :
    baselineCluster g t r + clusterMargin g (ρstar : Zeros) ≤ Boff + Bgamma := by
  have h1 := clusterValue_ge_baseline_add_margin hgs hgc heven hnn hr hwin ρstar
  have h2 := clusterValue_le_budget hgs hgc heven hpole hprime hoff hgamma
  linarith

/-- **The admissible window of the lane, from both sides.**  For a zero of the
target ordinate at height `a_*`, any pair of complement budgets that the
split-budget compiler could consume must satisfy

    baselineCluster + (√2/2) a_*² ∫ g u²  ≤  B_off + B_Γ  <  ℓ(Q_cluster)
                                          ≤  baselineCluster (1 + √2 (cosh(Λ/2) − 1)),

so the two channels must be evaluated to an absolute accuracy between the
second-moment margin and the height surplus — both of order `(a_* Λ)²`. -/
theorem marginWindow_two_sided {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r Λ : ℝ} (hr : 0 < r) (hΛ : 0 ≤ Λ) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (ρstar : SameOrd t) :
    baselineCluster g t r + clusterMargin g (ρstar : Zeros) ≤ Boff + Bgamma
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ baselineCluster g t r * (1 + Real.sqrt 2 * (Real.cosh (Λ / 2) - 1)) :=
  ⟨budget_exceeds_baseline_plus_margin hgs hgc heven hnn hr hwin hpole hprime hoff hgamma ρstar,
    clusterValue_le_baselineCluster_mul hgs hgc heven hnn hr hΛ hsupp hwin⟩

end PoleQuotientClusterMargin
end Zeta23Bridge
