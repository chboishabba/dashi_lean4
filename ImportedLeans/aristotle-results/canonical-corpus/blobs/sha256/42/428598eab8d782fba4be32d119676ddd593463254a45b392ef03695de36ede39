/-
# `PhysicalGaussianNearFarRelativeBound`: what the A gate really needs

The A lane currently ends at the cutoff-optimization theorem
`ClayNS.gauss_nearfar_strict_relative_contraction`, whose two *physical*
hypotheses are

* **(A-near)** `|⟪N_{≤R},W_⊥⟫_{ρ_ν}| ≤ η_∞‖W_⊥‖²_{ρ_ν}` uniformly in the cutoff
  `R`, with `η_∞ < 1`, and
* **(A-far-rel)** `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ C_far‖W_⊥‖²_{ρ_ν}`.

This file settles the status of that pair.  Three things are proved, and they
are of three different kinds: a *reduction* (two hypotheses to one), a
*falsification* (the cutoff architecture is not weakening anything), and a
*no-go* (the surviving hypothesis is genuinely an amplitude — Reynolds —
restriction and cannot be obtained from soft estimates).

## 1. Reduction: two physical hypotheses become one

`ClayNS.physical_gauss_nearfar_relative_bound`.  The single mixed-weight
relative estimate

  **(A-single)**  `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ K·∫ρ_ν‖W_⊥‖²`,   `K < 1`,

implies the full strict relative contraction

  `|⟪N,W_⊥⟫_{ρ_ν}| ≤ K‖W_⊥‖²_{ρ_ν}`,

*directly*: since `ρ_ν ≤ ρ_{2ν}` pointwise, no cutoff, no tail optimization and
no far/near bookkeeping are needed.  (A-single) is exactly (A-far-rel) with
`C_far = K < 1`; and (A-near) at every cutoff, uniformly, is a one-line
consequence of it (`ClayNS.gauss_near_pairing_of_mixed_moment`).  So the A gate
is fed by **one** scale-invariant norm estimate rather than two.

## 2. Falsification: the cutoff optimization gains nothing

`ClayNS.gauss_uniform_near_implies_contraction` and
`ClayNS.gauss_nearfar_optimization_no_gain`.  If the interaction has a finite
Gaussian pairing moment, then (A-near) *uniform in the cutoff* already implies
the conclusion of the optimization theorem, with the same constant and with no
use of (A-far-rel) at all: the near pairings converge to the full pairing as
`R → ∞` by dominated convergence.  Hence the uniform-in-`R` hypothesis is not a
weakening of the target; the entire physical content of the A gate sits in the
constant `η_∞ < 1`, and searching for a cleverer cutoff cannot produce it.

## 3. No-go: the surviving hypothesis is an amplitude restriction

`ClayNS.gauss_relative_contraction_amplitude_no_go`.  Fix a profile shape and
let its amplitude grow, `V = λV₀`.  The similarity equation
`V_τ = ν∆V − ½y·∇V − ½V − N` then reads `W = λ(M₀ − λN₀)` with `N = λ²N₀`,
where `M₀ = ν∆V₀ − ½y·∇V₀ − ½V₀` is the linear response of the shape and `N₀`
its quadratic interaction.  For **every** `η < 1` the relative contraction
`|⟪N,W⟫_ρ| ≤ η‖W‖²_ρ` fails as soon as

  `λ ≥ (|b| + |c| + 1)/((1−η)·a) `,  `a = ‖N₀‖²_ρ`, `b = ⟪N₀,M₀⟫_ρ`,
  `c = ‖M₀‖²_ρ`,

i.e. as soon as the *similarity Reynolds number* `λ‖N₀‖²_ρ/‖M₀‖²_ρ` is of unit
size.  Both sides are quartic in `λ` with leading coefficients `a` and `ηa`, so
the failure is not a matter of constants: no estimate that is uniform over
amplitudes can give (A-near), (A-single) or any relative contraction with
`η < 1`.  Any proof of the A gate must therefore consume a *dynamical*
amplitude normalization of the actual blow-up profile — an explicit
scale-invariant bound of the shape `‖V‖ ≲ √ν` in the relevant norm — and cannot
be produced by cutoff geometry, Littlewood–Paley splitting, or
divergence-free/pressure cancellation alone, all of which are amplitude
homogeneous.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianNearFarOptimization

open MeasureTheory Set Filter
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-! ## The weight monotonicity `ρ_ν ≤ ρ_{2ν}` -/

/-- The Gaussian weight increases with its parameter: `ρ_ν ≤ ρ_{2ν}`. -/
lemma gaussWeight_le_two {nu : ℝ} (hnu : 0 < nu) (y : E3) :
    gaussWeight nu y ≤ gaussWeight (2 * nu) y := by
  rw [gaussWeight, gaussWeight, Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
  have h : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  gcongr
  linarith

/-! ## 1. Two physical hypotheses become one -/

/-- **(A-near), uniformly in the cutoff, from (A-single).**  The mixed-weight
relative moment bound dominates every near pairing, with a constant independent
of the cutoff `R`. -/
theorem gauss_near_pairing_of_mixed_moment {nu K : ℝ} (hnu : 0 < nu)
    (N Wp : E3 → E3)
    (hmix : (∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hint : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)))
    (R : ℝ) :
    |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have hbound : ∀ y : E3, ‖gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫‖
      ≤ gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    have hcs : |(⟪N y, Wp y⟫ : ℝ)| ≤ ‖N y‖ * ‖Wp y‖ := abs_real_inner_le_norm _ _
    have hmono := gaussWeight_le_two hnu y
    have hnn : (0 : ℝ) ≤ ‖N y‖ * ‖Wp y‖ := by positivity
    by_cases h : ‖y‖ ≤ R
    · simp only [gaussNear, h, if_true, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwpos]
      calc gaussWeight nu y * |(⟪N y, Wp y⟫ : ℝ)|
          ≤ gaussWeight nu y * (‖N y‖ * ‖Wp y‖) := mul_le_mul_of_nonneg_left hcs hwpos
        _ ≤ gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) :=
            mul_le_mul_of_nonneg_right hmono hnn
    · have : (0 : ℝ) ≤ gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) := by
        have := (gaussWeight_pos (2 * nu) y).le
        positivity
      simp [gaussNear, h, this]
  have hle := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hle
  linarith

/-- **The A gate from one scale-invariant estimate.**  If the interaction obeys
the single mixed-weight relative bound

  `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ K·∫ρ_ν‖W_⊥‖²`,

then it is a strict relative contraction of the transverse expenditure with the
same constant,

  `|⟪N,W_⊥⟫_{ρ_ν}| ≤ K·‖W_⊥‖²_{ρ_ν}`.

No cutoff and no tail optimization are used: the weight monotonicity
`ρ_ν ≤ ρ_{2ν}` does all the work.  In particular (A-near) and (A-far-rel) are
both consequences of this one hypothesis, which is the announced reduction
`2 physical hypotheses → 1`. -/
theorem physical_gauss_nearfar_relative_bound {nu K : ℝ} (hnu : 0 < nu)
    (N Wp : E3 → E3)
    (hmix : (∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hint : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))) :
    |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have hbound : ∀ y : E3, ‖gaussWeight nu y * ⟪N y, Wp y⟫‖
      ≤ gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    have hcs : |(⟪N y, Wp y⟫ : ℝ)| ≤ ‖N y‖ * ‖Wp y‖ := abs_real_inner_le_norm _ _
    have hmono := gaussWeight_le_two hnu y
    have hnn : (0 : ℝ) ≤ ‖N y‖ * ‖Wp y‖ := by positivity
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwpos]
    calc gaussWeight nu y * |(⟪N y, Wp y⟫ : ℝ)|
        ≤ gaussWeight nu y * (‖N y‖ * ‖Wp y‖) := mul_le_mul_of_nonneg_left hcs hwpos
      _ ≤ gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) :=
          mul_le_mul_of_nonneg_right hmono hnn
  have hle := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hle
  linarith

/-- The drop-in replacement for `ClayNS.gauss_nearfar_strict_relative_contraction`:
the same conclusion (`∃ θ < 1` with a strict relative contraction of the
transverse expenditure), obtained from the single hypothesis (A-single) instead
of the pair (A-near, uniform in the cutoff) + (A-far-rel). -/
theorem physical_gauss_nearfar_strict_relative_contraction {nu K : ℝ} (hnu : 0 < nu)
    (hK : K < 1) (N Wp : E3 → E3)
    (hmix : (∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hint : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))) :
    ∃ theta : ℝ, theta < 1 ∧
      |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
        ≤ theta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 :=
  ⟨K, hK, physical_gauss_nearfar_relative_bound hnu N Wp hmix hint⟩

/-- The exact weight identity behind the mixed-weight hypothesis:
`ρ_{2ν}(y)·e^{−|y|²/(8ν)} = ρ_ν(y)`. -/
lemma gaussWeight_two_mul_half_tail {nu : ℝ} (hnu : 0 < nu) (y : E3) :
    gaussWeight (2 * nu) y * Real.exp (-(‖y‖ ^ 2) / (8 * nu)) = gaussWeight nu y := by
  rw [gaussWeight, gaussWeight, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **A pointwise criterion for (A-single).**  The single mixed-weight
hypothesis holds with constant `K` as soon as the interaction is pointwise
dominated by the transverse velocity *with one half of the Gaussian weight to
spare*,

  `‖N(y)‖ ≤ K·e^{−|y|²/(8ν)}‖W_⊥(y)‖`.

This is the sharpest reformulation of what the A gate still needs: a pointwise
relative bound on the physical interaction which is allowed to degrade, but
only by a Gaussian factor, at the far field. -/
theorem mixed_moment_of_pointwise_gaussian_domination {nu K : ℝ} (hnu : 0 < nu)
    (N Wp : E3 → E3)
    (hdom : ∀ y : E3, ‖N y‖ ≤ K * Real.exp (-(‖y‖ ^ 2) / (8 * nu)) * ‖Wp y‖)
    (hintN : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)))
    (hintW : Integrable (fun y : E3 => gaussWeight nu y * ‖Wp y‖ ^ 2)) :
    (∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))
      ≤ K * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have hpt : ∀ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)
      ≤ K * (gaussWeight nu y * ‖Wp y‖ ^ 2) := by
    intro y
    have hwpos := (gaussWeight_pos (2 * nu) y).le
    have hstep : ‖N y‖ * ‖Wp y‖
        ≤ (K * Real.exp (-(‖y‖ ^ 2) / (8 * nu))) * ‖Wp y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right (hdom y) (norm_nonneg (Wp y))
      nlinarith [norm_nonneg (Wp y)]
    calc gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)
        ≤ gaussWeight (2 * nu) y * ((K * Real.exp (-(‖y‖ ^ 2) / (8 * nu))) * ‖Wp y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hwpos
      _ = K * ((gaussWeight (2 * nu) y * Real.exp (-(‖y‖ ^ 2) / (8 * nu))) * ‖Wp y‖ ^ 2) := by
          ring
      _ = K * (gaussWeight nu y * ‖Wp y‖ ^ 2) := by
          rw [gaussWeight_two_mul_half_tail hnu y]
  have hmono := integral_mono hintN (hintW.const_mul K)
    (fun y => hpt y)
  rwa [integral_const_mul] at hmono

/-! ## 2. The cutoff optimization does not weaken the physical input -/

/-- The near fields converge to the full field, in the Gaussian pairing, as the
cutoff grows: a dominated-convergence statement along the integers. -/
theorem gauss_near_pairing_tendsto {nu : ℝ} (N Wp : E3 → E3)
    (hN : Continuous N) (hW : Continuous Wp)
    (hint : Integrable (fun y : E3 => gaussWeight nu y * (‖N y‖ * ‖Wp y‖))) :
    Tendsto (fun n : ℕ => ∫ y : E3, gaussWeight nu y * ⟪gaussNear (n : ℝ) N y, Wp y⟫)
      atTop (nhds (∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫)) := by
  have hmeasN : Measurable N := hN.measurable
  have hmeasW : Measurable Wp := hW.measurable
  have hmeasρ : Measurable (fun y : E3 => gaussWeight nu y) := by
    unfold gaussWeight
    fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun y : E3 => gaussWeight nu y * ⟪gaussNear (n : ℝ) N y, Wp y⟫) volume := by
    intro n
    have hnear : Measurable (gaussNear (n : ℝ) N) := by
      unfold gaussNear
      refine Measurable.ite ?_ hmeasN measurable_const
      exact measurableSet_le (by fun_prop) measurable_const
    exact ((hmeasρ.mul ((hnear.inner hmeasW))).aestronglyMeasurable)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun y : E3 => gaussWeight nu y * (‖N y‖ * ‖Wp y‖)) hmeas hint ?_ ?_
  · intro n
    refine Filter.Eventually.of_forall fun y => ?_
    have hwpos := (gaussWeight_pos nu y).le
    have hcs : |(⟪N y, Wp y⟫ : ℝ)| ≤ ‖N y‖ * ‖Wp y‖ := abs_real_inner_le_norm _ _
    have hnn : (0 : ℝ) ≤ gaussWeight nu y * (‖N y‖ * ‖Wp y‖) := by positivity
    by_cases h : ‖y‖ ≤ (n : ℝ)
    · simp only [gaussNear, h, if_true, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwpos]
      exact mul_le_mul_of_nonneg_left hcs hwpos
    · simp [gaussNear, h, hnn]
  · refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge ‖y‖
    refine tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => ?_
    have : ‖y‖ ≤ (n : ℝ) := hm.trans (by exact_mod_cast Nat.cast_le.2 hn)
    simp [gaussNear, this]

/-- **The uniform-in-cutoff near hypothesis already is the target.**  If the
Gaussian pairing moment is finite and (A-near) holds at every cutoff with one
constant `η`, then the full interaction obeys the same relative bound — with no
far hypothesis, no tail and no choice of cutoff. -/
theorem gauss_uniform_near_implies_contraction {nu eta : ℝ} (N Wp : E3 → E3)
    (hN : Continuous N) (hW : Continuous Wp)
    (hint : Integrable (fun y : E3 => gaussWeight nu y * (‖N y‖ * ‖Wp y‖)))
    (hnear : ∀ R : ℝ, 0 ≤ R →
      |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
        ≤ eta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2) :
    |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
      ≤ eta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have htend := gauss_near_pairing_tendsto (nu := nu) N Wp hN hW hint
  have habs : Tendsto
      (fun n : ℕ => |∫ y : E3, gaussWeight nu y * ⟪gaussNear (n : ℝ) N y, Wp y⟫|)
      atTop (nhds |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|) := htend.abs
  refine le_of_tendsto habs ?_
  refine Filter.Eventually.of_forall fun n => hnear (n : ℝ) (Nat.cast_nonneg n)

/-- **No gain from the cutoff optimization.**  The hypotheses of
`ClayNS.gauss_nearfar_strict_relative_contraction` are *stronger* than its
conclusion already without the far hypothesis: (A-near) uniform in the cutoff
gives the strict relative contraction outright.  Consequently no refinement of
the cutoff geometry can reduce the physical content of the A gate; that content
is precisely the constant `η_∞ < 1`. -/
theorem gauss_nearfar_optimization_no_gain {nu etaInf : ℝ} (hetaInf : etaInf < 1)
    (N Wp : E3 → E3) (hN : Continuous N) (hW : Continuous Wp)
    (hint : Integrable (fun y : E3 => gaussWeight nu y * (‖N y‖ * ‖Wp y‖)))
    (hnear : ∀ R : ℝ, 0 ≤ R →
      |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
        ≤ etaInf * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2) :
    ∃ theta : ℝ, theta < 1 ∧
      |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
        ≤ theta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 :=
  ⟨etaInf, hetaInf, gauss_uniform_near_implies_contraction N Wp hN hW hint hnear⟩

/-! ## 3. The amplitude no-go -/

/-- The scalar core of the amplitude no-go.  With `a > 0` the two quartics
`λ³|b − λa|` and `η·λ²(c − 2λb + λ²a)` have leading coefficients `a` and `ηa`;
for `η < 1` the first eventually dominates, with the explicit threshold
`λ ≥ max(1, (|b| + |c| + 1)/((1−η)a))`. -/
theorem amplitude_pairing_exceeds_relative {a b c eta lam : ℝ} (ha : 0 < a)
    (heta0 : 0 ≤ eta) (heta : eta < 1) (hlam1 : 1 ≤ lam)
    (hlam : (|b| + |c| + 1) / ((1 - eta) * a) ≤ lam) :
    eta * (lam ^ 2 * (c - 2 * lam * b + lam ^ 2 * a)) < lam ^ 3 * |b - lam * a| := by
  have h1e : 0 < 1 - eta := by linarith
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hthr : |b| + |c| + 1 ≤ (1 - eta) * a * lam := by
    rw [div_le_iff₀ (by positivity)] at hlam
    linarith
  -- the quadratic gain
  have hkey : 0 < (1 - eta) * lam ^ 2 * a + (2 * eta - 1) * lam * b - eta * c := by
    have hb : -(lam * |b|) ≤ (2 * eta - 1) * lam * b := by
      have h1 : |2 * eta - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have h2 : |(2 * eta - 1) * lam * b| ≤ lam * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam0.le]
        have : |2 * eta - 1| * lam ≤ 1 * lam := by
          exact mul_le_mul_of_nonneg_right h1 hlam0.le
        nlinarith [abs_nonneg b, abs_nonneg (2 * eta - 1)]
      linarith [neg_abs_le ((2 * eta - 1) * lam * b), le_abs_self ((2 * eta - 1) * lam * b)]
    have hc : -|c| ≤ -(eta * c) := by
      have : eta * c ≤ |c| := by
        calc eta * c ≤ 1 * |c| := by
              nlinarith [le_abs_self c, abs_nonneg c]
          _ = |c| := one_mul _
      linarith
    have hquad : lam * (|b| + |c| + 1) ≤ (1 - eta) * lam ^ 2 * a := by
      have := mul_le_mul_of_nonneg_left hthr hlam0.le
      nlinarith
    nlinarith [abs_nonneg b, abs_nonneg c]
  have habs : lam * a - b ≤ |b - lam * a| := by
    have := neg_abs_le (b - lam * a)
    linarith
  have hstep : eta * (lam ^ 2 * (c - 2 * lam * b + lam ^ 2 * a))
      < lam ^ 3 * (lam * a - b) := by nlinarith [sq_nonneg lam, pow_pos hlam0 3]
  have hmono : lam ^ 3 * (lam * a - b) ≤ lam ^ 3 * |b - lam * a| :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  linarith

/-- The Gaussian pairing of the amplitude family `N = λ²N₀`,
`W = λ(M₀ − λN₀)`. -/
lemma amplitude_family_pairing {nu lam : ℝ} (N0 M0 : E3 → E3)
    (hNN : Integrable (fun y : E3 => gaussWeight nu y * ‖N0 y‖ ^ 2))
    (hNM : Integrable (fun y : E3 => gaussWeight nu y * ⟪N0 y, M0 y⟫)) :
    (∫ y : E3, gaussWeight nu y * ⟪(lam ^ 2) • N0 y, lam • (M0 y - lam • N0 y)⟫)
      = lam ^ 3 * (∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫)
        - lam ^ 4 * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2 := by
  have hpt : ∀ y : E3, gaussWeight nu y * ⟪(lam ^ 2) • N0 y, lam • (M0 y - lam • N0 y)⟫
      = lam ^ 3 * (gaussWeight nu y * ⟪N0 y, M0 y⟫)
        - lam ^ 4 * (gaussWeight nu y * ‖N0 y‖ ^ 2) := by
    intro y
    have hself : (⟪N0 y, N0 y⟫ : ℝ) = ‖N0 y‖ ^ 2 := real_inner_self_eq_norm_sq _
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_right, hself]
    ring
  calc (∫ y : E3, gaussWeight nu y * ⟪(lam ^ 2) • N0 y, lam • (M0 y - lam • N0 y)⟫)
      = ∫ y : E3, (lam ^ 3 * (gaussWeight nu y * ⟪N0 y, M0 y⟫)
          - lam ^ 4 * (gaussWeight nu y * ‖N0 y‖ ^ 2)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = lam ^ 3 * (∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫)
        - lam ^ 4 * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2 := by
        rw [integral_sub (hNM.const_mul _) (hNN.const_mul _), integral_const_mul,
          integral_const_mul]

/-- The Gaussian energy of the amplitude family `W = λ(M₀ − λN₀)`. -/
lemma amplitude_family_energy {nu lam : ℝ} (N0 M0 : E3 → E3)
    (hNN : Integrable (fun y : E3 => gaussWeight nu y * ‖N0 y‖ ^ 2))
    (hMM : Integrable (fun y : E3 => gaussWeight nu y * ‖M0 y‖ ^ 2))
    (hNM : Integrable (fun y : E3 => gaussWeight nu y * ⟪N0 y, M0 y⟫)) :
    (∫ y : E3, gaussWeight nu y * ‖lam • (M0 y - lam • N0 y)‖ ^ 2)
      = lam ^ 2 * ((∫ y : E3, gaussWeight nu y * ‖M0 y‖ ^ 2)
          - 2 * lam * (∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫)
          + lam ^ 2 * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2) := by
  have hpt : ∀ y : E3, gaussWeight nu y * ‖lam • (M0 y - lam • N0 y)‖ ^ 2
      = lam ^ 2 * (gaussWeight nu y * ‖M0 y‖ ^ 2)
        - (2 * lam ^ 3) * (gaussWeight nu y * ⟪N0 y, M0 y⟫)
        + lam ^ 4 * (gaussWeight nu y * ‖N0 y‖ ^ 2) := by
    intro y
    have hnorm : ‖M0 y - lam • N0 y‖ ^ 2
        = ‖M0 y‖ ^ 2 - 2 * lam * ⟪N0 y, M0 y⟫ + lam ^ 2 * ‖N0 y‖ ^ 2 := by
      have := @norm_sub_sq_real _ _ _ (M0 y) (lam • N0 y)
      rw [this, real_inner_smul_right, norm_smul]
      have hcomm : (⟪M0 y, N0 y⟫ : ℝ) = ⟪N0 y, M0 y⟫ := real_inner_comm _ _
      rw [hcomm]
      simp [Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [norm_smul, mul_pow, hnorm]
    simp [Real.norm_eq_abs, sq_abs]
    ring
  calc (∫ y : E3, gaussWeight nu y * ‖lam • (M0 y - lam • N0 y)‖ ^ 2)
      = ∫ y : E3, (lam ^ 2 * (gaussWeight nu y * ‖M0 y‖ ^ 2)
          - (2 * lam ^ 3) * (gaussWeight nu y * ⟪N0 y, M0 y⟫)
          + lam ^ 4 * (gaussWeight nu y * ‖N0 y‖ ^ 2)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = lam ^ 2 * ((∫ y : E3, gaussWeight nu y * ‖M0 y‖ ^ 2)
          - 2 * lam * (∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫)
          + lam ^ 2 * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2) := by
        rw [integral_add
            (f := fun y : E3 => lam ^ 2 * (gaussWeight nu y * ‖M0 y‖ ^ 2)
              - (2 * lam ^ 3) * (gaussWeight nu y * ⟪N0 y, M0 y⟫))
            (g := fun y : E3 => lam ^ 4 * (gaussWeight nu y * ‖N0 y‖ ^ 2))
            ((hMM.const_mul _).sub (hNM.const_mul _)) (hNN.const_mul _),
          integral_sub (hMM.const_mul _) (hNM.const_mul _), integral_const_mul,
          integral_const_mul, integral_const_mul]
        ring

/-- **The amplitude no-go for the A gate.**  Let `N₀` be the quadratic
interaction of a fixed similarity shape with nonzero Gaussian energy, `M₀` its
linear (Ornstein–Uhlenbeck plus scaling) response, and consider the amplitude
family

  `V = λV₀`,  `N = λ²N₀`,  `W = V_τ = λ(M₀ − λN₀)`.

Then for every `η < 1` the relative contraction `|⟪N,W⟫_ρ| ≤ η‖W‖²_ρ` **fails**
for all amplitudes past the explicit threshold
`λ ≥ max(1, (|b|+|c|+1)/((1−η)a))`, where `a = ‖N₀‖²_ρ`, `b = ⟪N₀,M₀⟫_ρ`,
`c = ‖M₀‖²_ρ`.

Consequently no amplitude-homogeneous argument — cutoff geometry,
Littlewood–Paley shells, divergence-free or pressure cancellation — can supply
(A-near) or the single mixed-weight bound: the A gate necessarily consumes a
dynamical amplitude (Reynolds-type) normalization of the actual blow-up
profile.

The statement covers the transverse (marginal-projected) form of the A gate as
well: the marginal projection is onto `ℝ·V = ℝ·V₀`, which is amplitude
independent, so along the family the transverse fields are again `N_⊥ = λ²N₀⊥`
and `W_⊥ = λ(M₀⊥ − λN₀⊥)`; applying the theorem to the transverse shapes gives
the failure of `|⟪N,W_⊥⟫_ρ| ≤ η‖W_⊥‖²_ρ` whenever `N₀⊥` has nonzero Gaussian
energy. -/
theorem gauss_relative_contraction_amplitude_no_go {nu eta lam : ℝ}
    (N0 M0 : E3 → E3)
    (hNN : Integrable (fun y : E3 => gaussWeight nu y * ‖N0 y‖ ^ 2))
    (hMM : Integrable (fun y : E3 => gaussWeight nu y * ‖M0 y‖ ^ 2))
    (hNM : Integrable (fun y : E3 => gaussWeight nu y * ⟪N0 y, M0 y⟫))
    (ha : 0 < ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2)
    (heta0 : 0 ≤ eta) (heta : eta < 1) (hlam1 : 1 ≤ lam)
    (hlam : (|∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫|
        + |∫ y : E3, gaussWeight nu y * ‖M0 y‖ ^ 2| + 1)
      / ((1 - eta) * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2) ≤ lam) :
    eta * (∫ y : E3, gaussWeight nu y * ‖lam • (M0 y - lam • N0 y)‖ ^ 2)
      < |∫ y : E3, gaussWeight nu y * ⟪(lam ^ 2) • N0 y, lam • (M0 y - lam • N0 y)⟫| := by
  set a : ℝ := ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2 with hadef
  set b : ℝ := ∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫ with hbdef
  set c : ℝ := ∫ y : E3, gaussWeight nu y * ‖M0 y‖ ^ 2 with hcdef
  have hpair := amplitude_family_pairing (nu := nu) (lam := lam) N0 M0 hNN hNM
  have hen := amplitude_family_energy (nu := nu) (lam := lam) N0 M0 hNN hMM hNM
  rw [hpair, hen]
  have hcore := amplitude_pairing_exceeds_relative (a := a) (b := b) (c := c)
    (eta := eta) (lam := lam) ha heta0 heta hlam1 hlam
  have habs : |lam ^ 3 * b - lam ^ 4 * a| = lam ^ 3 * |b - lam * a| := by
    have hlam0 : (0 : ℝ) < lam := by linarith
    rw [show lam ^ 3 * b - lam ^ 4 * a = lam ^ 3 * (b - lam * a) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ 3)]
  rw [habs]
  exact hcore

/-- **The A gate bounds the amplitude.**  Contrapositive of the no-go: if the
strict relative contraction does hold at amplitude `λ ≥ 1` along the family,
then the amplitude is bounded by the explicit ratio of the shape's Gaussian
moments.  This is the precise sense in which the A gate is a Reynolds-type
smallness condition on the similarity profile. -/
theorem amplitude_bound_of_gauss_relative_contraction {nu eta lam : ℝ}
    (N0 M0 : E3 → E3)
    (hNN : Integrable (fun y : E3 => gaussWeight nu y * ‖N0 y‖ ^ 2))
    (hMM : Integrable (fun y : E3 => gaussWeight nu y * ‖M0 y‖ ^ 2))
    (hNM : Integrable (fun y : E3 => gaussWeight nu y * ⟪N0 y, M0 y⟫))
    (ha : 0 < ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2)
    (heta0 : 0 ≤ eta) (heta : eta < 1) (hlam1 : 1 ≤ lam)
    (hcontr : |∫ y : E3, gaussWeight nu y * ⟪(lam ^ 2) • N0 y, lam • (M0 y - lam • N0 y)⟫|
      ≤ eta * ∫ y : E3, gaussWeight nu y * ‖lam • (M0 y - lam • N0 y)‖ ^ 2) :
    lam < (|∫ y : E3, gaussWeight nu y * ⟪N0 y, M0 y⟫|
        + |∫ y : E3, gaussWeight nu y * ‖M0 y‖ ^ 2| + 1)
      / ((1 - eta) * ∫ y : E3, gaussWeight nu y * ‖N0 y‖ ^ 2) := by
  by_contra hcon
  push_neg at hcon
  exact absurd hcontr (not_le.2
    (gauss_relative_contraction_amplitude_no_go N0 M0 hNN hMM hNM ha heta0 heta hlam1 hcon))

end ClayNS
