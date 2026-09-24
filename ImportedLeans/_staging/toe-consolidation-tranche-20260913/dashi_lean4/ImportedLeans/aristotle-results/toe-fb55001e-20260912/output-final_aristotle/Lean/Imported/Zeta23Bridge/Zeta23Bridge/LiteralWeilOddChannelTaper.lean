/-
# Discharging the parity minor: an explicit taper for which the odd pole channel vanishes

`LiteralWeilParityBalance.lean` reduces the four-sample parity decomposition of the
literal zeta Weil explicit formula to a single remaining obligation: the target
parity pair must be transverse to the (ordinate-modulated) pole pair.  This module
discharges that obligation in the odd channel, unconditionally, by *constructing*
the taper.

The mechanism.  Both the odd pole response and the odd target response are
integrals of the taper against an explicit weight,

  `Os(s) = ∫ g(u) cosh(u/2) sin(tu) sin(su) du`,
  `B_α(s) = ∫ g(u) sinh(αu) sin(su) du`.

Fix the sample radius `r = t/4`.  On the window `u ≈ π/(2t)` the pole weight is
strictly positive; on the window `u ≈ 3π/(2t)` it is strictly negative — the
ordinate modulation `sin(tu)` has changed sign, while `sin(ru)` has not.  The
target weight `sinh(αu) sin(ru)` is strictly positive on *both* windows, since it
does not see the ordinate at all.  Taking `g` to be a positive combination of two
symmetric bumps, one in each window, with the combination weight chosen to cancel
the pole response exactly, leaves the target response a sum of two positive terms.

Hence `Os(r) = 0` while `B_α(r) ≠ 0`, which already forces the target class to be
nonzero in the parity quotient: the odd coordinates of the balance relation give
`B_α(r) = c₂ Os(r)`.

Consequences, all unconditional:

* `exists_taper_poleOdd_zero_oddResp_ne_zero` — the construction.
* `literalWeilOddChannelTargetTransverse` — `Q_target ≠ 0` for that taper.
* `literalWeilOffLineNuisanceTransverse` — for an actual nontrivial zero of
  `riemannZeta` off the critical line, with nonzero ordinate, the literal Weil
  explicit formula supplies a four-sample balance relation in which

    `Q_other + Q_prime + Q_Γ ≠ 0`   and   `Q_target = -(Q_other + Q_prime + Q_Γ)`

  in the parity quotient by the pole space.  No balance relation, no minor and no
  taper property is assumed: all three are produced.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilParityBalance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOddChannelTaper

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance

/-! ## A localized bump with a positivity property -/

/-- A smooth bump supported in the window `|u - c| < R`, nonnegative, and with
strictly positive integral against any continuous weight that is strictly
positive on the window. -/
theorem exists_bump_localized (c : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ Continuous φ ∧ HasCompactSupport φ ∧ (∀ u, 0 ≤ φ u)
      ∧ (∀ u, φ u ≠ 0 → |u - c| < R)
      ∧ (∀ w : ℝ → ℝ, Continuous w → (∀ u, |u - c| < R → 0 < w u) →
          0 < ∫ u : ℝ, φ u * w u)
      ∧ 0 < φ c := by
  classical
  set f : ContDiffBump c := ⟨R / 2, R, by linarith, by linarith⟩ with hf
  have hfd : ContDiff ℝ 2 (⇑f) := f.contDiff (n := 2)
  refine ⟨⇑f, hfd, hfd.continuous, f.hasCompactSupport, fun u => f.nonneg,
    ?_, ?_, ?_⟩
  · intro u hu
    have : u ∈ Function.support (⇑f) := hu
    rw [f.support_eq] at this
    have := Metric.mem_ball.mp this
    rwa [Real.dist_eq] at this
  · intro w hw hwpos
    have hnonneg : 0 ≤ fun u : ℝ => f u * w u := by
      intro u
      by_cases hu : (f : ℝ → ℝ) u = 0
      · simp [hu]
      · have hb : |u - c| < R := by
          have : u ∈ Function.support (⇑f) := hu
          rw [f.support_eq] at this
          have := Metric.mem_ball.mp this
          rwa [Real.dist_eq] at this
        exact mul_nonneg f.nonneg (hwpos u hb).le
    have hint : Integrable (fun u : ℝ => f u * w u) :=
      taper_integrable hfd.continuous f.hasCompactSupport hw
    rw [integral_pos_iff_support_of_nonneg hnonneg hint]
    have hsub : Metric.closedBall c (R / 2) ⊆ Function.support (fun u : ℝ => f u * w u) := by
      intro u hu
      have h1 : (f : ℝ → ℝ) u = 1 := f.one_of_mem_closedBall hu
      have hb : |u - c| < R := by
        have := Metric.mem_closedBall.mp hu
        rw [Real.dist_eq] at this
        linarith
      have : f u * w u = w u := by rw [h1, one_mul]
      simp only [Function.mem_support, this]
      exact (hwpos u hb).ne'
    have hmeas : (0 : ENNReal) < volume (Metric.closedBall c (R / 2)) := by
      rw [Real.volume_closedBall]
      simp only [ENNReal.ofReal_pos]
      positivity
    exact lt_of_lt_of_le hmeas (measure_mono hsub)
  · have h1 : (f : ℝ → ℝ) c = 1 :=
      f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    rw [h1]; norm_num

/-! ## Symmetrisation -/

/-- The symmetrisation `g(u) = φ(u) + φ(-u)` of a profile. -/
def symmetrize (φ : ℝ → ℝ) : ℝ → ℝ := fun u => φ u + φ (-u)

theorem symmetrize_even (φ : ℝ → ℝ) (u : ℝ) : symmetrize φ (-u) = symmetrize φ u := by
  simp [symmetrize]; ring

theorem symmetrize_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (symmetrize φ) :=
  hφ.add (hφ.comp contDiff_neg)

theorem symmetrize_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (symmetrize φ) :=
  hφ.add (hφ.comp continuous_neg)

theorem symmetrize_hasCompactSupport {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (symmetrize φ) := by
  apply HasCompactSupport.add hφ
  exact hφ.comp_homeomorph (Homeomorph.neg ℝ)

/-- Against an even weight the symmetrisation just doubles the integral. -/
theorem integral_symmetrize {φ w : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hw : Continuous w) (hweven : ∀ u, w (-u) = w u) :
    ∫ u : ℝ, symmetrize φ u * w u = 2 * ∫ u : ℝ, φ u * w u := by
  have hsplit : (fun u : ℝ => symmetrize φ u * w u)
      = fun u : ℝ => φ u * w u + φ (-u) * w u := by
    funext u; simp [symmetrize]; ring
  have h1 : Integrable (fun u : ℝ => φ u * w u) := taper_integrable hφ hφc hw
  have h2 : Integrable (fun u : ℝ => φ (-u) * w u) :=
    taper_integrable (hφ.comp continuous_neg) (hφc.comp_homeomorph (Homeomorph.neg ℝ)) hw
  have hflip : ∫ u : ℝ, φ (-u) * w u = ∫ u : ℝ, φ u * w u := by
    have := MeasureTheory.integral_neg_eq_self (fun u : ℝ => φ (-u) * w u) (volume : Measure ℝ)
    simp only [neg_neg, hweven] at this
    exact this.symm
  rw [hsplit, integral_add h1 h2, hflip]
  ring

/-! ## Linearity of the responses in the taper -/

theorem oddResp_add_smul {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (lam y s : ℝ) :
    oddResp (fun u => a u + lam * b u) y s = oddResp a y s + lam * oddResp b y s := by
  unfold oddResp
  have h1 : Integrable (fun u : ℝ => a u * (Real.sinh (y * u) * Real.sin (s * u))) :=
    taper_integrable ha hac (by fun_prop)
  have h2 : Integrable (fun u : ℝ => lam * (b u * (Real.sinh (y * u) * Real.sin (s * u)))) :=
    ((taper_integrable hb hbc (by fun_prop)).const_mul lam)
  rw [show (fun u : ℝ => (a u + lam * b u) * (Real.sinh (y * u) * Real.sin (s * u)))
      = fun u : ℝ => a u * (Real.sinh (y * u) * Real.sin (s * u))
        + lam * (b u * (Real.sinh (y * u) * Real.sin (s * u))) by funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

theorem poleOddResp_add_smul {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (lam t s : ℝ) :
    poleOddResp (fun u => a u + lam * b u) t s
      = poleOddResp a t s + lam * poleOddResp b t s := by
  unfold poleOddResp
  have h1 : Integrable
      (fun u : ℝ => a u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))) :=
    taper_integrable ha hac (by fun_prop)
  have h2 : Integrable
      (fun u : ℝ => lam * (b u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u)))) :=
    ((taper_integrable hb hbc (by fun_prop)).const_mul lam)
  rw [show (fun u : ℝ => (a u + lam * b u)
        * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u)))
      = fun u : ℝ => a u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))
        + lam * (b u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))) by
    funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

/-! ## Sign flips in the two parameters -/

theorem oddResp_neg_height (g : ℝ → ℝ) (y s : ℝ) : oddResp g (-y) s = -oddResp g y s := by
  unfold oddResp
  rw [← integral_neg]
  congr 1; funext u
  rw [show -y * u = -(y * u) by ring, Real.sinh_neg]
  ring

theorem poleOddResp_neg_ordinate (g : ℝ → ℝ) (t s : ℝ) :
    poleOddResp g (-t) s = -poleOddResp g t s := by
  unfold poleOddResp
  rw [← integral_neg]
  congr 1; funext u
  rw [show -t * u = -(t * u) by ring, Real.sin_neg]
  ring

/-! ## The construction -/

/-- **The explicit taper.**  For a positive height `α` and a positive ordinate `t`
there is an even, `C²`, compactly supported taper and a positive sample radius at
which the odd pole response vanishes while the odd target response does not. -/
theorem exists_taper_poleOdd_zero_oddResp_ne_zero_pos {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleOddResp g t r = 0 ∧ oddResp g α r ≠ 0 := by
  have hpi := Real.pi_pos
  set r : ℝ := t / 4 with hr
  have hrpos : 0 < r := by positivity
  set R : ℝ := π / (8 * t) with hRdef
  have hRpos : 0 < R := by positivity
  -- the two window centres
  set c₁ : ℝ := π / (2 * t) with hc₁
  set c₂ : ℝ := 3 * π / (2 * t) with hc₂
  -- weights
  set wp : ℝ → ℝ := fun u => Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (r * u) with hwp
  set wt : ℝ → ℝ := fun u => Real.sinh (α * u) * Real.sin (r * u) with hwt
  have hwpc : Continuous wp := by rw [hwp]; fun_prop
  have hwtc : Continuous wt := by rw [hwt]; fun_prop
  have hwpe : ∀ u, wp (-u) = wp u := by
    intro u
    simp only [hwp]
    rw [show -u / 2 = -(u / 2) by ring, Real.cosh_neg, show t * -u = -(t * u) by ring,
      show r * -u = -(r * u) by ring, Real.sin_neg, Real.sin_neg]
    ring
  have hwte : ∀ u, wt (-u) = wt u := by
    intro u
    simp only [hwt]
    rw [show α * -u = -(α * u) by ring, show r * -u = -(r * u) by ring, Real.sinh_neg,
      Real.sin_neg]
    ring
  -- sign of `sin (r u)` on both windows: `r u ∈ (0, π)`
  have hsinr : ∀ u : ℝ, 0 < u → u < 2 * π / t → 0 < Real.sin (r * u) := by
    intro u hu hult
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [hr]
      have : u < 2 * π / t := hult
      have h4 : t / 4 * u = t * u / 4 := by ring
      rw [h4]
      have h5 : u * t < 2 * π := (lt_div_iff₀ ht).mp hult
      have h6 : t * u = u * t := mul_comm t u
      linarith
  -- window 1 : `sin (t u) > 0`
  have hwin₁ : ∀ u : ℝ, |u - c₁| < R → 0 < wp u ∧ 0 < wt u := by
    intro u hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlow : 3 * π / (8 * t) < u := by
      have : c₁ - R < u := by linarith
      rw [hc₁, hRdef] at this
      calc 3 * π / (8 * t) = π / (2 * t) - π / (8 * t) := by field_simp; ring
        _ < u := this
    have hhigh : u < 5 * π / (8 * t) := by
      have : u < c₁ + R := by linarith
      rw [hc₁, hRdef] at this
      calc u < π / (2 * t) + π / (8 * t) := this
        _ = 5 * π / (8 * t) := by field_simp; ring
    have hupos : 0 < u := lt_trans (by positivity) hlow
    have hu2pi : u < 2 * π / t := by
      have : 5 * π / (8 * t) < 2 * π / t := by
        rw [div_lt_div_iff₀ (by positivity) ht]
        nlinarith [Real.pi_pos]
      linarith
    have hsr : 0 < Real.sin (r * u) := hsinr u hupos hu2pi
    have hst : 0 < Real.sin (t * u) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · have hlt : t * u < t * (5 * π / (8 * t)) := mul_lt_mul_of_pos_left hhigh ht
        have h5 : t * (5 * π / (8 * t)) = 5 * π / 8 := by field_simp
        rw [h5] at hlt
        linarith
    constructor
    · rw [hwp]
      have : 0 < Real.cosh (u / 2) := Real.cosh_pos _
      positivity
    · rw [hwt]
      have : 0 < Real.sinh (α * u) := Real.sinh_pos_iff.mpr (by positivity)
      positivity
  -- window 2 : `sin (t u) < 0`
  have hwin₂ : ∀ u : ℝ, |u - c₂| < R → 0 < -wp u ∧ 0 < wt u := by
    intro u hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlow : 11 * π / (8 * t) < u := by
      have : c₂ - R < u := by linarith
      rw [hc₂, hRdef] at this
      calc 11 * π / (8 * t) = 3 * π / (2 * t) - π / (8 * t) := by field_simp; ring
        _ < u := this
    have hhigh : u < 13 * π / (8 * t) := by
      have : u < c₂ + R := by linarith
      rw [hc₂, hRdef] at this
      calc u < 3 * π / (2 * t) + π / (8 * t) := this
        _ = 13 * π / (8 * t) := by field_simp; ring
    have hupos : 0 < u := lt_trans (by positivity) hlow
    have hu2pi : u < 2 * π / t := by
      have : 13 * π / (8 * t) < 2 * π / t := by
        rw [div_lt_div_iff₀ (by positivity) ht]
        nlinarith [Real.pi_pos]
      linarith
    have hsr : 0 < Real.sin (r * u) := hsinr u hupos hu2pi
    have hst : Real.sin (t * u) < 0 := by
      have hlt : Real.sin (t * u - π) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have hlt : t * (11 * π / (8 * t)) < t * u := mul_lt_mul_of_pos_left hlow ht
          have h11 : t * (11 * π / (8 * t)) = 11 * π / 8 := by field_simp
          rw [h11] at hlt
          linarith
        · have hlt : t * u < t * (13 * π / (8 * t)) := mul_lt_mul_of_pos_left hhigh ht
          have h13 : t * (13 * π / (8 * t)) = 13 * π / 8 := by field_simp
          rw [h13] at hlt
          linarith
      have := Real.sin_sub_pi (t * u)
      linarith [this ▸ hlt]
    constructor
    · rw [hwp]
      have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
      have hn : 0 < -Real.sin (t * u) := by linarith
      have hprod := mul_pos (mul_pos hc hn) hsr
      linarith [hprod]
    · rw [hwt]
      have : 0 < Real.sinh (α * u) := Real.sinh_pos_iff.mpr (by positivity)
      positivity
  -- the two bumps
  obtain ⟨φ₁, hφ₁d, hφ₁c, hφ₁s, hφ₁n, hφ₁supp, hφ₁pos, -⟩ := exists_bump_localized c₁ hRpos
  obtain ⟨φ₂, hφ₂d, hφ₂c, hφ₂s, hφ₂n, hφ₂supp, hφ₂pos, -⟩ := exists_bump_localized c₂ hRpos
  set g₁ : ℝ → ℝ := symmetrize φ₁ with hg₁
  set g₂ : ℝ → ℝ := symmetrize φ₂ with hg₂
  have hg₁c : Continuous g₁ := symmetrize_continuous hφ₁c
  have hg₂c : Continuous g₂ := symmetrize_continuous hφ₂c
  have hg₁s : HasCompactSupport g₁ := symmetrize_hasCompactSupport hφ₁s
  have hg₂s : HasCompactSupport g₂ := symmetrize_hasCompactSupport hφ₂s
  -- responses of the two symmetrised bumps
  have hP₁ : 0 < poleOddResp g₁ t r := by
    have : poleOddResp g₁ t r = 2 * ∫ u : ℝ, φ₁ u * wp u := by
      rw [poleOddResp]
      exact integral_symmetrize hφ₁c hφ₁s hwpc hwpe
    rw [this]
    have := hφ₁pos wp hwpc (fun u hu => (hwin₁ u hu).1)
    linarith
  have hQ₁ : 0 < oddResp g₁ α r := by
    have : oddResp g₁ α r = 2 * ∫ u : ℝ, φ₁ u * wt u := by
      rw [oddResp]
      exact integral_symmetrize hφ₁c hφ₁s hwtc hwte
    rw [this]
    have := hφ₁pos wt hwtc (fun u hu => (hwin₁ u hu).2)
    linarith
  have hP₂ : poleOddResp g₂ t r < 0 := by
    have heq : poleOddResp g₂ t r = 2 * ∫ u : ℝ, φ₂ u * wp u := by
      rw [poleOddResp]
      exact integral_symmetrize hφ₂c hφ₂s hwpc hwpe
    have hneg := hφ₂pos (fun u => -wp u) (by fun_prop) (fun u hu => (hwin₂ u hu).1)
    have : ∫ u : ℝ, φ₂ u * wp u < 0 := by
      have hrw : (fun u : ℝ => φ₂ u * -wp u) = fun u : ℝ => -(φ₂ u * wp u) := by
        funext u; ring
      rw [hrw, integral_neg] at hneg
      linarith
    rw [heq]; linarith
  have hQ₂ : 0 < oddResp g₂ α r := by
    have : oddResp g₂ α r = 2 * ∫ u : ℝ, φ₂ u * wt u := by
      rw [oddResp]
      exact integral_symmetrize hφ₂c hφ₂s hwtc hwte
    rw [this]
    have := hφ₂pos wt hwtc (fun u hu => (hwin₂ u hu).2)
    linarith
  -- the combination
  set lam : ℝ := -poleOddResp g₂ t r / poleOddResp g₁ t r with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos (by linarith) hP₁
  refine ⟨fun u => g₂ u + lam * g₁ u, r, ?_, ?_, ?_, hrpos, ?_, ?_⟩
  · exact (symmetrize_contDiff hφ₂d).add (contDiff_const.mul (symmetrize_contDiff hφ₁d))
  · have hsc : HasCompactSupport (fun u : ℝ => lam * g₁ u) := hg₁s.mul_left
    exact hg₂s.add hsc
  · intro u
    show g₂ (-u) + lam * g₁ (-u) = g₂ u + lam * g₁ u
    rw [hg₁, hg₂, symmetrize_even, symmetrize_even]
  · rw [poleOddResp_add_smul hg₂c hg₂s hg₁c hg₁s, hlam]
    field_simp
    ring
  · rw [oddResp_add_smul hg₂c hg₂s hg₁c hg₁s]
    have : 0 < oddResp g₂ α r + lam * oddResp g₁ α r := by positivity
    linarith

/-- The construction for arbitrary nonzero height and ordinate, by the two sign
symmetries of the responses. -/
theorem exists_taper_poleOdd_zero_oddResp_ne_zero {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleOddResp g t r = 0 ∧ oddResp g α r ≠ 0 := by
  obtain ⟨g, r, h1, h2, h3, h4, h5, h6⟩ :=
    exists_taper_poleOdd_zero_oddResp_ne_zero_pos (α := |α|) (t := |t|)
      (abs_pos.mpr hα) (abs_pos.mpr ht)
  refine ⟨g, r, h1, h2, h3, h4, ?_, ?_⟩
  · rcases abs_cases t with ⟨he, -⟩ | ⟨he, -⟩
    · rwa [← he]
    · have : t = -|t| := by rw [he]; ring
      rw [this, poleOddResp_neg_ordinate, h5, neg_zero]
  · rcases abs_cases α with ⟨he, -⟩ | ⟨he, -⟩
    · rwa [← he]
    · have : α = -|α| := by rw [he]; ring
      rw [this, oddResp_neg_height]
      simpa using h6

/-! ## The transversality consequence -/

/-- **`Q_target ≠ 0` from a vanishing odd pole response.**  If the odd pole
response vanishes at the sample radius while the odd target response does not,
the target parity vector is not in the pole space. -/
theorem target_quotient_ne_zero_of_poleOdd_zero {g : ℝ → ℝ} {α t r : ℝ}
    (hpole : poleOddResp g t r = 0) (htarget : oddResp g α r ≠ 0) :
    qcls g t r (targetParityVec g α r) ≠ 0 := by
  intro hzero
  rw [qcls_eq_zero_iff, poleSpace, Submodule.mem_span_pair] at hzero
  obtain ⟨c₁, c₂, hc⟩ := hzero
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp only [targetParityVec, evenPattern, oddPattern, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  rw [hpole] at e0 e1
  exact htarget (by linarith)

/-- **The odd-channel transversality for the constructed taper.** -/
theorem literalWeilOddChannelTargetTransverse {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ qcls g t r (targetParityVec g α r) ≠ 0 := by
  obtain ⟨g, r, h1, h2, h3, h4, h5, h6⟩ := exists_taper_poleOdd_zero_oddResp_ne_zero hα ht
  exact ⟨g, r, h1, h2, h3, h4, target_quotient_ne_zero_of_poleOdd_zero h5 h6⟩

/-- **`literalWeilOffLineNuisanceTransverse`.**  For an actual nontrivial zero
`ρ* = 1/2 + α + it` of `riemannZeta` with `α ≠ 0` (off the critical line) and
`t ≠ 0`, there is an even `C²` compactly supported taper and a positive sample
radius for which the literal zeta Weil explicit formula supplies a four-sample
balance relation whose pole part is killed by the parity quotient, whose target
class equals minus the class of the remaining contributions, and for which

  `Q_other + Q_prime + Q_Γ ≠ 0`.

Nothing is assumed: the balance relation comes from the explicit formula and the
transversality from the explicit taper. -/
theorem literalWeilOffLineNuisanceTransverse {ρstar : Zeros} {α t : ℝ}
    (hre : (ρstar : ℂ).re = 1 / 2 + α) (him : (ρstar : ℂ).im = t)
    (hα : α ≠ 0) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r
      ∧ (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g α r
          + otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
          + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0)
      ∧ qcls g t r (poleVec (sampleFam g t r)) = 0
      ∧ qcls g t r (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g α r)
          = -qcls g t r (otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
              + gammaVec (sampleFam g t r))
      ∧ qcls g t r (otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
          + gammaVec (sampleFam g t r)) ≠ 0 := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hpole, htarget⟩ :=
    exists_taper_poleOdd_zero_oddResp_ne_zero hα ht
  obtain ⟨hbal, hmem⟩ :=
    literalWeilFourSampleParityBalance hgs hgc heven hre him r
  obtain ⟨h1, h2, h3⟩ := parityQuotientBalance hmem hbal
  have hmult : ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) ≠ 0 := by
    have := (Zeta23.zetaZeroConfig).one_le_mult ρstar ρstar.2
    positivity
  refine ⟨g, r, hgs, hgc, heven, hrpos, hbal, h1, h2, h3 ?_⟩
  rw [qcls_smul]
  intro hzero
  rcases smul_eq_zero.mp hzero with h | h
  · exact hmult h
  · exact target_quotient_ne_zero_of_poleOdd_zero hpole htarget h

end LiteralWeilOddChannelTaper
end Zeta23Bridge
