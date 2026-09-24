/-
# Narrow-window domination: the Schur remainder is paid for by the window width

The two-taper determinant of leading responses splits exactly (`targetLeadingCoeff_det_expand`)
as

    4 λ² · (cross determinant)  +  detRest,

and `abs_detRest_le` bounds `|detRest|` by the nonnegative polynomial `detRestBound`
in the ten window responses.  Every monomial of `detRestBound` carries at least one
*within-window self response*, while the cross determinant is bounded below by a
product of *cross-window responses* times the strict endpoint ratio gap.

For unit-mass tapers in symmetric windows of half-width `e` around three fixed
ordered centres `0 < c₀ < c₁ < c₂`:

* every self response is at most `responseCap x (c-e) (c+e)`, which **vanishes at
  `e = 0`**;
* every cross response is at least `responseFloor x (c+e) (c'-e)`, which tends to the
  **strictly positive** constant `3/4 (c'² - c²)(cosh (x c') - cosh (x c))`;
* the endpoint ratio gap is `gateDefect / denomProduct`, and `gateDefect` is strictly
  positive at `e = 0` by the point-window TP₂ gate.

Consequently the division-free comparison

    endpointBudget · denomProduct  <  marginFloor · gateDefect

holds at `e = 0` (its left side is `0`), hence for all sufficiently narrow windows by
continuity.  That is exactly the domination hypothesis `hdom` of the Schur admission
gate, so `hdom` is no longer a hypothesis: it is produced by an explicit family of
tent tapers.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilNormalizedWindowBounds
import Zeta23Bridge.LiteralWeilWindowSeparationInstance
import Zeta23Bridge.LiteralWeilDetRestBoundMonotonicity

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace LiteralWeilNarrowWindowDomination

open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilNormalizedWindowBounds
open Zeta23Bridge.LiteralWeilWindowSeparationInstance
open Zeta23Bridge.LiteralWeilDetRestBoundMonotonicity
open Zeta23Bridge.CoshWindowSeparation

/-! ## The cross determinant at the level of the polarised form -/

/-- The polarised version of `crossIntegral_det_ge`: the cross determinant of the
`covForm` responses is at least the product of the two `a`-responses times the
endpoint ratio gap. -/
theorem covForm_det_ge {p q0 q1 : ℝ → ℝ} {al0 be0 al1 be1 al2 be2 a b : ℝ}
    (hp : WindowTaper p al0 be0) (hq0 : WindowTaper q0 al1 be1) (hq1 : WindowTaper q1 al2 be2)
    (ha : 0 < a) (hab : a < b) (hal0 : 0 < al0) (h0 : al0 ≤ be0) (h01 : be0 < al1)
    (h1 : al1 ≤ be1) (h12 : be1 < al2) :
    covForm p q0 a * covForm p q1 a
        * (coshDiff b al0 al2 / coshDiff a al0 al2 - coshDiff b be0 be1 / coshDiff a be0 be1)
      ≤ covForm p q0 a * covForm p q1 b - covForm p q1 a * covForm p q0 b := by
  have hbase := crossIntegral_det_ge hp hq0 hq1 ha hab hal0 h0 h01 h1 h12
  rw [covForm_eq_crossIntegral' hp.cont hp.cpt hq0.cont hq0.cpt,
    covForm_eq_crossIntegral' hp.cont hp.cpt hq0.cont hq0.cpt,
    covForm_eq_crossIntegral' hp.cont hp.cpt hq1.cont hq1.cpt,
    covForm_eq_crossIntegral' hp.cont hp.cpt hq1.cont hq1.cpt]
  nlinarith [hbase]

/-! ## The endpoint model of the narrow-window family -/

/-- The endpoint budget: `endpointDetRestBound` evaluated at the geometric caps of the
symmetric windows of half-width `e` around `c₀ < c₁ < c₂`. -/
def endpointBudget (lam a b c0 c1 c2 e : ℝ) : ℝ :=
  endpointDetRestBound lam
    (responseCap a (c0 - e) (c0 + e)) (responseCap b (c0 - e) (c0 + e))
    (responseCap a (c1 - e) (c1 + e)) (responseCap b (c1 - e) (c1 + e))
    (responseCap a (c2 - e) (c2 + e)) (responseCap b (c2 - e) (c2 + e))
    (responseCap a (c0 - e) (c1 + e)) (responseCap b (c0 - e) (c1 + e))
    (responseCap a (c0 - e) (c2 + e)) (responseCap b (c0 - e) (c2 + e))

/-- The geometric floor of `4 λ²` times the product of the two `a`-cross-responses. -/
def marginFloor (lam a c0 c1 c2 e : ℝ) : ℝ :=
  4 * lam ^ 2 * (responseFloor a (c0 + e) (c1 - e) * responseFloor a (c0 + e) (c2 - e))

/-- The (positive) denominator of the endpoint ratio gap. -/
def denomProduct (a c0 c1 c2 e : ℝ) : ℝ :=
  coshDiff a (c0 - e) (c2 - e) * coshDiff a (c0 + e) (c1 + e)

/-- The division-free domination defect. -/
def dominationDefect (lam a b c0 c1 c2 e : ℝ) : ℝ :=
  marginFloor lam a c0 c1 c2 e * gateDefect a b c0 c1 c2 e
    - endpointBudget lam a b c0 c1 c2 e * denomProduct a c0 c1 c2 e

theorem continuous_endpointBudget (lam a b c0 c1 c2 : ℝ) :
    Continuous (endpointBudget lam a b c0 c1 c2) := by
  unfold endpointBudget endpointDetRestBound responseCap coshDiff
  fun_prop

theorem continuous_marginFloor (lam a c0 c1 c2 : ℝ) :
    Continuous (marginFloor lam a c0 c1 c2) := by
  unfold marginFloor responseFloor coshDiff
  fun_prop

theorem continuous_denomProduct (a c0 c1 c2 : ℝ) :
    Continuous (denomProduct a c0 c1 c2) := by
  unfold denomProduct coshDiff
  fun_prop

theorem continuous_dominationDefect (lam a b c0 c1 c2 : ℝ) :
    Continuous (dominationDefect lam a b c0 c1 c2) := by
  unfold dominationDefect
  exact ((continuous_marginFloor lam a c0 c1 c2).mul
      (continuous_gateDefect a b c0 c1 c2)).sub
    ((continuous_endpointBudget lam a b c0 c1 c2).mul (continuous_denomProduct a c0 c1 c2))

/-- **The self responses vanish at zero window width**, hence so does the whole
endpoint budget: every monomial of the quartic remainder carries a self response. -/
theorem endpointBudget_zero (lam a b c0 c1 c2 : ℝ) : endpointBudget lam a b c0 c1 c2 0 = 0 := by
  have h : ∀ x c : ℝ, responseCap x (c - 0) (c + 0) = 0 := by
    intro x c
    simp [responseCap, coshDiff]
  unfold endpointBudget endpointDetRestBound
  rw [h a c0, h b c0, h a c1, h b c1, h a c2, h b c2]
  ring

/-- At zero window width the domination defect is the strictly positive product of the
two cross-response floors with the point-window TP₂ gate. -/
theorem dominationDefect_zero_pos {lam a b c0 c1 c2 : ℝ} (hlam : lam ≠ 0) (ha : 0 < a)
    (hab : a < b) (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    0 < dominationDefect lam a b c0 c1 c2 0 := by
  have hgate := gateDefect_zero_pos ha hab hc0 h01 h12
  have hF0 : 0 < responseFloor a (c0 + 0) (c1 - 0) := by
    simpa using responseFloor_pos ha hc0 h01
  have hF1 : 0 < responseFloor a (c0 + 0) (c2 - 0) := by
    simpa using responseFloor_pos ha hc0 (h01.trans h12)
  have hlam2 : 0 < lam ^ 2 := by positivity
  have hmargin : 0 < marginFloor lam a c0 c1 c2 0 := by
    unfold marginFloor
    positivity
  unfold dominationDefect
  rw [endpointBudget_zero]
  have : 0 < marginFloor lam a c0 c1 c2 0 * gateDefect a b c0 c1 c2 0 := mul_pos hmargin hgate
  linarith

/-- **A narrow radius exists.**  For every nonzero `λ`, every pair of heights
`0 < a < b` and every triple of ordered centres, all sufficiently narrow symmetric
windows satisfy simultaneously the geometric ordering, the four-endpoint gate and the
division-free domination inequality. -/
theorem exists_narrow_radius {lam a b c0 c1 c2 : ℝ} (hlam : lam ≠ 0) (ha : 0 < a)
    (hab : a < b) (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℝ, 0 < e → e ≤ e0 →
      e < c0 ∧ c0 + e < c1 - e ∧ c1 + e < c2 - e ∧
        0 < gateDefect a b c0 c1 c2 e ∧ 0 < dominationDefect lam a b c0 c1 c2 e := by
  have hopen : IsOpen {e : ℝ | 0 < gateDefect a b c0 c1 c2 e ∧
      0 < dominationDefect lam a b c0 c1 c2 e} :=
    (isOpen_lt continuous_const (continuous_gateDefect a b c0 c1 c2)).inter
      (isOpen_lt continuous_const (continuous_dominationDefect lam a b c0 c1 c2))
  have hmem : (0 : ℝ) ∈ {e : ℝ | 0 < gateDefect a b c0 c1 c2 e ∧
      0 < dominationDefect lam a b c0 c1 c2 e} :=
    ⟨gateDefect_zero_pos ha hab hc0 h01 h12,
      dominationDefect_zero_pos hlam ha hab hc0 h01 h12⟩
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  set e0 : ℝ := min (min (eps / 2) (c0 / 2)) (min ((c1 - c0) / 4) ((c2 - c1) / 4)) with he0
  have he1 : e0 ≤ eps / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have he2 : e0 ≤ c0 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have he3 : e0 ≤ (c1 - c0) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have he4 : e0 ≤ (c2 - c1) / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have he0pos : 0 < e0 := by
    rw [he0]
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  refine ⟨e0, he0pos, fun e hepos hele => ?_⟩
  have hin : e ∈ Metric.ball (0 : ℝ) eps := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hepos]
    linarith
  obtain ⟨hg, hd⟩ := hball hin
  exact ⟨by linarith, by linarith, by linarith, hg, hd⟩

/-! ## The explicit narrow window tapers -/

/-- The unit-mass tent taper of the symmetric modulus window of half-width `e` around
the centre `c`. -/
def narrowTaper (c e : ℝ) : ℝ → ℝ := normalized (tentTaper (c - e) (c + e))

theorem narrowTaper_window {c e : ℝ} (hc : 0 < c - e) (he : 0 < e) :
    WindowTaper (narrowTaper c e) (c - e) (c + e) :=
  windowTaper_normalized (exists_windowTaper hc (by linarith))

theorem narrowTaper_mass {c e : ℝ} (hc : 0 < c - e) (he : 0 < e) :
    (∫ u : ℝ, narrowTaper c e u) = 1 :=
  integral_normalized (exists_windowTaper hc (by linarith)).mass

/-! ## The domination theorem -/

/-- **The domination hypothesis is now a theorem.**  For every nonzero `λ`, every pair
of heights `0 < a < b` and every triple of ordered centres `0 < c₀ < c₁ < c₂` there is
an explicit triple of unit-mass tent window tapers, in symmetric windows of a common
narrow half-width, for which the four-endpoint gate holds *and* the self-response
remainder bound is strictly below the cross determinant margin. -/
theorem exists_windowTriple_detRestBound_lt {lam a b c0 c1 c2 : ℝ} (hlam : lam ≠ 0)
    (ha : 0 < a) (hab : a < b) (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    ∃ (p q0 q1 : ℝ → ℝ) (al0 be0 al1 be1 al2 be2 : ℝ),
      WindowTaper p al0 be0 ∧ WindowTaper q0 al1 be1 ∧ WindowTaper q1 al2 be2 ∧
      (∫ u : ℝ, p u) = 1 ∧ (∫ u : ℝ, q0 u) = 1 ∧ (∫ u : ℝ, q1 u) = 1 ∧
      0 < al0 ∧ al0 ≤ be0 ∧ be0 < al1 ∧ al1 ≤ be1 ∧ be1 < al2 ∧ al2 ≤ be2 ∧
      coshDiff b be0 be1 * coshDiff a al0 al2 < coshDiff b al0 al2 * coshDiff a be0 be1 ∧
      detRestBound p q0 q1 lam a b <
        4 * lam ^ 2 * (covForm p q0 a * covForm p q1 b - covForm p q1 a * covForm p q0 b) := by
  obtain ⟨e0, he0pos, hall⟩ := exists_narrow_radius hlam ha hab hc0 h01 h12
  obtain ⟨hec0, hord1, hord2, hgate, hdefect⟩ := hall e0 he0pos le_rfl
  set e : ℝ := e0 with hedef
  have hepos : 0 < e := he0pos
  have hb : 0 < b := ha.trans hab
  -- the three windows
  have hp0 : 0 < c0 - e := by linarith
  have hp1 : 0 < c1 - e := by linarith
  have hp2 : 0 < c2 - e := by linarith
  have hp : WindowTaper (narrowTaper c0 e) (c0 - e) (c0 + e) := narrowTaper_window hp0 hepos
  have hq0 : WindowTaper (narrowTaper c1 e) (c1 - e) (c1 + e) := narrowTaper_window hp1 hepos
  have hq1 : WindowTaper (narrowTaper c2 e) (c2 - e) (c2 + e) := narrowTaper_window hp2 hepos
  have hpm : (∫ u : ℝ, narrowTaper c0 e u) = 1 := narrowTaper_mass hp0 hepos
  have hq0m : (∫ u : ℝ, narrowTaper c1 e u) = 1 := narrowTaper_mass hp1 hepos
  have hq1m : (∫ u : ℝ, narrowTaper c2 e u) = 1 := narrowTaper_mass hp2 hepos
  -- the widened brackets used for the two cross responses
  have hpw1 : WindowTaper (narrowTaper c0 e) (c0 - e) (c1 + e) :=
    hp.mono le_rfl (by linarith)
  have hq0w : WindowTaper (narrowTaper c1 e) (c0 - e) (c1 + e) :=
    hq0.mono (by linarith) le_rfl
  have hpw2 : WindowTaper (narrowTaper c0 e) (c0 - e) (c2 + e) :=
    hp.mono le_rfl (by linarith)
  have hq1w : WindowTaper (narrowTaper c2 e) (c0 - e) (c2 + e) :=
    hq1.mono (by linarith) le_rfl
  -- the four-endpoint gate
  have hgate' : coshDiff b (c0 + e) (c1 + e) * coshDiff a (c0 - e) (c2 - e)
      < coshDiff b (c0 - e) (c2 - e) * coshDiff a (c0 + e) (c1 + e) := by
    unfold gateDefect at hgate
    linarith
  -- the ten endpoint caps
  have capPa := targetLeadingCoeff_le_unitMass hp hpm ha hp0
  have capPb := targetLeadingCoeff_le_unitMass hp hpm hb hp0
  have capQ0a := targetLeadingCoeff_le_unitMass hq0 hq0m ha hp1
  have capQ0b := targetLeadingCoeff_le_unitMass hq0 hq0m hb hp1
  have capQ1a := targetLeadingCoeff_le_unitMass hq1 hq1m ha hp2
  have capQ1b := targetLeadingCoeff_le_unitMass hq1 hq1m hb hp2
  have capC0a := covForm_le_unitMass hpw1 hq0w hpm hq0m ha hp0
  have capC0b := covForm_le_unitMass hpw1 hq0w hpm hq0m hb hp0
  have capC1a := covForm_le_unitMass hpw2 hq1w hpm hq1m ha hp0
  have capC1b := covForm_le_unitMass hpw2 hq1w hpm hq1m hb hp0
  -- the two cross-response floors
  have floor0 : responseFloor a (c0 + e) (c1 - e) ≤ covForm (narrowTaper c0 e) (narrowTaper c1 e) a :=
    covForm_ge_unitMass hp hq0 hpm hq0m ha hp0 (by linarith) (by linarith)
  have floor1 : responseFloor a (c0 + e) (c2 - e) ≤ covForm (narrowTaper c0 e) (narrowTaper c2 e) a :=
    covForm_ge_unitMass hp hq1 hpm hq1m ha hp0 (by linarith) (by linarith)
  have hF0pos : 0 < responseFloor a (c0 + e) (c1 - e) :=
    responseFloor_pos ha (by linarith) (by linarith)
  have hF1pos : 0 < responseFloor a (c0 + e) (c2 - e) :=
    responseFloor_pos ha (by linarith) (by linarith)
  -- the endpoint ratio gap
  have hDtop : 0 < coshDiff a (c0 - e) (c2 - e) := coshDiff_pos ha hp0 (by linarith)
  have hDbot : 0 < coshDiff a (c0 + e) (c1 + e) := coshDiff_pos ha (by linarith) (by linarith)
  have hden : 0 < denomProduct a c0 c1 c2 e := by
    unfold denomProduct
    exact mul_pos hDtop hDbot
  have hgapeq : coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
      - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e)
      = gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e := by
    unfold gateDefect denomProduct
    field_simp
  have hgapnn : 0 ≤ coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
      - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e) := by
    rw [hgapeq]
    exact (div_pos hgate hden).le
  -- the cross determinant is at least the geometric floor times the gap
  have hdet := covForm_det_ge hp hq0 hq1 ha hab hp0 (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hfloorprod :
      responseFloor a (c0 + e) (c1 - e) * responseFloor a (c0 + e) (c2 - e)
          * (coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
            - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e))
        ≤ covForm (narrowTaper c0 e) (narrowTaper c1 e) a
            * covForm (narrowTaper c0 e) (narrowTaper c2 e) a
          * (coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
            - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e)) := by
    have h1 : 0 ≤ covForm (narrowTaper c0 e) (narrowTaper c1 e) a := le_trans hF0pos.le floor0
    refine mul_le_mul_of_nonneg_right ?_ hgapnn
    exact mul_le_mul floor0 floor1 hF1pos.le h1
  -- the budget comparison
  have hbudget : endpointBudget lam a b c0 c1 c2 e
      < marginFloor lam a c0 c1 c2 e
        * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e) := by
    rw [← mul_div_assoc, lt_div_iff₀ hden]
    unfold dominationDefect at hdefect
    linarith
  have hmarginle : marginFloor lam a c0 c1 c2 e
        * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e)
      ≤ 4 * lam ^ 2 *
        (covForm (narrowTaper c0 e) (narrowTaper c1 e) a
            * covForm (narrowTaper c0 e) (narrowTaper c2 e) b
          - covForm (narrowTaper c0 e) (narrowTaper c2 e) a
            * covForm (narrowTaper c0 e) (narrowTaper c1 e) b) := by
    have hlam2 : (0:ℝ) < 4 * lam ^ 2 := by positivity
    have hchain :
        responseFloor a (c0 + e) (c1 - e) * responseFloor a (c0 + e) (c2 - e)
            * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e)
          ≤ covForm (narrowTaper c0 e) (narrowTaper c1 e) a
              * covForm (narrowTaper c0 e) (narrowTaper c2 e) b
            - covForm (narrowTaper c0 e) (narrowTaper c2 e) a
              * covForm (narrowTaper c0 e) (narrowTaper c1 e) b := by
      rw [← hgapeq]
      exact hfloorprod.trans hdet
    unfold marginFloor
    nlinarith [hchain, hlam2]
  -- transport the ten caps through the quartic remainder polynomial
  have hmono := detRestBound_mono (lam := lam) hp.cont hp.cpt hq0.cont hq0.cpt hq1.cont hq1.cpt
    hp.nonneg hq0.nonneg hq1.nonneg capPa capPb capQ0a capQ0b capQ1a capQ1b
    capC0a capC0b capC1a capC1b
  refine ⟨narrowTaper c0 e, narrowTaper c1 e, narrowTaper c2 e,
    c0 - e, c0 + e, c1 - e, c1 + e, c2 - e, c2 + e, hp, hq0, hq1, hpm, hq0m, hq1m,
    hp0, by linarith, by linarith, by linarith, by linarith, by linarith, hgate', ?_⟩
  calc detRestBound (narrowTaper c0 e) (narrowTaper c1 e) (narrowTaper c2 e) lam a b
      ≤ endpointBudget lam a b c0 c1 c2 e := hmono
    _ < marginFloor lam a c0 c1 c2 e
        * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e) := hbudget
    _ ≤ _ := hmarginle

end LiteralWeilNarrowWindowDomination
end Zeta23Bridge
