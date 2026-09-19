import Zeta23.GammaFacts.Series
import Zeta23Bridge.LiteralWeilGammaChannel

/-!
# Order structure of the gamma bracket

The vendored digamma partial fractions imply that

  B(x) = Re digamma(1/4 + i x/2) - log pi

is minimized at x=0.

At the elementary level,

  Re (1 / (a + i y)) = a / (a^2 + y^2),

so for a>0 this real reciprocal decreases when |y| grows.  Every such
reciprocal enters Re digamma with a minus sign.

This file formalizes that order structure from the already-proved summable
digamma series.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

def gammaSeriesPoint (x : ℝ) : ℂ :=
  (1/4 : ℂ) + Complex.I * ((x/2 : ℝ) : ℂ)

theorem gammaSeriesPoint_re (x : ℝ) :
    (gammaSeriesPoint x).re = 1/4 := by
  simp [gammaSeriesPoint]

theorem gammaSeriesPoint_im (x : ℝ) :
    (gammaSeriesPoint x).im = x/2 := by
  simp [gammaSeriesPoint]

theorem gammaSeriesPoint_integerComplement (x : ℝ) :
    gammaSeriesPoint x ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp [gammaSeriesPoint] at hre
  have h4 : (4 * k : ℤ) = 1 := by
    have hr : (4 : ℝ) * k = 1 := by
      rw [hre]
      norm_num
    exact_mod_cast hr
  omega

theorem real_one_div_add_I
    {a y : ℝ} (ha : a ≠ 0 ∨ y ≠ 0) :
    (1 / ((a : ℂ) + Complex.I * (y : ℂ))).re
      = a / (a^2 + y^2) := by
  have hne : ((a : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp at hr hi
    exact ha.elim (fun ha0 => ha0 hr) (fun hy0 => hy0 hi)
  rw [one_div]
  rw [Complex.inv_def]
  simp [Complex.normSq_apply]
  push_cast
  ring

theorem real_reciprocal_le_at_zero
    {a y : ℝ} (ha : 0 < a) :
    (1 / ((a : ℂ) + Complex.I * (y : ℂ))).re
      <= (1 / (a : ℂ)).re := by
  rw [real_one_div_add_I (Or.inl ha.ne')]
  have hzero :
      (1 / (a : ℂ)).re = 1/a := by
    push_cast
    simp [ha.ne']
  rw [hzero]
  have hden : 0 < a^2 + y^2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg y]
  rw [div_le_iff₀ hden]
  have ha0 : 0 <= a := ha.le
  have hsq : 0 <= y^2 := sq_nonneg y
  field_simp [ha.ne']
  nlinarith

def digammaTailTerm (x : ℝ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1)
    - 1 / (gammaSeriesPoint x + n + 1)

theorem digammaTailTerm_re_mono_zero
    (x : ℝ) (n : ℕ) :
    (digammaTailTerm 0 n).re
      <= (digammaTailTerm x n).re := by
  unfold digammaTailTerm
  simp only [map_sub]
  have ha : 0 < (n : ℝ) + 5/4 := by positivity
  have hx :
      (gammaSeriesPoint x + n + 1)
        =
      (((n : ℝ) + 5/4 : ℝ) : ℂ)
        + Complex.I * (((x/2 : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [gammaSeriesPoint] <;> ring
  have h0 :
      (gammaSeriesPoint 0 + n + 1)
        =
      (((n : ℝ) + 5/4 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [gammaSeriesPoint] <;> ring
  rw [hx, h0]
  have hrec :=
    real_reciprocal_le_at_zero
      (a := (n : ℝ) + 5/4) (y := x/2) ha
  linarith

theorem summable_digammaTailTerm (x : ℝ) :
    Summable (digammaTailTerm x) := by
  unfold digammaTailTerm
  simpa [gammaSeriesPoint, add_assoc] using
    Zeta23.DigammaSeries.summable_digamma_series
      (gammaSeriesPoint_integerComplement x)

theorem tsum_digammaTailTerm_re_mono_zero (x : ℝ) :
    (∑' n : ℕ, (digammaTailTerm 0 n).re)
      <= ∑' n : ℕ, (digammaTailTerm x n).re := by
  have h0 : Summable (fun n : ℕ => (digammaTailTerm 0 n).re) :=
    (Complex.hasSum_re (summable_digammaTailTerm 0).hasSum).summable
  have hx : Summable (fun n : ℕ => (digammaTailTerm x n).re) :=
    (Complex.hasSum_re (summable_digammaTailTerm x).hasSum).summable
  exact h0.tsum_le_tsum (fun n => digammaTailTerm_re_mono_zero x n) hx

theorem digammaSeriesPoint_re_formula (x : ℝ) :
    (Complex.digamma (gammaSeriesPoint x)).re
      =
    -Real.eulerMascheroniConstant
      - (1 / gammaSeriesPoint x).re
      + ∑' n : ℕ, (digammaTailTerm x n).re := by
  have hs :=
    Zeta23.DigammaSeries.digamma_series
      (gammaSeriesPoint_integerComplement x)
  rw [hs]
  simp only [map_add, map_sub, map_neg, Complex.ofReal_re]
  have hsum :
      (∑' n : ℕ, digammaTailTerm x n).re
        = ∑' n : ℕ, (digammaTailTerm x n).re :=
    Complex.re_tsum (summable_digammaTailTerm x)
  rw [hsum]
  rfl

theorem digamma_real_zero_le (x : ℝ) :
    (Complex.digamma (gammaSeriesPoint 0)).re
      <= (Complex.digamma (gammaSeriesPoint x)).re := by
  rw [digammaSeriesPoint_re_formula, digammaSeriesPoint_re_formula]
  have htail := tsum_digammaTailTerm_re_mono_zero x
  have hhead :
      (1 / gammaSeriesPoint x).re
        <= (1 / gammaSeriesPoint 0).re := by
    have hx :
        gammaSeriesPoint x
          = ((1/4 : ℝ) : ℂ) + Complex.I * ((x/2 : ℝ) : ℂ) := by
      rfl
    have h0 :
        gammaSeriesPoint 0 = ((1/4 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [gammaSeriesPoint]
    rw [hx, h0]
    exact real_reciprocal_le_at_zero
      (a := (1/4 : ℝ)) (y := x/2) (by norm_num)
  linarith

theorem gammaBracket_zero_le (x : ℝ) :
    Zeta23.EF.gammaBracket 0 <= Zeta23.EF.gammaBracket x := by
  unfold Zeta23.EF.gammaBracket
  have h := digamma_real_zero_le x
  simpa [gammaSeriesPoint] using h

end Synthesis
