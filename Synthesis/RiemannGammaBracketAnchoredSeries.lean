import Synthesis.RiemannGammaBracketOrder
import Synthesis.RiemannLorentzianCosFTConvolution

/-!
# Anchored Lorentzian series for the literal Gamma bracket

The divergent harmonic constants in the digamma expansion disappear after
anchoring at x=0.  The literal bracket becomes

  B(x) = B(0)
    + (L_{1/4}(0)-L_{1/4}(x))
    + sum_n (L_{n+5/4}(0)-L_{n+5/4}(x)),

where L_a(x)=a/(a^2+x^2/4).

Every increment is nonnegative.  This form is designed for centered tapers:
the B(0) and L_a(0) constants integrate to zero because integral cosFT h = 0.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

def gammaHeadIncrement (x : ℝ) : ℝ :=
  digammaLorentzian (1/4) 0 - digammaLorentzian (1/4) x

def gammaTailIncrement (n : ℕ) (x : ℝ) : ℝ :=
  digammaLorentzian ((n:ℝ)+5/4) 0
    - digammaLorentzian ((n:ℝ)+5/4) x

theorem gammaHeadIncrement_nonneg (x : ℝ) :
    0 <= gammaHeadIncrement x := by
  unfold gammaHeadIncrement digammaLorentzian
  have hden : 0 < (1/4 : ℝ)^2 + x^2/4 := by positivity
  field_simp
  nlinarith [sq_nonneg x]

theorem gammaTailIncrement_nonneg (n : ℕ) (x : ℝ) :
    0 <= gammaTailIncrement n x := by
  unfold gammaTailIncrement digammaLorentzian
  have ha : 0 < (n:ℝ)+5/4 := by positivity
  have hden : 0 < ((n:ℝ)+5/4)^2 + x^2/4 := by positivity
  field_simp
  nlinarith [sq_nonneg x]

theorem head_reciprocal_re_eq_lorentzian (x : ℝ) :
    (1 / gammaSeriesPoint x).re
      = digammaLorentzian (1/4) x := by
  have hx :
      gammaSeriesPoint x
        = ((1/4 : ℝ) : ℂ)
          + Complex.I * ((x/2 : ℝ) : ℂ) := by
    rfl
  rw [hx, real_one_div_add_I (Or.inl (by norm_num))]
  unfold digammaLorentzian
  ring

theorem tail_reciprocal_re_eq_lorentzian (n : ℕ) (x : ℝ) :
    (1 / (gammaSeriesPoint x + n + 1)).re
      = digammaLorentzian ((n:ℝ)+5/4) x := by
  have hx :
      (gammaSeriesPoint x + n + 1)
        =
      (((n:ℝ)+5/4 : ℝ) : ℂ)
        + Complex.I * ((x/2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [gammaSeriesPoint] <;> ring
  rw [hx, real_one_div_add_I (Or.inl (by positivity))]
  unfold digammaLorentzian
  ring

theorem digammaTailTerm_re_sub_zero_eq_increment
    (n : ℕ) (x : ℝ) :
    (digammaTailTerm x n).re - (digammaTailTerm 0 n).re
      = gammaTailIncrement n x := by
  unfold digammaTailTerm gammaTailIncrement
  simp only [map_sub]
  rw [tail_reciprocal_re_eq_lorentzian,
      tail_reciprocal_re_eq_lorentzian]
  ring

theorem summable_gammaTailIncrement (x : ℝ) :
    Summable (fun n : ℕ => gammaTailIncrement n x) := by
  have hx : Summable (fun n : ℕ => (digammaTailTerm x n).re) :=
    (Complex.hasSum_re (summable_digammaTailTerm x).hasSum).summable
  have h0 : Summable (fun n : ℕ => (digammaTailTerm 0 n).re) :=
    (Complex.hasSum_re (summable_digammaTailTerm 0).hasSum).summable
  have hd := hx.sub h0
  apply hd.congr
  intro n
  exact digammaTailTerm_re_sub_zero_eq_increment n x

theorem gammaBracket_eq_anchored_lorentzian_series (x : ℝ) :
    Zeta23.EF.gammaBracket x
      =
    Zeta23.EF.gammaBracket 0
      + gammaHeadIncrement x
      + ∑' n : ℕ, gammaTailIncrement n x := by
  unfold Zeta23.EF.gammaBracket
  have hx := digammaSeriesPoint_re_formula x
  have h0 := digammaSeriesPoint_re_formula 0
  rw [hx, h0]
  have hheadx := head_reciprocal_re_eq_lorentzian x
  have hhead0 := head_reciprocal_re_eq_lorentzian 0
  have htail :
      (∑' n : ℕ, (digammaTailTerm x n).re)
        - ∑' n : ℕ, (digammaTailTerm 0 n).re
      =
      ∑' n : ℕ, gammaTailIncrement n x := by
    rw [← tsum_sub
      ((Complex.hasSum_re (summable_digammaTailTerm x).hasSum).summable)
      ((Complex.hasSum_re (summable_digammaTailTerm 0).hasSum).summable)]
    apply tsum_congr
    intro n
    exact digammaTailTerm_re_sub_zero_eq_increment n x
  rw [hheadx, hhead0]
  linarith

def gammaBracketPartial (N : ℕ) (x : ℝ) : ℝ :=
  Zeta23.EF.gammaBracket 0
    + gammaHeadIncrement x
    + ∑ n ∈ Finset.range N, gammaTailIncrement n x

theorem gammaBracketPartial_le (N : ℕ) (x : ℝ) :
    gammaBracketPartial N x <= Zeta23.EF.gammaBracket x := by
  rw [gammaBracket_eq_anchored_lorentzian_series]
  unfold gammaBracketPartial
  gcongr
  exact Summable.sum_le_tsum
    (Finset.range N)
    (fun n _ => gammaTailIncrement_nonneg n x)
    (summable_gammaTailIncrement x)

theorem gammaBracket_zero_le_partial (N : ℕ) (x : ℝ) :
    Zeta23.EF.gammaBracket 0 <= gammaBracketPartial N x := by
  unfold gammaBracketPartial
  have hh := gammaHeadIncrement_nonneg x
  have ht : 0 <= ∑ n ∈ Finset.range N, gammaTailIncrement n x := by
    positivity
  linarith

theorem gammaBracketPartial_tendsto (x : ℝ) :
    Filter.Tendsto (fun N => gammaBracketPartial N x)
      Filter.atTop (nhds (Zeta23.EF.gammaBracket x)) := by
  rw [gammaBracket_eq_anchored_lorentzian_series]
  unfold gammaBracketPartial
  have ht :=
    (summable_gammaTailIncrement x).hasSum.tendsto_sum_nat
  simpa [Finset.sum_filter] using
    (tendsto_const_nhds.add
      (tendsto_const_nhds.add ht))

end Synthesis
