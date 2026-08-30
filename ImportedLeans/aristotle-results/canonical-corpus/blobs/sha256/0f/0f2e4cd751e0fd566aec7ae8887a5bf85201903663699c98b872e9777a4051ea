/-
# Row A1a — the cheapest nonzero positive patch, computed

`WilsonCubicVertex` shows the literal Wilson cubic vertex vanishes on the corner
(Brillouin-boundary) witness and equals `1` at the quarter momentum.  This file
turns the second, positive statement into a *patch* statement, which is what the
enclosure of `PositivePatchEnclosure` consumes: on the slab of half-width `1/8`
around normalised momentum `1/4` — a box of volume exactly `1/32` — the vertex
component stays above `√2/2`.

* `sin_ge_sqrt2_div_two_of_mem_quarter` : `sin t ≥ √2/2` for `t ∈ [π/4, 3π/4]`.
* `wilsonCubicBgZero_diag_ge_on_quarterSlab` : the component `Γ_{μμρ}(q,−q,0)`
  is at least `√2/2` on the whole slab, for every `μ ≠ ρ`.
* `wilsonPatchFloor_value` : the resulting patch floor
  `vol × bound = (1/32)·(√2/2) = √2/64`.
* `latticeCellFloor_quarterSlab_eighth` : if the reduced bubble entry inherits
  that bound on the same slab, the Gaussian floor is the explicit number
  `1/128`.

This is a *conditional* numerical statement: it says what the floor is on the
patch on which the Wilson piece is bounded below, not that Bałaban's constrained
first variation (which also contains the averaging and projection variations,
`FirstVariationDecomposition`) satisfies that bound.
-/
import RequestProject.YangMills.PatchGaussianFloor
import RequestProject.YangMills.WilsonCubicVertex

namespace YangMills

open Real Set MeasureTheory Matrix

/-- `sin` stays above `√2/2` on the middle half `[π/4, 3π/4]` of its positive
arch. -/
theorem sin_ge_sqrt2_div_two_of_mem_quarter {t : ℝ} (h1 : π / 4 ≤ t)
    (h2 : t ≤ 3 * π / 4) : Real.sqrt 2 / 2 ≤ Real.sin t := by
  have hpi := Real.pi_pos
  rcases le_total t (π / 2) with h | h
  · have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 4) (y := t)
      (by linarith) h h1
    rwa [Real.sin_pi_div_four] at hm
  · have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 4) (y := π - t)
      (by linarith) (by linarith) (by linarith)
    rw [Real.sin_pi_div_four, Real.sin_pi_sub] at hm
    exact hm

/-- **The positive patch, computed on the literal vertex.**  On the slab of
half-width `1/8` around normalised momentum `1/4` in direction `ρ`, the
component of the Wilson cubic vertex with equal fluctuation indices `μ ≠ ρ`
stays above `√2/2`. -/
theorem wilsonCubicBgZero_diag_ge_on_quarterSlab {mu rho : Fin 4} (h : mu ≠ rho)
    {q : Fin 4 → ℝ} (hq : q ∈ quarterSlab rho (1 / 8)) :
    Real.sqrt 2 / 2 ≤ wilsonCubicBgZero q mu mu rho := by
  have hpi := Real.pi_pos
  have hrho : q rho ∈ Icc (1 / 4 - 1 / 8 : ℝ) (1 / 4 + 1 / 8) := by
    simpa [quarterSlab] using hq rho (mem_univ rho)
  have h1 : π / 4 ≤ π * (2 * q rho) := by
    have := hrho.1
    nlinarith
  have h2 : π * (2 * q rho) ≤ 3 * π / 4 := by
    have := hrho.2
    nlinarith
  rw [wilsonCubicBgZero_diag, if_neg h]
  have := sin_ge_sqrt2_div_two_of_mem_quarter h1 h2
  linarith

/-- The patch floor produced by that box: volume `1/32` times the bound `√2/2`. -/
theorem wilsonPatchFloor_value :
    ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2) = Real.sqrt 2 / 64 := by
  ring

/-- The slab of half-width `1/8` has volume exactly `1/32`. -/
theorem quarterSlab_eighth_volume_real (rho : Fin 4) :
    (volume (quarterSlab rho (1 / 8))).toReal = 1 / 32 := by
  rw [quarterSlab_volume_real (by norm_num) rho]
  norm_num

/-- **An explicit conditional Gaussian floor.**  If the reduced bubble entry of
the first background variation is at least `√2/2` on the slab of half-width
`1/8` around normalised momentum `1/4`, then — with the paramagnetic sign datum
supplying the sign on the complement — the Gaussian coefficient is at least
`1/128`. -/
theorem latticeCellFloor_quarterSlab_eighth
    {V S W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (rho : Fin 4)
    (hV : ∀ q, (V q)ᵀ = V q) (hS : ∀ q, S q = -((W q)ᵀ * W q))
    (hint : IntegrableOn (fun q => betaTrace (latticeSymbolOf q) (V q) (V q) (S q))
      puncturedCell)
    (hentry : ∀ q ∈ quarterSlab rho (1 / 8),
      Real.sqrt 2 / 2 ≤ |(latticeGramFactor q * V q * (latticeGramFactor q)ᵀ) 0 0|) :
    (1 : ℝ) / 128
      ≤ cellGaussianCoefficient
          (fun q => betaTrace (latticeSymbolOf q) (V q) (V q) (S q)) := by
  have hsqrt : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hmain := latticeCellFloor_of_patchEntry (V := V) (S := S) (W := W)
    (c := Real.sqrt 2 / 2) (delta := 1 / 8) rho (by norm_num) (by norm_num) hsqrt
    hV hS hint hentry
  have hval : ((1 : ℝ) / 8) / 4 * ((Real.sqrt 2 / 2) ^ 2 / 2) = 1 / 128 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h2]
    norm_num
  rwa [hval] at hmain

end YangMills
