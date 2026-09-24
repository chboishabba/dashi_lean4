/-
# `C53`: the Gaussian Fisher-information budget

The audit of `GaussianLinearBudgetAudit.lean` located the whole remaining
`a`-obstruction in a single term,

  `9AB²·G·K₀`,   `G = sup|∇Φ_a| = 1/(4πa)`,   `K₀ = ∫_cell β′(q)`,

i.e. in the step that replaces the *weighted* gradient pairing by the pointwise
supremum of `|∇Φ_a|` times an unweighted level-set integral.  For a
concentrating weight that step is catastrophically wasteful: the natural
quantity produced by a weighted Young inequality is not `sup|∇Φ|` but the
**Fisher information** of the weight,

  `∫ |∇Φ_a|²/Φ_a = ∫ Φ_a·|∇log Φ_a|²`.

For the Euclidean model `Φ_a = e^{−|x|²/4a}` this is `(3/2)(4π)^{3/2}√a`: the
large logarithmic derivative `|∇log Φ| ≍ a^{−1/2}` is compensated by the
`a^{3/2}` mass of the region where `Φ` actually lives, so the cost **vanishes**
as the weight concentrates, instead of blowing up like `a^{−1}`.

This file proves the torus analogue, for the exactly `ℤ³`-periodic weight
`Φ_a(x) = exp(−Σ_j ψ(x_j−x₀_j)/(4a))` that the development actually uses.  The
estimate is obtained by integrating the weighted quantity exactly — through the
one-dimensional factorisation of `TorusGaussianIntegrals.lean` — and *not* by
bounding `|∇Φ|²/Φ` by its supremum.

* `ClayNS.sq_dvec_div_torusGauss_eq_prod` — the separable identity
  `(∂_iΦ_a)²/Φ_a = tgLapB(u_i)·Π_{j≠i} tgFac(u_j)`;
* `ClayNS.torusGaussFisherInformationBound` (`C53`) —
  `∫_cell |∇Φ_a|²/Φ_a ≤ C_FI·√a`, with the explicit constant
  `C_FI = (3π⁵/2)·√(2π³)`.

Note the contrast with `ClayNS.abs_dvec_torusGauss_le_unif`, which is the
`a^{-1}` sup bound: the same weight, integrated against itself, has a *positive*
scaling dimension.  So `gaussian_gradient_term_blows_up` stays a theorem, but it
is a no-go for the sup-unweighted route only.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.TorusGaussianIntegrals

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The pointwise Fisher-information density -/

/-- The Fisher-information density of the torus Gaussian,
`|∇Φ_a|²/Φ_a = Φ_a|∇log Φ_a|²`. -/
def torusGaussFisher (a : ℝ) (x0 : E3) (z : STime) : ℝ :=
  ∑ i, dvec (0, ee i) (torusGauss a x0) z ^ 2 / torusGauss a x0 z

lemma torusGaussFisher_nonneg (a : ℝ) (x0 : E3) (z : STime) :
    0 ≤ torusGaussFisher a x0 z :=
  Finset.sum_nonneg fun _ _ =>
    div_nonneg (sq_nonneg _) (torusGauss_nonneg a x0 z)

/-- **The separable identity.**  Each coordinate contribution to the Fisher
information is again a product of one-dimensional factors, the distinguished one
being exactly the factor `tgLapB` already used for the Laplacian budget. -/
theorem sq_dvec_div_torusGauss_eq_prod {a : ℝ} (ha : 0 < a) (x0 : E3) (i : Fin 3) (z : STime) :
    dvec (0, ee i) (torusGauss a x0) z ^ 2 / torusGauss a x0 z
      = ∏ j, (if j = i then tgLapB a (z.2 j - x0 j) else tgFac a (z.2 j - x0 j)) := by
  have hP : torusGauss a x0 z = ∏ j, tgFac a (z.2 j - x0 j) := torusGauss_eq_prod a x0 z
  have hPpos : (0:ℝ) < ∏ j, tgFac a (z.2 j - x0 j) :=
    Finset.prod_pos fun j _ => tgFac_pos a _
  have hane : a ≠ 0 := ne_of_gt ha
  rw [dvec_torusGauss, hP]
  have hkey : (-(1 / (4 * a)) * tgProfile1 (z.2 i - x0 i) * ∏ j, tgFac a (z.2 j - x0 j)) ^ 2
        / ∏ j, tgFac a (z.2 j - x0 j)
      = 1 / (16 * a ^ 2) * tgProfile1 (z.2 i - x0 i) ^ 2 * ∏ j, tgFac a (z.2 j - x0 j) := by
    field_simp
    ring
  rw [hkey]
  fin_cases i <;> simp [Fin.prod_univ_three, tgLapB] <;> ring

/-! ## The constant -/

/-- The Fisher-information constant `C_FI = (3π⁵/2)·√(2π³)`. -/
def tgFisherC : ℝ := 3 * π ^ 5 / 2 * Real.sqrt (2 * π ^ 3)

lemma tgFisherC_nonneg : 0 ≤ tgFisherC := by
  have : (0:ℝ) ≤ 3 * π ^ 5 / 2 := by positivity
  exact mul_nonneg this (Real.sqrt_nonneg _)

private lemma fisher_const_eval {a : ℝ} (ha : 0 < a) :
    3 * (π ^ 2 / (2 * a) * tgY2 a * tgY a ^ 2) = tgFisherC * Real.sqrt a := by
  have hY : tgY a ^ 2 = π ^ 3 * a := by
    rw [tgY, Real.sq_sqrt (by positivity)]
  have hY2 : tgY2 a = Real.sqrt (2 * π ^ 3) * Real.sqrt a := by
    rw [tgY2, ← Real.sqrt_mul (by positivity)]
  rw [hY, hY2, tgFisherC]
  field_simp

/-! ## `C53` -/

/-- **`C53`.  The torus Gaussian Fisher-information bound.**

  `∫_cell |∇Φ_a|²/Φ_a ≤ C_FI·√a`   for every `a > 0`.

The estimate is proved by integrating the weighted quantity exactly: each
coordinate contribution factorises as `tgLapB ⊗ tgFac ⊗ tgFac`, whose
one-dimensional budgets are `O(a^{-1/2})` and `O(a^{1/2})` respectively, so the
product is `O(a^{1/2})`.  Bounding `|∇Φ_a|²/Φ_a` by its supremum would instead
have produced `O(a^{-1})`. -/
theorem torusGaussFisherInformationBound {a : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ) :
    cellInt (fun x => torusGaussFisher a x0 (t, x)) ≤ tgFisherC * Real.sqrt a := by
  set g : Fin 3 → E3 → ℝ := fun i x =>
    ∏ j, (if j = i then tgLapB a (x j - x0 j) else tgFac a (x j - x0 j)) with hg
  have hgcont : ∀ i, Continuous (g i) := fun i =>
    continuous_cellProd (f := fun j u => if j = i then tgLapB a u else tgFac a u)
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using continuous_tgLapB a
        · simpa [hj] using continuous_tgFac a) x0
  have hgle : ∀ i, cellInt (g i) ≤ π ^ 2 / (2 * a) * tgY2 a * tgY a ^ 2 := by
    intro i
    have h := cellInt_prod_le (f := fun j u => if j = i then tgLapB a u else tgFac a u)
      (C := fun j => if j = i then π ^ 2 / (2 * a) * tgY2 a else tgY a) x0
      (fun j u => by
        dsimp only
        split <;> [exact tgLapB_nonneg ha u; exact tgFac_nonneg a u])
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using tgLapB_periodic a
        · simpa [hj] using tgFac_periodic a)
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using integral_tgLapB_le ha
        · simpa [hj] using integral_tgFac_le ha)
    refine h.trans (le_of_eq ?_)
    fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
  have hcong : cellInt (fun x : E3 => torusGaussFisher a x0 (t, x))
      = cellInt (fun x : E3 => ∑ i, g i x) := by
    refine cellInt_congr fun x => ?_
    exact Finset.sum_congr rfl fun i _ => sq_dvec_div_torusGauss_eq_prod ha x0 i (t, x)
  have hsum : cellInt (fun x : E3 => ∑ i, g i x)
      = cellInt (g 0) + cellInt (g 1) + cellInt (g 2) := by
    have h3 : ∀ x : E3, (∑ i, g i x) = g 0 x + g 1 x + g 2 x := fun x => by
      simp [Fin.sum_univ_three]
    rw [cellInt_congr h3,
      cellInt_add (f := fun x => g 0 x + g 1 x) (g := g 2) ((hgcont 0).add (hgcont 1))
        (hgcont 2),
      cellInt_add (f := g 0) (g := g 1) (hgcont 0) (hgcont 1)]
  rw [hcong, hsum, ← fisher_const_eval ha]
  have := add_le_add (add_le_add (hgle 0) (hgle 1)) (hgle 2)
  linarith

end ClayNS
