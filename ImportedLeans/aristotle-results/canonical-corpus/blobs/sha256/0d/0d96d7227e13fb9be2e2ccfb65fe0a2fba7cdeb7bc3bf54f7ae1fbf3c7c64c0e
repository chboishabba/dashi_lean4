/-
# The resolvent form of a finite family, and its heat factorization

This file develops, from scratch and with no extra hypotheses, the exact
algebra behind the "resolvent-weighted Gram flux" route:

for a finite family of vectors `A α` carrying strictly positive damping rates
`lam α`, the *resolvent form*

  `resForm A B = ∑_{α,β} ⟪A α, B β⟫ / (lam α + lam β)`

is the integral over `s ∈ (0,∞)` of the pairing of the heat-weighted
superpositions

  `A_s = ∑_α e^{-s·lam α} A α`,   `B_s = ∑_β e^{-s·lam β} B β`,

because the Cauchy kernel `1/(a+b)` has the positive representation
`∫_0^∞ e^{-sa} e^{-sb} ds`.

Three consequences are proved:

* `PSDForm.resForm_nonneg` — the resolvent form is positive semidefinite.  In
  particular the coherent (off-diagonal) part of a resolvent-weighted Gram sum
  is bounded below by minus its diagonal part (`neg_resOff_le_resDiag`), so no
  absolute bound on the off-diagonal endpoint is needed.
* `PSDForm.resForm_young` — the resolvent-weighted *mixed* sum is absorbed into
  the *same* positive resolvent form of `A` plus the resolvent form of the
  remainder family: `4|resForm A F| ≤ ε·resForm A A + (4/ε)·resForm F F` for
  every `ε > 0`.
* `PSDForm.resDiag_le` — the diagonal endpoint carries no convolution
  multiplicity: a uniform ceiling on the resolvent weights pays it against the
  plain sum of cell masses.

Everything is stated for an arbitrary symmetric positive-semidefinite real
bilinear form `PSDForm V`, so that it applies verbatim to the complex
`Fin 3 → ℂ` cells of the Waleffe/Galerkin carrier through the real part of the
Hermitian pairing (see `ResolventGramFlux.lean`).
-/
import Mathlib

noncomputable section

open MeasureTheory Set Real Finset

namespace ClayNS.Resolvent

/-- A symmetric positive-semidefinite real bilinear form on a real vector
space.  Definiteness is deliberately *not* assumed: the concrete NS carriers
use the real part of a Hermitian pairing on complex vectors. -/
structure PSDForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The underlying pairing. -/
  form : V → V → ℝ
  /-- Symmetry. -/
  symm : ∀ x y, form x y = form y x
  /-- Additivity in the first slot. -/
  add_left : ∀ x y z, form (x + y) z = form x z + form y z
  /-- Real homogeneity in the first slot. -/
  smul_left : ∀ (c : ℝ) (x y : V), form (c • x) y = c * form x y
  /-- Positive semidefiniteness. -/
  nonneg : ∀ x, 0 ≤ form x x

theorem integral_exp_neg_mul (b : ℝ) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(s * b)) = 1 / b := by
  have h := integral_comp_mul_right_Ioi (fun x => Real.exp (-x)) 0 hb
  simp only [zero_mul, smul_eq_mul] at h
  rw [h, integral_exp_neg_Ioi_zero, one_div, mul_one]

theorem integrableOn_exp_neg_mul (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => Real.exp (-(s * b))) (Ioi 0) volume := by
  have := exp_neg_integrableOn_Ioi (0 : ℝ) hb
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [neg_mul, mul_comm]

namespace PSDForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (P : PSDForm V)

theorem add_right (x y z : V) : P.form x (y + z) = P.form x y + P.form x z := by
  rw [P.symm, P.add_left, P.symm y x, P.symm z x]

theorem smul_right (c : ℝ) (x y : V) : P.form x (c • y) = c * P.form x y := by
  rw [P.symm, P.smul_left, P.symm y x]

theorem zero_left (y : V) : P.form 0 y = 0 := by
  have := P.smul_left 0 0 y
  simpa using this

theorem zero_right (x : V) : P.form x 0 = 0 := by
  rw [P.symm, P.zero_left]

theorem sum_left {ι : Type*} (s : Finset ι) (x : ι → V) (y : V) :
    P.form (∑ i ∈ s, x i) y = ∑ i ∈ s, P.form (x i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [P.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, P.add_left, ih, Finset.sum_insert ha]

theorem sum_right {ι : Type*} (s : Finset ι) (x : V) (y : ι → V) :
    P.form x (∑ i ∈ s, y i) = ∑ i ∈ s, P.form x (y i) := by
  rw [P.symm, P.sum_left]
  exact Finset.sum_congr rfl fun i _ => P.symm _ _

/-! ## Cauchy–Schwarz and Young for a positive semidefinite form -/

/-- Cauchy–Schwarz for a symmetric positive semidefinite bilinear form. -/
theorem sq_form_le (x y : V) : P.form x y ^ 2 ≤ P.form x x * P.form y y := by
  have key : ∀ t : ℝ, 0 ≤ P.form y y * t ^ 2 + 2 * P.form x y * t + P.form x x := by
    intro t
    have h := P.nonneg (x + t • y)
    have hx : P.form (x + t • y) (x + t • y)
        = P.form x x + t * P.form x y + (t * P.form y x + t * (t * P.form y y)) := by
      rw [P.add_left, P.add_right, P.add_right, P.smul_left, P.smul_right, P.smul_left,
        P.smul_right]
    rw [hx, P.symm y x] at h
    nlinarith [h]
  have hdisc : discrim (P.form y y) (2 * P.form x y) (P.form x x) ≤ 0 :=
    discrim_le_zero (fun t => by nlinarith [key t])
  have : (2 * P.form x y) ^ 2 - 4 * (P.form y y) * (P.form x x) ≤ 0 := by
    simpa [discrim] using hdisc
  nlinarith [this]

/-- Young's inequality in the shape used by the absorption step:
`4|⟪x,y⟫| ≤ ε‖x‖² + (4/ε)‖y‖²`. -/
theorem young_abs_le {ε : ℝ} (hε : 0 < ε) (x y : V) :
    4 * |P.form x y| ≤ ε * P.form x x + (4 / ε) * P.form y y := by
  have hcs := P.sq_form_le x y
  have hx := P.nonneg x
  have hy := P.nonneg y
  set g := P.form x x
  set h := P.form y y
  set m := P.form x y
  have hS : 0 ≤ ε * g + (4 / ε) * h := by positivity
  have hsq : (4 * |m|) ^ 2 ≤ (ε * g + (4 / ε) * h) ^ 2 := by
    have hm : |m| ^ 2 = m ^ 2 := sq_abs m
    have hexp : (ε * g + (4 / ε) * h) ^ 2 - 16 * (g * h)
        = (ε * g - (4 / ε) * h) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (ε * g - (4 / ε) * h)]
  have h4 : 0 ≤ 4 * |m| := by positivity
  nlinarith [hsq, hS, h4]

/-! ## Heat superpositions and the resolvent form -/

variable {ι : Type*} [Fintype ι]

/-- The heat-weighted superposition `A_s = ∑_α e^{-s·lam α} A α`. -/
def heatCombo (lam : ι → ℝ) (A : ι → V) (s : ℝ) : V :=
  ∑ i, Real.exp (-(s * lam i)) • A i

/-- The resolvent form `∑_{α,β} ⟪A α, B β⟫/(lam α + lam β)`. -/
def resForm (lam : ι → ℝ) (A B : ι → V) : ℝ :=
  ∑ i, ∑ j, P.form (A i) (B j) / (lam i + lam j)

/-- The resolvent form is symmetric.  Pure algebra: no positivity used. -/
theorem resForm_comm (lam : ι → ℝ) (A B : ι → V) :
    P.resForm lam A B = P.resForm lam B A := by
  rw [resForm, resForm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [P.symm, add_comm (lam j) (lam i)]

theorem heat_pairing_expand (lam : ι → ℝ) (A B : ι → V) (s : ℝ) :
    P.form (heatCombo lam A s) (heatCombo lam B s)
      = ∑ i, ∑ j, Real.exp (-(s * (lam i + lam j))) * P.form (A i) (B j) := by
  rw [heatCombo, heatCombo, P.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [P.smul_left, P.sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.smul_right, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- **The resolvent form is the heat integral of the pairing.**  This is the
Cauchy-kernel factorization `1/(λ_α+λ_β) = ∫_0^∞ e^{-sλ_α}e^{-sλ_β} ds` applied
to a whole finite family. -/
theorem resForm_eq_integral (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (A B : ι → V) :
    P.resForm lam A B
      = ∫ s in Ioi (0 : ℝ), P.form (heatCombo lam A s) (heatCombo lam B s) := by
  have hint : (∫ s in Ioi (0 : ℝ), P.form (heatCombo lam A s) (heatCombo lam B s))
      = ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j,
          Real.exp (-(s * (lam i + lam j))) * P.form (A i) (B j) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    exact P.heat_pairing_expand lam A B s
  rw [hint]
  have hterm : ∀ i j : ι,
      IntegrableOn (fun s : ℝ => Real.exp (-(s * (lam i + lam j))) * P.form (A i) (B j))
        (Ioi 0) volume := by
    intro i j
    exact (integrableOn_exp_neg_mul _ (by have := hlam i; have := hlam j; linarith)).mul_const _
  rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
    MeasureTheory.integrable_finset_sum _ (fun j _ => hterm i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finset_sum _ (fun j _ => hterm i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_mul_const,
    integral_exp_neg_mul _ (by have := hlam i; have := hlam j; linarith)]
  rw [div_eq_mul_inv, one_div, mul_comm]

/-- **Positivity of the resolvent form.** -/
theorem resForm_nonneg (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (A : ι → V) :
    0 ≤ P.resForm lam A A := by
  rw [P.resForm_eq_integral lam hlam]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun s _ => P.nonneg _

/-! ## The resolvent form is itself a positive semidefinite form -/

/-- The resolvent form, viewed as a symmetric positive semidefinite bilinear
form on families of cells. -/
def resPSD (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) : PSDForm (ι → V) where
  form A B := P.resForm lam A B
  symm A B := P.resForm_comm lam A B
  add_left A B C := by
    rw [resForm, resForm, resForm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.add_apply, P.add_left, add_div]
  smul_left c A B := by
    rw [resForm, resForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, P.smul_left, mul_div_assoc]
  nonneg A := P.resForm_nonneg lam hlam A

/-- **Cauchy–Schwarz for the resolvent form.** -/
theorem sq_resForm_le (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (A F : ι → V) :
    P.resForm lam A F ^ 2 ≤ P.resForm lam A A * P.resForm lam F F :=
  (P.resPSD lam hlam).sq_form_le A F

/-- **The absorption step (R299/R300).**  The resolvent-weighted mixed sum is
absorbed into an arbitrarily small multiple of the *same* positive resolvent
form of the cells, at the price of the resolvent form of the remainder. -/
theorem resForm_young (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) {ε : ℝ} (hε : 0 < ε)
    (A F : ι → V) :
    4 * |P.resForm lam A F| ≤ ε * P.resForm lam A A + (4 / ε) * P.resForm lam F F :=
  (P.resPSD lam hlam).young_abs_le hε A F

/-! ## An explicit reduction of the remainder leaf -/

/-- The seminorm attached to the form. -/
def nrmP (x : V) : ℝ := Real.sqrt (P.form x x)

theorem nrmP_nonneg (x : V) : 0 ≤ P.nrmP x := Real.sqrt_nonneg _

theorem abs_form_le (x y : V) : |P.form x y| ≤ P.nrmP x * P.nrmP y := by
  have hcs := P.sq_form_le x y
  have hx := P.nonneg x
  have hy := P.nonneg y
  have hsq : (P.nrmP x * P.nrmP y) ^ 2 = P.form x x * P.form y y := by
    rw [nrmP, nrmP, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hnn : 0 ≤ P.nrmP x * P.nrmP y := mul_nonneg (P.nrmP_nonneg x) (P.nrmP_nonneg y)
  nlinarith [sq_abs (P.form x y), abs_nonneg (P.form x y)]

/-- The remainder leaf is dominated by the *scalar* resolvent sum of the cell
seminorms.  This is the honest cost of discarding the signs inside the
remainder family. -/
theorem resForm_le_nrm_resolvent (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (F : ι → V) :
    P.resForm lam F F ≤ ∑ i, ∑ j, P.nrmP (F i) * P.nrmP (F j) / (lam i + lam j) := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hpos : 0 < lam i + lam j := by have := hlam i; have := hlam j; linarith
  have hle : P.form (F i) (F j) ≤ P.nrmP (F i) * P.nrmP (F j) :=
    le_trans (le_abs_self _) (P.abs_form_le (F i) (F j))
  gcongr

/-- With a uniform floor on the damping rates, the remainder leaf is bounded by
the square of the summed cell seminorms, with the explicit constant `1/(2λ₀)`. -/
theorem resForm_le_of_rate_floor {lam0 : ℝ} (lam : ι → ℝ) (hlam0 : 0 < lam0)
    (hfloor : ∀ i, lam0 ≤ lam i) (F : ι → V) :
    P.resForm lam F F ≤ (1 / (2 * lam0)) * (∑ i, P.nrmP (F i)) ^ 2 := by
  have hstep : ∀ i j : ι, P.form (F i) (F j) / (lam i + lam j)
      ≤ (1 / (2 * lam0)) * (P.nrmP (F i) * P.nrmP (F j)) := by
    intro i j
    have hpos : 0 < 2 * lam0 := by linarith
    have h2 : 2 * lam0 ≤ lam i + lam j := by
      have := hfloor i; have := hfloor j; linarith
    have hle : P.form (F i) (F j) ≤ P.nrmP (F i) * P.nrmP (F j) :=
      le_trans (le_abs_self _) (P.abs_form_le (F i) (F j))
    have hnn : 0 ≤ P.nrmP (F i) * P.nrmP (F j) :=
      mul_nonneg (P.nrmP_nonneg _) (P.nrmP_nonneg _)
    calc P.form (F i) (F j) / (lam i + lam j)
        ≤ (P.nrmP (F i) * P.nrmP (F j)) / (2 * lam0) := by gcongr
      _ = (1 / (2 * lam0)) * (P.nrmP (F i) * P.nrmP (F j)) := by ring
  have hsum : P.resForm lam F F
      ≤ ∑ i, ∑ j, (1 / (2 * lam0)) * (P.nrmP (F i) * P.nrmP (F j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
  have hexp : ∑ i, ∑ j, (1 / (2 * lam0)) * (P.nrmP (F i) * P.nrmP (F j))
      = (1 / (2 * lam0)) * (∑ i, P.nrmP (F i)) ^ 2 := by
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  exact le_trans hsum (le_of_eq hexp)

/-! ## Diagonal and off-diagonal endpoint -/

/-- The diagonal part of the resolvent form. -/
def resDiag (lam : ι → ℝ) (A : ι → V) : ℝ := ∑ i, P.form (A i) (A i) / (lam i + lam i)

/-- The off-diagonal (coherent) part of the resolvent form. -/
def resOff [DecidableEq ι] (lam : ι → ℝ) (A : ι → V) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, P.form (A i) (A j) / (lam i + lam j)

theorem resForm_eq_diag_add_off [DecidableEq ι] (lam : ι → ℝ) (A : ι → V) :
    P.resForm lam A A = P.resDiag lam A + P.resOff lam A := by
  rw [resForm, resDiag, resOff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- **R297, unconditionally.**  Because the full resolvent form is positive, the
coherent endpoint never falls below minus the diagonal endpoint; no absolute
bound on the off-diagonal part is required. -/
theorem neg_resOff_le_resDiag [DecidableEq ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (A : ι → V) : -P.resOff lam A ≤ P.resDiag lam A := by
  have h := P.resForm_nonneg lam hlam A
  rw [P.resForm_eq_diag_add_off lam A] at h
  linarith

/-- **R298, the weight ceiling.**  A uniform ceiling on nonnegative weights pays
a weighted sum of nonnegative masses against the plain sum: no multiplicity of
the index set appears. -/
theorem sum_weighted_le_ceiling {W : ℝ} (w m : ι → ℝ)
    (hW : ∀ i, w i ≤ W) (hm : ∀ i, 0 ≤ m i) :
    ∑ i, w i * m i ≤ W * ∑ i, m i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hW i) (hm i)

/-- The diagonal endpoint is paid by a uniform ceiling on the resolvent weights
against the plain sum of cell masses. -/
theorem resDiag_le {W : ℝ} (lam : ι → ℝ) (A : ι → V)
    (hW : ∀ i, 1 / (lam i + lam i) ≤ W) :
    P.resDiag lam A ≤ W * ∑ i, P.form (A i) (A i) := by
  have hrw : P.resDiag lam A
      = ∑ i, (1 / (lam i + lam i)) * P.form (A i) (A i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div, div_eq_inv_mul]
  rw [hrw]
  exact sum_weighted_le_ceiling _ _ hW (fun i => P.nonneg _)

end PSDForm

end ClayNS.Resolvent
