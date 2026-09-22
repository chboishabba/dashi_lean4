import Integration.BishopVendoredRealEvaluation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Order and convergence transport for DASHI's vendored Bishop reals

This module mirrors the exact sign/order/absolute-value and convergence
definitions from the vendored Bishop Real.agda / Sequence.agda and proves that
the canonical evaluator into Lean Real preserves them.

Source definitions:
* NonNegative x: x_n >= -1/n for every nonzero n;
* x <= y: NonNegative (y - x);
* |x| is the pointwise rational absolute-value sequence;
* f -> x: for every nonzero k, eventually |f_n - x| <= (1/k)^*.

The result is a reusable theorem:

  Bishop convergence -> ordinary Lean Tendsto after eval.

This is the key bridge needed to identify the existing Bishop power-series
exp/sin/cos limits with the corresponding classical Lean functions.
-/

namespace Integration.BishopVendoredOrderConvergenceEvaluation

open Filter
open scoped Topology

open Integration.BishopVendoredRealEvaluation

noncomputable section

/-- Exact semantic mirror of Bishop NonNegative after the canonical ℚ -> ℝ cast. -/
def NonNegative (x : RegularRatReal) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    -(1 / (n : ℝ)) ≤ (x.seq n : ℝ)

/-- Pointwise absolute value, exactly matching vendored Real.∣_∣. -/
def absReal (x : RegularRatReal) : RegularRatReal where
  seq n := |x.seq n|
  regular m n hm hn := by
    have h :=
      abs_sub_abs_le_abs_sub (x.seq m : ℝ) (x.seq n : ℝ)
    have hreg := x.regular m n hm hn
    simpa only [Rat.cast_abs] using h.trans hreg

/-- Constant rational embedding, exactly matching vendored Real._⋆. -/
def rational (q : ℚ) : RegularRatReal where
  seq _ := q
  regular m n hm hn := by
    simp
    positivity

/-- Evaluation of a rational embedding is the ordinary rational cast. -/
theorem eval_rational (q : ℚ) :
    eval (rational q) = (q : ℝ) := by
  apply tendsto_nhds_unique (tendsto_eval (rational q))
  simpa [shifted, rational] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (q : ℝ)) atTop (𝓝 (q : ℝ)))

/-- Evaluation preserves the vendored pointwise absolute value. -/
theorem eval_abs (x : RegularRatReal) :
    eval (absReal x) = |eval x| := by
  apply tendsto_nhds_unique (tendsto_eval (absReal x))
  simpa [shifted, absReal, Rat.cast_abs] using
    (tendsto_eval x).abs

private theorem neg_one_div_succ_tendsto_zero :
    Tendsto (fun n : ℕ => -(1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
  simpa using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1) |>.neg

/-- Vendored constructive nonnegativity is sound for the evaluated real. -/
theorem eval_nonnegative
    {x : RegularRatReal}
    (hx : NonNegative x) :
    0 ≤ eval x := by
  apply le_of_tendsto_of_tendsto'
    neg_one_div_succ_tendsto_zero
    (tendsto_eval x)
  intro n
  simpa [shifted] using hx (n + 1) (by omega)

/-- Source subtraction expressed using the exact vendored add/neg operations. -/
def sub (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) : RegularRatReal :=
  A.add x (A.neg y)

/-- Evaluation preserves source subtraction. -/
theorem eval_sub
    (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) :
    eval (sub A x y) = eval x - eval y := by
  simp [sub, A.eval_add, A.eval_neg]
  ring

/-- Exact Bishop order mirror: x <= y iff y-x is NonNegative. -/
def Le (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) : Prop :=
  NonNegative (sub A y x)

/-- Bishop order is sound under evaluation. -/
theorem eval_le
    (A : VendoredArithmeticMirror)
    {x y : RegularRatReal}
    (hxy : Le A x y) :
    eval x ≤ eval y := by
  have hnn : 0 ≤ eval (sub A y x) :=
    eval_nonnegative hxy
  rw [eval_sub] at hnn
  linarith

/-- Exact Bishop absolute-difference expression. -/
def absDiff
    (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) : RegularRatReal :=
  absReal (sub A x y)

/-- Evaluation of the Bishop absolute difference is ordinary real distance. -/
theorem eval_absDiff
    (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) :
    eval (absDiff A x y) = dist (eval x) (eval y) := by
  rw [absDiff, eval_abs, eval_sub, Real.dist_eq]

/-- Quantitative mirror of Sequence._ConvergesTo_.

The source constructor stores N_k - 1 and requires the estimate from
suc(N_k - 1) onward; we retain that exact indexing here.
-/
def BishopConvergesTo
    (A : VendoredArithmeticMirror)
    (f : ℕ → RegularRatReal)
    (x : RegularRatReal) : Prop :=
  ∀ k : ℕ, k ≠ 0 →
    ∃ NkPred : ℕ,
      ∀ n : ℕ, NkPred + 1 ≤ n →
        Le A
          (absDiff A (f n) x)
          (rational (1 / (k : ℚ)))

/-- The exact Bishop 1/k convergence modulus transports to ordinary Lean
metric convergence under eval. -/
theorem eval_tendsto_of_bishopConvergesTo
    (A : VendoredArithmeticMirror)
    {f : ℕ → RegularRatReal}
    {x : RegularRatReal}
    (hconv : BishopConvergesTo A f x) :
    Tendsto (fun n => eval (f n)) atTop (𝓝 (eval x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  let k : ℕ := m + 1
  have hk : k ≠ 0 := by
    dsimp [k]
    omega
  obtain ⟨Npred, hN⟩ := hconv k hk
  refine ⟨Npred + 1, ?_⟩
  intro n hn
  have hsource :=
    eval_le A (hN n hn)
  rw [eval_absDiff, eval_rational] at hsource
  have hkcast :
      ((1 / (k : ℚ) : ℚ) : ℝ) = 1 / (k : ℝ) := by
    norm_num
  rw [hkcast] at hsource
  have hsmall : 1 / (k : ℝ) < ε := by
    simpa [k] using hm
  exact lt_of_le_of_lt hsource hsmall

/-- Machine-readable status for the convergence bridge. -/
structure VendorConvergenceBoundary where
  bishopNonnegativeMirrored : Bool
  bishopOrderMirrored : Bool
  bishopAbsoluteValueMirrored : Bool
  rationalEmbeddingEvaluatesCorrectly : Bool
  evaluatorOrderSound : Bool
  evaluatorAbsPreserving : Bool
  bishopQuantitativeConvergenceMirrored : Bool
  bishopConvergenceImpliesLeanTendsto : Bool

def vendorConvergenceBoundary : VendorConvergenceBoundary where
  bishopNonnegativeMirrored := true
  bishopOrderMirrored := true
  bishopAbsoluteValueMirrored := true
  rationalEmbeddingEvaluatesCorrectly := true
  evaluatorOrderSound := true
  evaluatorAbsPreserving := true
  bishopQuantitativeConvergenceMirrored := true
  bishopConvergenceImpliesLeanTendsto := true

end

end Integration.BishopVendoredOrderConvergenceEvaluation
