import Integration.BishopVendoredOrderConvergenceEvaluation
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Classical semantics of DASHI's vendored Bishop exponential

DASHI already constructs its concrete Bishop exponential as the limit of

  x^n / n!

and proves that those Bishop partial sums converge to bishopExp x.

This module does not assume that bishopExp is classical exp.  It mirrors the
actual source term/partial-sum family, transports the source convergence theorem
through the vendored Bishop evaluator, and identifies the resulting Lean limit
with Real.exp by uniqueness of limits and Mathlib's exponential-series theorem.
-/

namespace Integration.BishopVendoredExponentialSemantics

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation

noncomputable section

def sourcePow (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.one
  | n + 1 => A.mul (sourcePow A x n) x

theorem eval_sourcePow
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (sourcePow A x n) = eval x ^ n := by
  induction n with
  | zero =>
      simp [sourcePow, A.eval_one]
  | succ n ih =>
      rw [sourcePow, A.eval_mul, ih, pow_succ]

def inverseFactorialRat (n : ℕ) : ℚ :=
  1 / (n.factorial : ℚ)

def expTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (n : ℕ) : RegularRatReal :=
  A.mul
    (sourcePow A x n)
    (rational (inverseFactorialRat n))

theorem eval_expTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (expTerm A x n) =
      eval x ^ n / (n.factorial : ℝ) := by
  rw [expTerm, A.eval_mul, eval_sourcePow, eval_rational]
  simp [inverseFactorialRat, div_eq_mul_inv]

def expPartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.zero
  | n + 1 =>
      A.add (expPartialSum A x n) (expTerm A x n)

theorem eval_expPartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (N : ℕ) :
    eval (expPartialSum A x N) =
      ∑ n ∈ Finset.range N,
        eval x ^ n / (n.factorial : ℝ) := by
  induction N with
  | zero =>
      simp [expPartialSum, A.eval_zero]
  | succ N ih =>
      rw [expPartialSum, A.eval_add, ih, eval_expTerm]
      simp [Finset.sum_range_succ]

/-- Source-facing mirror of the theorem already proved in
BishopExponentialSeriesConvergenceExact.bishopExpConverges. -/
structure VendoredExpLimitMirror
    (A : VendoredArithmeticMirror) where
  expB : RegularRatReal → RegularRatReal
  converges :
    ∀ x,
      BishopConvergesTo A
        (expPartialSum A x)
        (expB x)

open VendoredExpLimitMirror public

private theorem lean_exp_partialSums_tendsto
    (x : ℝ) :
    Tendsto
      (fun N =>
        ∑ n ∈ Finset.range N,
          x ^ n / (n.factorial : ℝ))
      atTop
      (𝓝 (Real.exp x)) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ]
  exact hs.tendsto_sum_nat

/-- The concrete vendored/DASHI Bishop exponential evaluates to classical
Real.exp; this is derived from the actual source convergence theorem. -/
theorem eval_exp_eq_real_exp
    (A : VendoredArithmeticMirror)
    (E : VendoredExpLimitMirror A)
    (x : RegularRatReal) :
    eval (E.expB x) = Real.exp (eval x) := by
  have hsource :
      Tendsto
        (fun N => eval (expPartialSum A x N))
        atTop
        (𝓝 (eval (E.expB x))) :=
    eval_tendsto_of_bishopConvergesTo A (E.converges x)
  have hclassical :
      Tendsto
        (fun N => eval (expPartialSum A x N))
        atTop
        (𝓝 (Real.exp (eval x))) := by
    simpa only [eval_expPartialSum] using
      lean_exp_partialSums_tendsto (eval x)
  exact tendsto_nhds_unique hsource hclassical

structure VendorExponentialSemanticsBoundary where
  literalSourcePowerMirrored : Bool
  literalInverseFactorialTermsMirrored : Bool
  literalSourcePartialSumsMirrored : Bool
  bishopConvergenceTransportReused : Bool
  classicalExpSeriesReused : Bool
  bishopExpSemanticIdentificationCompiled : Bool
  actualAgdaExpConvergenceMirrorInhabited : Bool

def vendorExponentialSemanticsBoundary :
    VendorExponentialSemanticsBoundary where
  literalSourcePowerMirrored := true
  literalInverseFactorialTermsMirrored := true
  literalSourcePartialSumsMirrored := true
  bishopConvergenceTransportReused := true
  classicalExpSeriesReused := true
  bishopExpSemanticIdentificationCompiled := true
  actualAgdaExpConvergenceMirrorInhabited := false

end

end Integration.BishopVendoredExponentialSemantics
