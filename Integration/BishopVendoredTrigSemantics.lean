import Integration.BishopVendoredExponentialSemantics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Classical semantics of DASHI's concrete Bishop sine/cosine series

The mirrored source terms are exactly those in
BalabanBishopConcreteSineCosineTermParityExact:

  (-1)^n * (1/(2n+1)!) * x^(2n+1)
  (-1)^n * (1/(2n)!)   * x^(2n)

The repository already supplies term identification/convergence machinery on
the Bishop carrier.  This module proves that any such Bishop limits evaluate
to Lean's Real.sin / Real.cos.
-/

namespace Integration.BishopVendoredTrigSemantics

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredExponentialSemantics

noncomputable section

def oddExponent (n : ℕ) : ℕ := 2 * n + 1
def evenExponent (n : ℕ) : ℕ := 2 * n

def alternatingSign
    (A : VendoredArithmeticMirror) (n : ℕ) : RegularRatReal :=
  sourcePow A (A.neg A.one) n

theorem eval_alternatingSign
    (A : VendoredArithmeticMirror) (n : ℕ) :
    eval (alternatingSign A n) = (-1 : ℝ) ^ n := by
  rw [alternatingSign, eval_sourcePow, A.eval_neg, A.eval_one]
  norm_num

def sineTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (n : ℕ) : RegularRatReal :=
  A.mul
    (alternatingSign A n)
    (A.mul
      (rational (1 / ((oddExponent n).factorial : ℚ)))
      (sourcePow A x (oddExponent n)))

def cosineTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (n : ℕ) : RegularRatReal :=
  A.mul
    (alternatingSign A n)
    (A.mul
      (rational (1 / ((evenExponent n).factorial : ℚ)))
      (sourcePow A x (evenExponent n)))

theorem eval_sineTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (sineTerm A x n) =
      (-1 : ℝ) ^ n *
        eval x ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ) := by
  rw [sineTerm, A.eval_mul, eval_alternatingSign,
      A.eval_mul, eval_rational, eval_sourcePow]
  simp [oddExponent, div_eq_mul_inv]
  ring

theorem eval_cosineTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (cosineTerm A x n) =
      (-1 : ℝ) ^ n *
        eval x ^ (2 * n) /
        ((2 * n).factorial : ℝ) := by
  rw [cosineTerm, A.eval_mul, eval_alternatingSign,
      A.eval_mul, eval_rational, eval_sourcePow]
  simp [evenExponent, div_eq_mul_inv]
  ring

def sinePartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.zero
  | n + 1 =>
      A.add (sinePartialSum A x n) (sineTerm A x n)

def cosinePartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.zero
  | n + 1 =>
      A.add (cosinePartialSum A x n) (cosineTerm A x n)

theorem eval_sinePartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (N : ℕ) :
    eval (sinePartialSum A x N) =
      ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n *
          eval x ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℝ) := by
  induction N with
  | zero =>
      simp [sinePartialSum, A.eval_zero]
  | succ N ih =>
      rw [sinePartialSum, A.eval_add, ih, eval_sineTerm]
      simp [Finset.sum_range_succ]

theorem eval_cosinePartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (N : ℕ) :
    eval (cosinePartialSum A x N) =
      ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n *
          eval x ^ (2 * n) /
          ((2 * n).factorial : ℝ) := by
  induction N with
  | zero =>
      simp [cosinePartialSum, A.eval_zero]
  | succ N ih =>
      rw [cosinePartialSum, A.eval_add, ih, eval_cosineTerm]
      simp [Finset.sum_range_succ]

structure VendoredTrigLimitMirror
    (A : VendoredArithmeticMirror) where
  sinB cosB : RegularRatReal → RegularRatReal

  sinConverges :
    ∀ x,
      BishopConvergesTo A
        (sinePartialSum A x)
        (sinB x)

  cosConverges :
    ∀ x,
      BishopConvergesTo A
        (cosinePartialSum A x)
        (cosB x)

open VendoredTrigLimitMirror public

private theorem lean_sine_partialSums_tendsto
    (x : ℝ) :
    Tendsto
      (fun N =>
        ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ n *
            x ^ (2 * n + 1) /
            ((2 * n + 1).factorial : ℝ))
      atTop
      (𝓝 (Real.sin x)) :=
  (Real.hasSum_sin x).tendsto_sum_nat

private theorem lean_cosine_partialSums_tendsto
    (x : ℝ) :
    Tendsto
      (fun N =>
        ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ n *
            x ^ (2 * n) /
            ((2 * n).factorial : ℝ))
      atTop
      (𝓝 (Real.cos x)) :=
  (Real.hasSum_cos x).tendsto_sum_nat

theorem eval_sin_eq_real_sin
    (A : VendoredArithmeticMirror)
    (T : VendoredTrigLimitMirror A)
    (x : RegularRatReal) :
    eval (T.sinB x) = Real.sin (eval x) := by
  have hsource :
      Tendsto
        (fun N => eval (sinePartialSum A x N))
        atTop
        (𝓝 (eval (T.sinB x))) :=
    eval_tendsto_of_bishopConvergesTo A (T.sinConverges x)
  have hclassical :
      Tendsto
        (fun N => eval (sinePartialSum A x N))
        atTop
        (𝓝 (Real.sin (eval x))) := by
    simpa only [eval_sinePartialSum] using
      lean_sine_partialSums_tendsto (eval x)
  exact tendsto_nhds_unique hsource hclassical

theorem eval_cos_eq_real_cos
    (A : VendoredArithmeticMirror)
    (T : VendoredTrigLimitMirror A)
    (x : RegularRatReal) :
    eval (T.cosB x) = Real.cos (eval x) := by
  have hsource :
      Tendsto
        (fun N => eval (cosinePartialSum A x N))
        atTop
        (𝓝 (eval (T.cosB x))) :=
    eval_tendsto_of_bishopConvergesTo A (T.cosConverges x)
  have hclassical :
      Tendsto
        (fun N => eval (cosinePartialSum A x N))
        atTop
        (𝓝 (Real.cos (eval x))) := by
    simpa only [eval_cosinePartialSum] using
      lean_cosine_partialSums_tendsto (eval x)
  exact tendsto_nhds_unique hsource hclassical

structure VendorTrigSemanticsBoundary where
  literalSignedFactorialTermsMirrored : Bool
  sourcePartialSumsMirrored : Bool
  bishopConvergenceTransportReused : Bool
  classicalSinSeriesReused : Bool
  classicalCosSeriesReused : Bool
  bishopSinSemanticIdentificationCompiled : Bool
  bishopCosSemanticIdentificationCompiled : Bool
  actualAgdaTrigConvergenceMirrorInhabited : Bool

def vendorTrigSemanticsBoundary : VendorTrigSemanticsBoundary where
  literalSignedFactorialTermsMirrored := true
  sourcePartialSumsMirrored := true
  bishopConvergenceTransportReused := true
  classicalSinSeriesReused := true
  classicalCosSeriesReused := true
  bishopSinSemanticIdentificationCompiled := true
  bishopCosSemanticIdentificationCompiled := true
  actualAgdaTrigConvergenceMirrorInhabited := false

end

end Integration.BishopVendoredTrigSemantics
