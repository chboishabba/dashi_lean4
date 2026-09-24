import Integration.BishopVendoredTrigSemantics
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Classical semantics of DASHI's constructed Bishop Machin pi

The Agda source constructs

  bishopMachinPi
    = 16 * atan_B(1/5) - 4 * atan_B(1/239)

where each atan_B is the Bishop limit of the literal alternating power series

  sum_n (-1)^n x^(2n+1)/(2n+1).

This module mirrors exactly that construction.  It first proves that evaluation
of any such Bishop atan limit agrees with Real.arctan for |x| < 1, then uses
Mathlib's formal John Machin identity

  4 * arctan (1/5) - arctan (1/239) = pi/4

to conclude that the exact constructed Bishop Machin real evaluates to
Real.pi.

No trigonometric-addition or branch axiom is imported from the Agda side.
-/

namespace Integration.BishopVendoredMachinPiSemantics

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredExponentialSemantics
open Integration.BishopVendoredTrigSemantics

noncomputable section

def oddExponent (n : ℕ) : ℕ := 2 * n + 1

def atanTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (n : ℕ) : RegularRatReal :=
  A.mul
    (alternatingSign A n)
    (A.mul
      (rational (1 / ((oddExponent n : ℕ) : ℚ)))
      (sourcePow A x (oddExponent n)))

theorem eval_atanTerm
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (atanTerm A x n) =
      (-1 : ℝ) ^ n *
        eval x ^ (2 * n + 1) /
        ((2 * n + 1 : ℕ) : ℝ) := by
  rw [atanTerm, A.eval_mul, eval_alternatingSign,
      A.eval_mul, eval_rational, eval_sourcePow]
  simp [oddExponent, div_eq_mul_inv]
  ring

def atanPartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.zero
  | n + 1 =>
      A.add (atanPartialSum A x n) (atanTerm A x n)

theorem eval_atanPartialSum
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (N : ℕ) :
    eval (atanPartialSum A x N) =
      ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n *
          eval x ^ (2 * n + 1) /
          ((2 * n + 1 : ℕ) : ℝ) := by
  induction N with
  | zero =>
      simp [atanPartialSum, A.eval_zero]
  | succ N ih =>
      rw [atanPartialSum, A.eval_add, ih, eval_atanTerm]
      simp [Finset.sum_range_succ]

/-- Any Bishop limit of the exact arctangent series evaluates to classical
Real.arctan, provided the evaluated point lies in the classical radius. -/
theorem eval_atan_eq_real_arctan
    (A : VendoredArithmeticMirror)
    (x atanB : RegularRatReal)
    (hconv :
      BishopConvergesTo A
        (atanPartialSum A x)
        atanB)
    (hx : |eval x| < 1) :
    eval atanB = Real.arctan (eval x) := by
  have hsource :
      Tendsto
        (fun N => eval (atanPartialSum A x N))
        atTop
        (𝓝 (eval atanB)) :=
    eval_tendsto_of_bishopConvergesTo A hconv

  have hseries :
      Tendsto
        (fun N =>
          ∑ n ∈ Finset.range N,
            (-1 : ℝ) ^ n *
              eval x ^ (2 * n + 1) /
              ((2 * n + 1 : ℕ) : ℝ))
        atTop
        (𝓝 (Real.arctan (eval x))) :=
    (Real.hasSum_arctan (x := eval x) (by simpa [Real.norm_eq_abs] using hx)).tendsto_sum_nat

  have hclassical :
      Tendsto
        (fun N => eval (atanPartialSum A x N))
        atTop
        (𝓝 (Real.arctan (eval x))) := by
    simpa only [eval_atanPartialSum] using hseries

  exact tendsto_nhds_unique hsource hclassical

def oneFifth : ℚ := 1 / 5
def oneTwoHundredThirtyNinth : ℚ := 1 / 239

def bishopOneFifth : RegularRatReal := rational oneFifth
def bishopOneTwoHundredThirtyNinth : RegularRatReal :=
  rational oneTwoHundredThirtyNinth

structure VendoredMachinSourceMirror
    (A : VendoredArithmeticMirror) where
  atanOneFifth : RegularRatReal
  atanOneTwoHundredThirtyNinth : RegularRatReal

  atanOneFifthConverges :
    BishopConvergesTo A
      (atanPartialSum A bishopOneFifth)
      atanOneFifth

  atanOneTwoHundredThirtyNinthConverges :
    BishopConvergesTo A
      (atanPartialSum A bishopOneTwoHundredThirtyNinth)
      atanOneTwoHundredThirtyNinth

open VendoredMachinSourceMirror public

theorem eval_atanOneFifth
    (A : VendoredArithmeticMirror)
    (M : VendoredMachinSourceMirror A) :
    eval M.atanOneFifth = Real.arctan (1 / 5 : ℝ) := by
  have hpoint : eval bishopOneFifth = (1 / 5 : ℝ) := by
    rw [bishopOneFifth, eval_rational]
    norm_num [oneFifth]
  rw [← hpoint]
  apply eval_atan_eq_real_arctan
    A bishopOneFifth M.atanOneFifth
    M.atanOneFifthConverges
  rw [hpoint]
  norm_num

theorem eval_atanOneTwoHundredThirtyNinth
    (A : VendoredArithmeticMirror)
    (M : VendoredMachinSourceMirror A) :
    eval M.atanOneTwoHundredThirtyNinth =
      Real.arctan (1 / 239 : ℝ) := by
  have hpoint :
      eval bishopOneTwoHundredThirtyNinth =
        (1 / 239 : ℝ) := by
    rw [bishopOneTwoHundredThirtyNinth, eval_rational]
    norm_num [oneTwoHundredThirtyNinth]
  rw [← hpoint]
  apply eval_atan_eq_real_arctan
    A bishopOneTwoHundredThirtyNinth
    M.atanOneTwoHundredThirtyNinth
    M.atanOneTwoHundredThirtyNinthConverges
  rw [hpoint]
  norm_num

/-- Exact mirror of the Agda bishopMachinPi construction. -/
def machinPiB
    (A : VendoredArithmeticMirror)
    (M : VendoredMachinSourceMirror A) : RegularRatReal :=
  sub A
    (A.mul (rational 16) M.atanOneFifth)
    (A.mul (rational 4) M.atanOneTwoHundredThirtyNinth)

/-- The constructed Bishop Machin real evaluates to classical pi. -/
theorem eval_machinPi_eq_real_pi
    (A : VendoredArithmeticMirror)
    (M : VendoredMachinSourceMirror A) :
    eval (machinPiB A M) = Real.pi := by
  rw [machinPiB, eval_sub,
      A.eval_mul, A.eval_mul,
      eval_rational, eval_rational,
      eval_atanOneFifth A M,
      eval_atanOneTwoHundredThirtyNinth A M]

  have hmachin :=
    Real.four_mul_arctan_inv_5_sub_arctan_inv_239

  have hmachin' :
      4 * Real.arctan (1 / 5 : ℝ) -
        Real.arctan (1 / 239 : ℝ) =
      Real.pi / 4 := by
    simpa [div_eq_mul_inv] using hmachin

  linarith

structure VendorMachinPiSemanticsBoundary where
  literalAtanSeriesMirrored : Bool
  bishopAtanConvergenceTransportReused : Bool
  classicalArctanSeriesReused : Bool
  johnMachinIdentityReused : Bool
  bishopAtanOneFifthSemanticIdentificationOwned : Bool
  bishopAtanOne239SemanticIdentificationOwned : Bool
  bishopMachinPiSemanticIdentificationOwned : Bool

  actualAgdaMachinConvergenceMirrorInhabited : Bool

def vendorMachinPiSemanticsBoundary :
    VendorMachinPiSemanticsBoundary where
  literalAtanSeriesMirrored := true
  bishopAtanConvergenceTransportReused := true
  classicalArctanSeriesReused := true
  johnMachinIdentityReused := true
  bishopAtanOneFifthSemanticIdentificationOwned := true
  bishopAtanOne239SemanticIdentificationOwned := true
  bishopMachinPiSemanticIdentificationOwned := true

  actualAgdaMachinConvergenceMirrorInhabited := false

end

end Integration.BishopVendoredMachinPiSemantics
