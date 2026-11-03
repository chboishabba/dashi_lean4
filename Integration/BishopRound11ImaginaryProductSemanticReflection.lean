import Integration.BishopRound11MachinSourceBinding
import Integration.BishopVendoredMachinPiSemantics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# K05: source-faithful imaginary-exponential semantic reflection

For EVERY source-backed Round11/Machin binding, the very same Bishop
signed-factorial cosine/sine limits satisfy both addition identities
under Bishop's **actual resampled arithmetic**. We prove this using
the source convergence -> classical semantic evaluator, classical
trigonometry, and reflection of evaluation equality into the original
Bishop setoid.

This is an independent Lean proof route for the *original* same-series
identity. It is NOT a native Agda mixed-factorial Cauchy coefficient
proof, an Agda proof-term import, or an Agda kernel receipt.
The Agda golden product theorem remains a separate source obligation.

Sources: Bishop & Bridges; Zachary Murray; Viktor Csimma;
John Machin; original DASHI proof owners; Mathlib trigonometry.
-/

namespace Integration.BishopRound11ImaginaryProductSemanticReflection

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredExponentialSemantics
open Integration.BishopVendoredTrigSemantics
open Integration.BishopVendoredMachinPiSemantics
open Integration.BishopRound11MachinSourceBinding

noncomputable section

/-- Cartesian real coordinate of the original pure-imaginary
exponential product on the vendored Bishop pair. -/
def cosineProduct (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x y : RegularRatReal) : RegularRatReal :=
  A.add
    (A.mul (B.cosB x) (B.cosB y))
    (A.neg (A.mul (B.sinB x) (B.sinB y)))

/-- Cartesian imaginary coordinate of the same product. -/
def sineProduct (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x y : RegularRatReal) : RegularRatReal :=
  A.add
    (A.mul (B.sinB x) (B.cosB y))
    (A.mul (B.cosB x) (B.sinB y))

private theorem eval_sinB
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x : RegularRatReal) :
    eval (B.sinB x) = Real.sin (eval x) :=
  eval_sin_eq_real_sin A (trigMirror A B) x

private theorem eval_cosB
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x : RegularRatReal) :
    eval (B.cosB x) = Real.cos (eval x) :=
  eval_cos_eq_real_cos A (trigMirror A B) x

/-- The original Bishop cosine addition theorem, not a fresh function. -/
theorem sourceCosineAddition
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x y : RegularRatReal) :
    Equiv (B.cosB (A.add x y)) (cosineProduct A B x y) := by
  apply eval_eq_iff_equiv.mp
  calc
    eval (B.cosB (A.add x y))
        = Real.cos (eval (A.add x y)) := eval_cosB A B _
    _ = Real.cos (eval x) * Real.cos (eval y) -
        Real.sin (eval x) * Real.sin (eval y) := by
          rw [A.eval_add, Real.cos_add]
    _ = eval (cosineProduct A B x y) := by
          simp only [cosineProduct, A.eval_add, A.eval_mul,
            A.eval_neg, eval_cosB, eval_sinB]
          ring

/-- The original Bishop sine addition theorem, same native data. -/
theorem sourceSineAddition
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x y : RegularRatReal) :
    Equiv (B.sinB (A.add x y)) (sineProduct A B x y) := by
  apply eval_eq_iff_equiv.mp
  calc
    eval (B.sinB (A.add x y))
        = Real.sin (eval (A.add x y)) := eval_sinB A B _
    _ = Real.sin (eval x) * Real.cos (eval y) +
        Real.cos (eval x) * Real.sin (eval y) := by
          rw [A.eval_add, Real.sin_add]
    _ = eval (sineProduct A B x y) := by
          simp only [sineProduct, A.eval_add, A.eval_mul,
            eval_cosB, eval_sinB]
          ring

/-- Precisely the original pure-imaginary complex exponential product
in componentwise Bishop setoid equality. Its source Agda double Cauchy
reindexing is **not** claimed to be established by this Lean route. -/
theorem sourceImaginaryExponentialProduct
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (x y : RegularRatReal) :
    Equiv (B.cosB (A.add x y)) (cosineProduct A B x y) ∧
    Equiv (B.sinB (A.add x y)) (sineProduct A B x y) :=
  ⟨sourceCosineAddition A B x y, sourceSineAddition A B x y⟩

/-- The actual source Machin pi used by the Round11 binding. -/
def sourceMachinPi (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) : RegularRatReal :=
  machinPiB A (machinMirror A B)

/-- Actual Bishop quarter angle: the source pi times the rational 1/4. -/
def sourceMachinQuarter (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) : RegularRatReal :=
  A.mul (rational (1 / 4 : ℚ)) (sourceMachinPi A B)

theorem eval_sourceMachinQuarter (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    eval (sourceMachinQuarter A B) = Real.pi / 4 := by
  rw [sourceMachinQuarter, A.eval_mul, eval_rational,
    sourceMachinPi, eval_machinPi_eq_real_pi A (machinMirror A B)]
  ring

/-- The original Round11 source sine/cosine have equal values at
the true Bishop Machin quarter angle, via source-faithful evaluation.
This is stronger than relying on the rational tangent polynomial alone,
but it remains a Lean companion proof, not an Agda native theorem. -/
theorem sourceMachinQuarterCosineEqualsSine
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    Equiv (B.cosB (sourceMachinQuarter A B))
      (B.sinB (sourceMachinQuarter A B)) := by
  apply eval_eq_iff_equiv.mp
  rw [eval_cosB, eval_sinB, eval_sourceMachinQuarter]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- The actual original Agda quarter expression is
    4 atan_B(1/5) - atan_B(1/239), not an arbitrary pi/4 object.
This source-faithful expression uses the same Bishop input limits. -/
def originalSourceMachinAtanQuarter
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) : RegularRatReal :=
  A.add
    (A.mul (rational (4 : ℚ)) B.atanOneFifth)
    (A.neg B.atanOneTwoHundredThirtyNinth)

/-- Same-object quarter transport: actual arctangent construction
agrees in the vendored Bishop setoid with 1/4 of its Machin real.
Only original resampled ring operations and faithful evaluation used. -/
theorem originalAtanQuarter_equiv_MachinPiQuarter
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    Equiv (originalSourceMachinAtanQuarter A B)
      (sourceMachinQuarter A B) := by
  apply eval_eq_iff_equiv.mp
  simp only [originalSourceMachinAtanQuarter, sourceMachinQuarter,
    sourceMachinPi, machinPiB, eval_sub, A.eval_add, A.eval_neg,
    A.eval_mul, eval_rational]
  ring

/-- K05 quarter sine/cosine equality at the ACTUAL source
arctangent expression (not only the synthetically written pi/4). -/
theorem originalAtanQuarterCosineEqualsSine
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    Equiv (B.cosB (originalSourceMachinAtanQuarter A B))
      (B.sinB (originalSourceMachinAtanQuarter A B)) := by
  apply eval_eq_iff_equiv.mp
  have hquarter :
      eval (originalSourceMachinAtanQuarter A B) = Real.pi / 4 := by
    calc
      eval (originalSourceMachinAtanQuarter A B)
          = eval (sourceMachinQuarter A B) :=
            eval_respects_equiv (originalAtanQuarter_equiv_MachinPiQuarter A B)
      _ = Real.pi / 4 := eval_sourceMachinQuarter A B
  rw [eval_cosB, eval_sinB, hquarter,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- Source Machin's pi is classically the true pi under the
proved faithful evaluator, and this implication is independent
of the native source quarter-angle route. -/
theorem sourceMachinPiEvaluatesToClassicalPi
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    eval (sourceMachinPi A B) = Real.pi :=
  eval_machinPi_eq_real_pi A (machinMirror A B)


/-- Terminal π characterization on the *same* source-faithful
Round11 series: its Machin real is a positive zero, and every
positive sine zero has angle at least that Machin real (under
faithful evaluation). This discharges the classical LEAST ZERO
semantic leaf in Lean without assuming a nonminimal period.

A distinct Agda-native constructive sine-positive-on-(0,pi_M)
theorem or verified semantic importer remains a golden obligation. -/
theorem sourceMachinPi_is_first_positive_sine_zero
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    0 < eval (sourceMachinPi A B) ∧
    Equiv (B.sinB (sourceMachinPi A B)) A.zero ∧
    (∀ x : RegularRatReal,
      0 < eval x →
      Equiv (B.sinB x) A.zero →
      eval (sourceMachinPi A B) ≤ eval x) := by
  have hPi := sourceMachinPiEvaluatesToClassicalPi A B
  constructor
  · rw [hPi]
    exact Real.pi_pos
  constructor
  · apply eval_eq_iff_equiv.mp
    rw [eval_sinB, hPi, Real.sin_pi, A.eval_zero]
  · intro x hx hzero
    rw [hPi]
    have hs : Real.sin (eval x) = 0 := by
      have heq := eval_respects_equiv hzero
      rwa [eval_sinB, A.eval_zero] at heq
    by_contra h
    have hlt : eval x < Real.pi := lt_of_not_ge h
    have hspos : 0 < Real.sin (eval x) :=
      Real.sin_pos_of_pos_of_lt_pi hx hlt
    linarith

end

end Integration.BishopRound11ImaginaryProductSemanticReflection
