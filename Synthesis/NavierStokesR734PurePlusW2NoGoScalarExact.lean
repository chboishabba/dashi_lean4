import Mathlib

/-!
# NS R734 W2: exact scalar lower certificate for the original six-mode
# pure-plus Galerkin physical counterexample (Agda PR #1271)

Physical source owner: PR #1271
Docs/research/ns_r734_pure_plus_physical_w2_no_go_20261027.md;
Waleffe 1992 helical triad calculus, classical Leray projected NSE.
The SOURCE-PHYSICAL Fourier computation of X=8,D=36 and the selected
Pcrit=(5+sqrt(5)-sqrt(30))/10 is checked independently by exact SymPy
against the original N=2 six-mode Fourier projection; this Lean module
proves its subsequent irrational inequality and amplitude 512 sign.

It does NOT yet prove the Fourier source-to-expression identity in Lean,
nor the real Galerkin local-flow/short-time W2 contradiction in Lean.
Those mathematical transport obligations remain explicit. This is a
negative control against an auxiliary universal W2, NOT blow-up.
Native Lean 4.28 source-written candidate, current kernel check pending.
-/

namespace Synthesis
noncomputable section

def nsR734PurePlusPcrit : ℝ :=
  (5 + Real.sqrt 5 - Real.sqrt 30) / 10

theorem nsR734SqrtFiveAboveTwo : (2 : ℝ) < Real.sqrt 5 := by
  have h : (Real.sqrt (5 : ℝ)) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

theorem nsR734SqrtThirtyBelowElevenHalves :
    Real.sqrt 30 < (11 : ℝ) / 2 := by
  have h : (Real.sqrt (30 : ℝ)) ^ 2 = 30 :=
    Real.sq_sqrt (by norm_num)
  have hn : (0 : ℝ) ≤ Real.sqrt 30 := Real.sqrt_nonneg 30
  nlinarith

theorem nsR734PurePlusPcritStrictLower :
    (3 : ℝ) / 20 < nsR734PurePlusPcrit := by
  unfold nsR734PurePlusPcrit
  have h1 := nsR734SqrtFiveAboveTwo
  have h2 := nsR734SqrtThirtyBelowElevenHalves
  linarith

/-- The ORIGINAL N=2, viscosity-one selected X critical production
at amplitude 512 is positive once its true Fourier coefficient is
identified with the source Pcrit. -/
theorem nsR734Amplitude512DyadicCriticalDerivativePositive :
    0 < (512 : ℝ) ^ 3 * nsR734PurePlusPcrit -
          2 * (512 : ℝ) ^ 2 * 36 := by
  have hp := nsR734PurePlusPcritStrictLower
  have h : 0 < (512 : ℝ) * nsR734PurePlusPcrit - 72 := by
    nlinarith
  calc
    0 < (512 : ℝ) ^ 2 *
      ((512 : ℝ) * nsR734PurePlusPcrit - 72) := by
        exact mul_pos (by norm_num) h
    _ = (512 : ℝ) ^ 3 * nsR734PurePlusPcrit -
          2 * (512 : ℝ) ^ 2 * 36 := by ring

#print axioms nsR734PurePlusPcritStrictLower
#print axioms nsR734Amplitude512DyadicCriticalDerivativePositive

end
end Synthesis
