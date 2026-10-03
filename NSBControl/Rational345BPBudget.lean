import Mathlib.Tactic
import NSBControl.Rational345ShortTime

/-!
# B_P coarse structural budget arithmetic

This file contains only the numerical budget propagated through the literal
selected-rate decomposition.  The analytic/operator lemmas that feed these
constants are kept separate.

Bootstrap choice:
  radius = 1/100, hence ||x|| <= 601/100 using ||u0|| <= 6.

Structural constants in component sup norm:
* helical projector: H = 21/4;
* full projected bilinear convolution: B = 729 * 30 = 21870;
* one fixed-output mixed fold and one forcing-commutator fold use at most 729
  resonant p choices for a fixed output.

The resulting rate difference constant is intentionally coarse but remains
strictly below the existing R828 certified Lipschitz budget.
-/

namespace NSBControl
namespace Rational345BPBudget

open Rational345ShortTime

def bpBootstrapRadius : ℝ := 1 / 100
def stateBound : ℝ := 601 / 100

def helicalConstant : ℝ := 21 / 4
def projectedBilinearConstant : ℝ := 21870

def forcingValueBound : ℝ :=
  projectedBilinearConstant * stateBound^2

def forcingLipschitzBound : ℝ :=
  2 * projectedBilinearConstant * stateBound

/-- Bound for one fixed-output mixed vector component. -/
def mixedValueBound : ℝ :=
  729 * 2 * helicalConstant^2 * stateBound^2

/-- Difference constant for one fixed-output mixed vector component. -/
def mixedLipschitzBound : ℝ :=
  729 * 4 * helicalConstant^2 * stateBound

/-- Bound for one fixed-output forcing-commutator vector component. -/
def commutatorValueBound : ℝ :=
  729 * 4 * helicalConstant^2 * forcingValueBound * stateBound

/-- Difference constant for one fixed-output forcing-commutator component. -/
def commutatorLipschitzBound : ℝ :=
  729 * 4 * helicalConstant^2 *
    (forcingLipschitzBound * stateBound + forcingValueBound)

/-- Difference constant of one coherent-work output row:
2 Re <M,G>, with three complex components. -/
def coherentOutputLipschitzBound : ℝ :=
  6 *
    (mixedLipschitzBound * commutatorValueBound +
     mixedValueBound * commutatorLipschitzBound)

/-- Global R692 work sums at most all 729 radius-four outputs. -/
def globalCoherentLipschitzBound : ℝ :=
  729 * coherentOutputLipschitzBound

/-- Critical production difference bound.  Weight <=4 and the literal factor
2 give 8; the Hermitian product has three components. -/
def criticalProductionLipschitzBound : ℝ :=
  729 * 24 *
    (forcingValueBound + stateBound * forcingLipschitzBound)

/-- Critical dissipation difference bound.  Weight <=4, |k|^2<=48 and three
components give 4*48*3*2*R = 1152R per output. -/
def criticalDissipationLipschitzBound : ℝ :=
  729 * 1152 * stateBound

/-- Literal R815 normalization: 72*C + 6*P + 6*D. -/
def selectedRateLipschitzBudget : ℝ :=
  72 * globalCoherentLipschitzBound +
  6 * criticalProductionLipschitzBound +
  6 * criticalDissipationLipschitzBound

theorem bpBootstrapRadius_pos : 0 < bpBootstrapRadius := by
  norm_num [bpBootstrapRadius]

theorem stateBound_exact : stateBound = 601 / 100 := rfl

theorem helicalConstant_pos : 0 < helicalConstant := by
  norm_num [helicalConstant]

theorem projectedBilinearConstant_nonneg :
    0 ≤ projectedBilinearConstant := by
  norm_num [projectedBilinearConstant]

/-- Exact rational value, useful for auditing the margin independently of any
operator proof. -/
theorem selectedRateLipschitzBudget_exact :
    selectedRateLipschitzBudget =
      (580457195372468648627735272641 : ℝ) / 4000000 := by
  norm_num [selectedRateLipschitzBudget,
    globalCoherentLipschitzBound, coherentOutputLipschitzBound,
    mixedLipschitzBound, mixedValueBound,
    commutatorLipschitzBound, commutatorValueBound,
    forcingLipschitzBound, forcingValueBound,
    criticalProductionLipschitzBound,
    criticalDissipationLipschitzBound,
    projectedBilinearConstant, helicalConstant, stateBound]

/-- B_P has about 2.7x headroom even with this deliberately crude structural
estimate. -/
theorem selectedRateLipschitzBudget_le_certified :
    selectedRateLipschitzBudget ≤ rateLipschitzBound := by
  rw [selectedRateLipschitzBudget_exact]
  norm_num [rateLipschitzBound]

end Rational345BPBudget
end NSBControl
