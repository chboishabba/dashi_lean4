import NSBControl.Rational345BPClosed

namespace NSBControl
namespace Rational345BPClosedTest

open Set
open Rational345RealRadius4
open Rational345RealInitialState
open Rational345R830DecisionCompiler
open Rational345R830ResidenceInterval
open Rational345BPBudget
open Rational345BPClosed

example : BPLeaf := by
  exact bpLeaf_closed

example :
    ∃ (u : ℝ → State) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      u 0 = u₀ ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (galerkinField (u t)) t) ∧
      (∀ t : ℝ, |t| < δ →
        u t ∈ Metric.closedBall u₀ bpBootstrapRadius) ∧
      (∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
        selectedRate (u t) < 0) := by
  exact r830_pointwise_negative_witness

end Rational345BPClosedTest
end NSBControl
