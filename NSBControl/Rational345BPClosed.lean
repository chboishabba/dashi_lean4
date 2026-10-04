import NSBControl.Rational345BPCoherent
import NSBControl.Rational345BPMixedBounds
import NSBControl.Rational345BPCommutatorBounds
import NSBControl.Rational345R830PointwiseNegative

/-!
# B_P closure owner

Assembles the four finite operator inequalities, closes the degree-five
coherent-work leaf, combines it with the already-closed production and
dissipation estimates, and produces the exact `BPLeaf` consumed by the R830
decision compiler.

This owner also exposes the stronger residence-aware R830 witness: the same
local solution carries its bootstrap-ball residence and pointwise negative
selected rate, allowing later physicality constraints to shrink the terminal
interval without repeating B_Q/B_P arithmetic.
-/

namespace NSBControl
namespace Rational345BPClosed

open Set
open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPCoherent
open Rational345BPMixedBounds
open Rational345BPCommutatorBounds
open Rational345BPMaxCut
open Rational345BPProduction
open Rational345BPBudget
open Rational345BQGeometry
open Rational345R830DecisionCompiler
open Rational345R830LocalInterval
open Rational345R830ResidenceInterval
open Rational345R830PointwiseNegative

/-- All four R692 operator bounds. -/
theorem coherentOperatorLeaves_closed : CoherentOperatorLeaves where
  mixedValue := by
    intro u hu k
    exact fixedOutputMixed_norm_le hu k
  mixedDiff := by
    intro x hx y hy k
    exact fixedOutputMixed_diff_norm_le hx hy k
  commutatorValue := by
    intro u hu k
    exact fixedOutputCommutator_norm_le hu k
  commutatorDiff := by
    intro x hx y hy k
    exact fixedOutputCommutator_diff_norm_le hx hy k

/-- Degree-five global coherent-work leaf. -/
theorem coherentLeaf_closed : CoherentLeaf :=
  coherentLeaf_of_operator_leaves coherentOperatorLeaves_closed

/-- B_P is closed from coherent + cubic production; the quadratic dissipation
part is internal to `bpLeaf_of_two_leaves`. -/
theorem bpLeaf_closed : BPLeaf :=
  bpLeaf_of_two_leaves coherentLeaf_closed productionLeaf_closed

/-- Stronger public R830 witness.  In addition to the Picard derivative it
retains the actual radius-1/100 residence proof and the pointwise negative-rate
certificate used before integration. -/
theorem r830_pointwise_negative_witness :
    ∃ (u : ℝ → State) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      u 0 = u₀ ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (galerkinField (u t)) t) ∧
      (∀ t : ℝ, |t| < δ →
        u t ∈ Metric.closedBall u₀ bpBootstrapRadius) ∧
      (∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
        selectedRate (u t) < 0) := by
  obtain ⟨u, hu0, ε, hε, hderiv⟩ :=
    Rational345RealRadius4Quadratic.exists_local_solution u₀
  obtain ⟨δ, hδ, hres⟩ :=
    exists_positive_ball_residence
      galerkinField u u₀ hε bpBootstrapRadius_pos hu0 hderiv
  have hneg :=
    negative_rate_on_residence
      galerkinField u u₀ selectedRate
      hε hδ bpBootstrapRadius_pos hu0 hderiv hres
      (fun x hx => field_bound_on_bp_ball hx)
      bpLeaf_closed initial_rate_has_integer_margin
  exact ⟨u, ε, δ, hε, hδ, hu0, hderiv, hres, hneg⟩

/-- R830 endpoint in its original integrated existential form. -/
theorem r830_negative_integrated_payment :
    ∃ (u : ℝ → State) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      u 0 = u₀ ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (galerkinField (u t)) t) ∧
      (∫ t in (0 : ℝ)..residenceUsableTime ε δ,
        selectedRate (u t)) < 0 := by
  obtain ⟨u, ε, δ, hε, hδ, hu0, hderiv, hres, hneg⟩ :=
    r830_pointwise_negative_witness
  refine ⟨u, ε, δ, hε, hδ, hu0, hderiv, ?_⟩
  apply negative_integral_on_subinterval u selectedRate
    (residenceUsableTime_pos hε hδ) le_rfl
  · exact Rational345R830DecisionCompiler.selectedRate_continuous.continuousOn.comp
      (solution_continuousOn_residence hε hderiv)
      (fun _ ht => ht)
  · exact hneg

end Rational345BPClosed
end NSBControl
