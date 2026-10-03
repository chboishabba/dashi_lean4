import NSBControl.Rational345BPCoherent
import NSBControl.Rational345BPMixedBounds
import NSBControl.Rational345BPCommutatorBounds

/-!
# B_P closure owner

Assembles the four finite operator inequalities, closes the degree-five
coherent-work leaf, combines it with the already-closed production and
dissipation estimates, and produces the exact `BPLeaf` consumed by the R830
decision compiler.
-/

namespace NSBControl
namespace Rational345BPClosed

open Rational345BPCoherent
open Rational345BPMixedBounds
open Rational345BPCommutatorBounds
open Rational345BPMaxCut
open Rational345BPProduction
open Rational345R830DecisionCompiler

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

/-- R830 endpoint in its public existential form. -/
theorem r830_negative_integrated_payment :
    ∃ (u : ℝ → Rational345RealRadius4.State) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      u 0 = Rational345RealInitialState.u₀ ∧
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt u (Rational345RealRadius4.galerkinField (u t)) t) ∧
      (∫ t in (0 : ℝ)..Rational345R830ResidenceInterval.residenceUsableTime ε δ,
        Rational345RealRadius4.selectedRate (u t)) < 0 :=
  exists_local_solution_with_negative_integral bpLeaf_closed

end Rational345BPClosed
end NSBControl
