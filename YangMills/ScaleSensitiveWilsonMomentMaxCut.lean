import Mathlib
import YangMills.LiteralSU2FourDimensionalLattice

/-!
# The strongest cutoff-uniform Wilson bound available for free

The positive SU(2) plaquette cost lies in [0,2]. Consequently the average
plaquette cost has a cutoff-uniform bound by 2 under every probability law,
including Wilson and complete Gibbs measures.

This is useful as a negative control for the Clay compactness programme:
the estimate is genuinely uniform, but the observable is bounded and therefore
cannot by itself be the required scale-sensitive coercive function for an
unbounded/projective continuum topology.

The theorem prevents a later proof from silently relabelling the trivial
bounded plaquette observable as the missing coercive moment producer.
-/

namespace RequestProject.YangMills

def su2AveragePlaquetteCost
    (L : ℕ) [NeZero L] (links : SU2TorusLinks L) : ℝ :=
  (∑ p ∈ su2FourDimensionalPlaquettes L,
      su2PositivePlaquetteCost
        (su2Plaquette links p.1 p.2.1 p.2.2)) /
    ((su2FourDimensionalPlaquettes L).card : ℝ)

theorem su2_average_plaquette_cost_bounds
    (L : ℕ) [NeZero L]
    (hCard : (su2FourDimensionalPlaquettes L).card ≠ 0)
    (links : SU2TorusLinks L) :
    0 ≤ su2AveragePlaquetteCost L links ∧
      su2AveragePlaquetteCost L links ≤ 2 := by
  have hAction :=
    su2_four_dimensional_wilson_action_bounds
      L links (1 : ℝ) (by norm_num)
  have hCardReal :
      0 < ((su2FourDimensionalPlaquettes L).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hCard
  constructor
  · unfold su2AveragePlaquetteCost
    have hsum :
        0 ≤ ∑ p ∈ su2FourDimensionalPlaquettes L,
          su2PositivePlaquetteCost
            (su2Plaquette links p.1 p.2.1 p.2.2) := by
      simpa [su2FourDimensionalWilsonAction,
        finiteSU2WilsonAction] using hAction.1
    exact div_nonneg hsum hCardReal.le
  · unfold su2AveragePlaquetteCost
    have hsum :
        (∑ p ∈ su2FourDimensionalPlaquettes L,
          su2PositivePlaquetteCost
            (su2Plaquette links p.1 p.2.1 p.2.2))
        ≤ 2 * ((su2FourDimensionalPlaquettes L).card : ℝ) := by
      simpa [su2FourDimensionalWilsonAction,
        finiteSU2WilsonAction] using hAction.2
    apply (div_le_iff₀ hCardReal).2
    nlinarith

/--
Every probability measure inherits the same bound once measurability is paid.
No Wilson-specific dynamics enters this estimate.
-/
theorem su2_average_plaquette_cost_expectation_le_two
    (L : ℕ) [NeZero L]
    (hCard : (su2FourDimensionalPlaquettes L).card ≠ 0)
    (μ : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (hMeasurable : Measurable (su2AveragePlaquetteCost L)) :
    (∫ links : SU2TorusLinks L,
        su2AveragePlaquetteCost L links
      ∂((μ : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L))) ≤ 2 := by
  let m : MeasureTheory.Measure (SU2TorusLinks L) := μ
  have hNonneg : ∀ links, 0 ≤ su2AveragePlaquetteCost L links :=
    fun links => (su2_average_plaquette_cost_bounds L hCard links).1
  have hUpper : ∀ links, su2AveragePlaquetteCost L links ≤ 2 :=
    fun links => (su2_average_plaquette_cost_bounds L hCard links).2
  have hIntegrable :
      MeasureTheory.Integrable (su2AveragePlaquetteCost L) m := by
    apply MeasureTheory.Integrable.of_bound
      hMeasurable.aestronglyMeasurable 2
    exact Filter.Eventually.of_forall (fun links => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg links)]
      exact hUpper links)
  calc
    ∫ links : SU2TorusLinks L,
        su2AveragePlaquetteCost L links ∂m
      ≤ ∫ _ : SU2TorusLinks L, (2 : ℝ) ∂m := by
        exact MeasureTheory.integral_mono
          hIntegrable (MeasureTheory.integrable_const 2) hUpper
    _ = 2 := by simp [m]

/--
A marker proposition for the genuinely missing Clay-facing producer.

Unlike the bounded average plaquette cost, the selected observable must be
coercive for the chosen continuum/projective topology. This definition has no
constructor here: the physical RG estimate must supply one.
-/
def ScaleSensitiveWilsonMomentBound
    {Ω : Type*}
    (μ : ℕ → MeasureTheory.ProbabilityMeasure Ω)
    (cost : ℕ → Ω → ℝ) : Prop :=
  ∃ M : ℝ, ∀ k,
    (∫ x : Ω, cost k x
      ∂((μ k : MeasureTheory.ProbabilityMeasure Ω) :
        MeasureTheory.Measure Ω)) ≤ M

end RequestProject.YangMills
