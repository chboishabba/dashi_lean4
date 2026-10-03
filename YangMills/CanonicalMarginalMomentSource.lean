import Mathlib
import YangMills.CanonicalProjectiveMarginals
import YangMills.ProjectiveMarginalMomentTightness

/-!
# Same-source moment transfer to canonical projective marginals

D3.2 should consume estimates proved on the selected cutoff law itself.  If
`V_m` is a coercive observable on the selected `m`-dimensional marginal, then
its marginal expectation is exactly the source expectation of
`V_m ∘ Φ_m`, because the marginal law is the pushforward of the same cutoff
probability measure by `Φ_m`.

This file turns that identity into the `RealMarginalMomentTightnessProducer`
expected by the existing D3 tightness compiler.  No independently selected
marginal law or duplicated physical estimate is introduced.
-/

open Set MeasureTheory

namespace RequestProject.YangMills

structure RealCanonicalMarginalMomentSource
    (Ω : Type*) [MeasurableSpace Ω] where
  family : RealCanonicalProjectiveMarginalFamily Ω
  cost : (m : ℕ) → (Fin m → ℝ) → ENNReal
  costMeasurable : ∀ m, Measurable (cost m)
  momentBound : ℕ → ENNReal
  sourceUniformMoment :
    ∀ (m k : ℕ),
      (∫⁻ x : Ω, cost m (family.observable m x)
        ∂((family.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      momentBound m
  compactSublevel :
    ∀ (m : ℕ) (R : ENNReal), R ≠ ⊤ →
      IsCompact {x : Fin m → ℝ | cost m x ≤ R}
  threshold :
    ∀ (m : ℕ) (ε : ENNReal), 0 < ε →
      ∃ R : ENNReal,
        R ≠ 0 ∧ R ≠ ⊤ ∧ momentBound m / R ≤ ε

namespace RealCanonicalMarginalMomentSource

/-- The canonical marginal moment is literally the native source moment. -/
theorem marginal_lintegral_eq_source
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω)
    (m k : ℕ) :
    (∫⁻ y : Fin m → ℝ, source.cost m y
      ∂((source.family.marginal m k : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ))) =
    ∫⁻ x : Ω, source.cost m (source.family.observable m x)
      ∂((source.family.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω) := by
  unfold RealCanonicalProjectiveMarginalFamily.marginal
  rw [lintegral_map'
    (source.costMeasurable m).aemeasurable
    (source.family.observableMeasurable m).aemeasurable]

/-- Native selected-law moments therefore satisfy the marginal D3.2 bound. -/
theorem marginal_uniform_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω)
    (m k : ℕ) :
    (∫⁻ y : Fin m → ℝ, source.cost m y
      ∂((source.family.marginal m k : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ))) ≤ source.momentBound m := by
  rw [source.marginal_lintegral_eq_source m k]
  exact source.sourceUniformMoment m k

/-- Compile same-source estimates directly into the existing marginal tightness producer. -/
def toMomentTightnessProducer
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω) :
    RealMarginalMomentTightnessProducer where
  marginal := source.family.marginal
  cost := source.cost
  costMeasurable := source.costMeasurable
  momentBound := source.momentBound
  uniformMoment := source.marginal_uniform_moment
  compactSublevel := source.compactSublevel
  threshold := source.threshold

/-- Hence every selected finite marginal family is genuinely tight. -/
theorem marginal_tight
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω)
    (m : ℕ) :
    IsTightMeasureSet
      {ν : Measure (Fin m → ℝ) |
        ∃ p ∈ Set.range (source.family.marginal m),
          ((p : ProbabilityMeasure (Fin m → ℝ)) :
            Measure (Fin m → ℝ)) = ν} :=
  source.toMomentTightnessProducer.marginal_tight m

end RealCanonicalMarginalMomentSource

end RequestProject.YangMills
