import Mathlib
import YangMills.WilsonCylinderCompactification

open MeasureTheory

/-!
# Finite cutoff laws on the canonical Wilson-cylinder state

The cylinder-first continuum state is not introduced after taking a projective
limit.  Every finite cutoff law is pushed through the SAME bounded Wilson
coordinate map into the compact closure state.  Consequently the D3/projective
measure construction is performed directly on the intended generalized
cylinder carrier, with no later image-support or pullback theorem required.
-/

namespace RequestProject.YangMills

/-- Raw configurations embed into the closure of their bounded coordinate image. -/
def wilsonCylinderEmbed
    {Ω : Type*} (raw : ℕ → Ω → ℝ) : Ω → WilsonCylinderState raw :=
  fun x =>
    ⟨wilsonTanhCubeMap raw x,
      subset_closure (Set.mem_range_self x)⟩

/-- Coordinatewise measurability makes the raw-to-cube map measurable. -/
theorem wilsonTanhCubeMap_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i)) :
    Measurable (wilsonTanhCubeMap raw) := by
  apply measurable_pi_lambda
  intro i
  apply Measurable.subtype_mk
  have hi := hMeas i
  fun_prop

/-- The same map, codomain-restricted to the cylinder closure, is measurable. -/
theorem wilsonCylinderEmbed_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i)) :
    Measurable (wilsonCylinderEmbed raw) := by
  exact Measurable.subtype_mk
    (wilsonTanhCubeMap_measurable raw hMeas)

/-- Push one physical finite probability law onto the canonical cylinder state. -/
noncomputable def wilsonCylinderPushforward
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (μ : ProbabilityMeasure Ω) :
    ProbabilityMeasure (WilsonCylinderState raw) :=
  ⟨(μ : Measure Ω).map (wilsonCylinderEmbed raw),
    (Measure.isProbabilityMeasure_map_iff
      (wilsonCylinderEmbed_measurable raw hMeas).aemeasurable).2 inferInstance⟩

/-- The whole finite cutoff family now lives on the SAME compact cylinder carrier. -/
noncomputable def wilsonCylinderCutoffLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    ℕ → ProbabilityMeasure (WilsonCylinderState raw) :=
  fun cutoff => wilsonCylinderPushforward raw hMeas (cutoffLaw cutoff)

end RequestProject.YangMills
