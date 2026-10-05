import Mathlib
import YangMills.WilsonCountableStoneWeierstrass

open MeasureTheory

/-!
# One countable Wilson separation theorem pays L2 cyclicity

On a compact cylinder state space, countable continuous Wilson coordinates
whose joint map is injective generate a uniformly dense real subalgebra by
Stone--Weierstrass.  The standard dense-range theorem for continuous functions
in finite-measure Lp then carries that SAME generated algebra densely into L2.

This merges the central D and F2 physical obligations: no independent uniform
or L2 density hypothesis is needed once the chosen countable Wilson family is
continuous and point-separating on the compact state space.
-/

namespace RequestProject.YangMills

/-- The continuous-function submodule underlying the Wilson-generated algebra is dense. -/
theorem countable_wilson_generated_submodule_dense
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    (wilson : ℕ → C(Ω, ℝ))
    (hInjective : Function.Injective (fun x i => wilson i x)) :
    (wilsonGeneratedAlgebra wilson).toSubmodule.topologicalClosure = ⊤ := by
  exact congrArg Subalgebra.toSubmodule
    (wilson_generated_algebra_dense wilson hInjective)

/--
The SAME countable Wilson family has dense generated image in physical L2 for
any finite weakly regular measure on the compact cylinder state space.
-/
theorem countable_wilson_generated_algebra_L2_dense
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (wilson : ℕ → C(Ω, ℝ))
    (hInjective : Function.Injective (fun x i => wilson i x)) :
    ((wilsonGeneratedAlgebra wilson).toSubmodule.map
      (ContinuousMap.toLp (E := ℝ) (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ := by
  exact
    (ContinuousMap.toLp_denseRange ℝ μ ℝ ENNReal.coe_ne_top).topologicalClosure_map_submodule
      (countable_wilson_generated_submodule_dense wilson hInjective)

/--
Merged DF2 source package: one countable continuous injective Wilson coordinate
family on a compact state space.  Uniform density and L2 density are derived.
-/
structure CountableWilsonDF2Source
    (Ω : Type*) [TopologicalSpace Ω] where
  wilson : ℕ → C(Ω, ℝ)
  coordinateMapInjective : Function.Injective (fun x i => wilson i x)

namespace CountableWilsonDF2Source

/-- Uniform observable-algebra density follows from the single injectivity receipt. -/
theorem uniform_dense
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    (source : CountableWilsonDF2Source Ω) :
    (wilsonGeneratedAlgebra source.wilson).topologicalClosure = ⊤ :=
  wilson_generated_algebra_dense source.wilson source.coordinateMapInjective

/-- L2 cyclicity/density follows from the same injectivity receipt. -/
theorem L2_dense
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (source : CountableWilsonDF2Source Ω) :
    ((wilsonGeneratedAlgebra source.wilson).toSubmodule.map
      (ContinuousMap.toLp (E := ℝ) (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ :=
  countable_wilson_generated_algebra_L2_dense
    μ source.wilson source.coordinateMapInjective

end CountableWilsonDF2Source

end RequestProject.YangMills
