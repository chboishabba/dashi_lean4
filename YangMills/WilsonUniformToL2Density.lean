import Mathlib
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Uniform Wilson density implies L² density

For any finite weakly regular measure, bounded continuous functions have dense
image in `L²`.  Therefore a Wilson/cylinder submodule that is already uniformly
dense in bounded continuous functions remains dense after the canonical map to
`L²`.  This identifies a common physical source theorem behind the bounded
measure-determining route and the spectral-completeness route.
-/

open MeasureTheory

namespace RequestProject.YangMills

/--
Uniform density of a Wilson/cylinder submodule transports through the canonical
bounded-continuous-to-`L²` map.  The analytic `L²` density step is therefore not
an additional Yang--Mills hypothesis.
-/
theorem wilson_uniform_dense_to_L2_dense
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (wilsonSubmodule : Submodule ℝ (Ω →ᵇ ℝ))
    (hDense : wilsonSubmodule.topologicalClosure = ⊤) :
    (wilsonSubmodule.map
      (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ := by
  exact
    (BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (by norm_num)).topologicalClosure_map_submodule
      hDense

/-- Exact remaining F2 source theorem in the uniform-observable route. -/
def WilsonUniformDensityProducerExists
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (wilsonSubmodule : Submodule ℝ (Ω →ᵇ ℝ)) : Prop :=
  wilsonSubmodule.topologicalClosure = ⊤

end RequestProject.YangMills
