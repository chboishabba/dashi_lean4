import Mathlib
import Mathlib.MeasureTheory.Group.Integral

/-!
# Independent Haar pair collapses to one relative boundary variable

For a probability Haar law, the relative variable `g⁻¹ * h` is Haar whenever
`g` and `h` are independent Haar variables.  This is the exact change of
variables needed by the finite Wilson gauge-projection route: the augmented
positive quadratic form naturally carries independent boundary copies on its
two half spaces, while the literal projected Wilson kernel is written with one
shared boundary field.

The theorem is purely measure-theoretic.  It neither assumes nor proves Wilson
reflection positivity; the remaining Block-A work is the same-object lattice
readback identifying the literal crossing features with a function of this
relative boundary variable.
-/

open MeasureTheory

namespace RequestProject.YangMills

/--
Two independent Haar variables reduce exactly to one Haar-distributed relative
variable.  No integrability assumption is needed beyond the ordinary real
integral conventions: the inner identity is `integral_mul_left_eq_self`, and
the outer integral is over a probability law.
-/
theorem haar_double_integral_relative_eq_single
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
    (k : G → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂μ ∂μ) = ∫ u, k u ∂μ := by
  have hInner : ∀ g : G, (∫ h, k (g⁻¹ * h) ∂μ) = ∫ u, k u ∂μ := by
    intro g
    exact integral_mul_left_eq_self k g⁻¹
  simp_rw [hInner]
  simp

end RequestProject.YangMills
