import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionCut

/-!
# Source-facing producer for the final finite Wilson OS2 leaf

The exact surviving Block-A proposition is positivity of the boundary-Haar
projected physical Wilson kernel.  The remaining source work has two logically
distinct parts:

1. identify the projected literal kernel with the positive kernel produced by
   the upper/lower half-path plus independent boundary-Haar calculation;
2. prove the quadratic form for that produced kernel is nonnegative.

This file makes those two obligations explicit and supplies the final compiler.
It does not relabel the obligations as a proof of Wilson RP: a concrete producer
must still be constructed from the literal crossing geometry.
-/

namespace RequestProject.YangMills

structure LiteralSU2BoundaryGaugeProjectionProducer where
  kernel :
    ∀ (n : ℕ) [NeZero n], ℝ →
      SU2PositiveInteriorLinks n → SU2PositiveInteriorLinks n → ℝ
  sameObject :
    ∀ (n : ℕ) [NeZero n] (β : ℝ),
      literalSU2BoundaryGaugeProjectedWilsonKernel n β = kernel n β
  reflectionPositive :
    ∀ (n : ℕ) [NeZero n] (β : ℝ), 0 ≤ β →
      ∀ f : SU2PositiveInteriorLinks n → ℝ,
        Measurable f →
        MeasureTheory.Integrable f (literalSU2PositiveInteriorHaar n) →
        0 ≤ ∫ left : SU2PositiveInteriorLinks n,
          ∫ right : SU2PositiveInteriorLinks n,
            f left * kernel n β left right * f right
            ∂(literalSU2PositiveInteriorHaar n)
          ∂(literalSU2PositiveInteriorHaar n)

/--
Final Block-A compiler: an actual same-object projected-kernel producer closes
`LiteralSU2BoundaryGaugeProjectionRPExact` without any additional Wilson-side
geometry or measure-theory assumptions.
-/
theorem literal_su2_boundary_gauge_projection_rp_of_producer
    (producer : LiteralSU2BoundaryGaugeProjectionProducer) :
    LiteralSU2BoundaryGaugeProjectionRPExact := by
  intro n hn β hβ f hfMeas hfInt
  letI : NeZero n := hn
  rw [producer.sameObject n β]
  exact producer.reflectionPositive n β hβ f hfMeas hfInt

/-- The precise live Block-A producer obligation. -/
def LiteralSU2BoundaryGaugeProjectionProducerExists : Prop :=
  Nonempty LiteralSU2BoundaryGaugeProjectionProducer

/-- Existence of the producer is exactly sufficient for finite projected Wilson RP. -/
theorem literal_su2_boundary_gauge_projection_rp_of_exists_producer
    (h : LiteralSU2BoundaryGaugeProjectionProducerExists) :
    LiteralSU2BoundaryGaugeProjectionRPExact := by
  rcases h with ⟨producer⟩
  exact literal_su2_boundary_gauge_projection_rp_of_producer producer

end RequestProject.YangMills
