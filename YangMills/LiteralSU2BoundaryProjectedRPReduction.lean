import Mathlib
import YangMills.LiteralSU2BoundaryProjectedHalfWeightFactorization
import YangMills.LiteralSU2PositiveHalfAnalytic

/-!
# Final half-weight compiler for finite pure-Wilson OS2

The exact projected kernel has already been factored as

  K_proj(L,R) = h(L) K_avg(L,R) h(R).

For nonnegative coupling, `h` is measurable and lies in `(0,1]`.  Therefore an
L1 test multiplied by `h` is still L1, and ordinary reflection positivity of
the averaged crossing kernel immediately implies reflection positivity of the
full projected Wilson kernel.

After this file, the only Block-A theorem left is RP of `K_avg`, equivalently
the Fubini rearrangement of the already-positive augmented boundary-feature
quadratic form.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Exact remaining crossing-only proposition after all noncrossing weights are removed. -/
def LiteralSU2BoundaryAveragedCrossingRPExact : Prop :=
  ∀ (n : ℕ) (_ : NeZero n) (β : ℝ), 0 ≤ β →
    ∀ f : SU2PositiveInteriorLinks n → ℝ,
      Measurable f →
      Integrable f (literalSU2PositiveInteriorHaar n) →
      0 ≤ ∫ left : SU2PositiveInteriorLinks n,
        ∫ right : SU2PositiveInteriorLinks n,
          f left *
            literalSU2BoundaryAveragedCrossingKernel n β left right *
            f right
          ∂(literalSU2PositiveInteriorHaar n)
        ∂(literalSU2PositiveInteriorHaar n)

/-- The named half weight is measurable on the positive-interior field. -/
theorem su2_positive_interior_wilson_half_weight_measurable
    (n : ℕ) [NeZero n]
    (β : ℝ) :
    Measurable (su2PositiveInteriorWilsonHalfWeight n β) := by
  unfold su2PositiveInteriorWilsonHalfWeight
  apply (su2_positive_half_measurable n β).comp
  unfold su2AssembleReflectedPair fourDimensionalUnflattenLinks
    su2LiteralSectorAssemble su2TrivialBoundaryTemporalLinks
    su2TrivialPositiveInteriorLinks su2PositiveFieldReflectedToNegative
  fun_prop

/-- The named half weight is positive and at most one for nonnegative coupling. -/
theorem su2_positive_interior_wilson_half_weight_pos_le_one
    (n : ℕ) [NeZero n]
    (β : ℝ) (hβ : 0 ≤ β)
    (positive : SU2PositiveInteriorLinks n) :
    0 < su2PositiveInteriorWilsonHalfWeight n β positive ∧
      su2PositiveInteriorWilsonHalfWeight n β positive ≤ 1 := by
  unfold su2PositiveInteriorWilsonHalfWeight
  exact su2_positive_half_pos_le_one n β hβ _

/--
Final noncrossing compiler: RP of the averaged literal crossing kernel closes
the exact projected finite-Wilson OS2 proposition.
-/
theorem literal_su2_boundary_gauge_projection_rp_of_averaged_crossing_rp
    (hCross : LiteralSU2BoundaryAveragedCrossingRPExact) :
    LiteralSU2BoundaryGaugeProjectionRPExact := by
  intro n hn β hβ f hfMeas hfInt
  letI : NeZero n := hn
  let h : SU2PositiveInteriorLinks n → ℝ :=
    su2PositiveInteriorWilsonHalfWeight n β
  have hhMeas : Measurable h :=
    su2_positive_interior_wilson_half_weight_measurable n β
  have hhNonneg : ∀ x, 0 ≤ h x := by
    intro x
    exact (su2_positive_interior_wilson_half_weight_pos_le_one n β hβ x).1.le
  have hhLeOne : ∀ x, h x ≤ 1 := by
    intro x
    exact (su2_positive_interior_wilson_half_weight_pos_le_one n β hβ x).2
  have hgMeas : Measurable (fun x => f x * h x) :=
    hfMeas.mul hhMeas
  have hgInt : Integrable (fun x => f x * h x)
      (literalSU2PositiveInteriorHaar n) :=
    integrable_mul_of_measurable_zero_one
      f h hfInt hhMeas hhNonneg hhLeOne
  have hPos := hCross n hn β hβ (fun x => f x * h x) hgMeas hgInt
  have hPoint : ∀ left right : SU2PositiveInteriorLinks n,
      f left *
          literalSU2BoundaryGaugeProjectedWilsonKernel n β left right *
          f right =
        (f left * h left) *
          literalSU2BoundaryAveragedCrossingKernel n β left right *
          (f right * h right) := by
    intro left right
    rw [literal_su2_boundary_gauge_projected_kernel_half_weight_factorization]
    ring
  simp_rw [hPoint]
  exact hPos

end RequestProject.YangMills
