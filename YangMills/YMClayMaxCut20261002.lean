import Mathlib
import YangMills.LiteralSU2HalfIndexBijection
import YangMills.LiteralSU2WilsonOSFactorization
import YangMills.LiteralSU2CompactQuaternionHaar
import YangMills.LiteralSU2LinkHaarReflection
import YangMills.LiteralSU2LinkSectorHaarSplit
import YangMills.LiteralSU2CrossingIntegralRP
import YangMills.LiteralSU2FixedBoundaryNoGo
import YangMills.LiteralSU2BoundaryGaugeProjectionCut
import YangMills.LiteralSU2BoundaryGaugeProjectionSymmetry
import YangMills.CMP119ResidualReflectionCut
import YangMills.CMP119LiteralCompleteCrossingRP
import YangMills.CMP119LiteralDyadicResidualWeld
import YangMills.CMP119NativeDyadicMomentBound
import YangMills.FourDimensionalNativeHaarReflectionMaxCut
import YangMills.FourDimensionalNativeHaarProductWeld
import YangMills.FourDimensionalFlatHaarReflectionIndex
import YangMills.FourDimensionalNativeHaarReflectionTransport
import YangMills.ScaleSensitiveWilsonMomentMaxCut

/-!
# YM max-cut frontier, 2026-10-03

The selected literal finite Wilson lane now owns the quaternion Haar carrier,
full-link product Haar, reflection invariance, the positive/boundary/negative
sector product split, continuous integral RP of the abstract exponential
crossing kernel, and exact reflection symmetry of the boundary-Haar projected
physical Wilson kernel.

A fixed-boundary Q8 witness shows that conditional boundary PSD is false.
Therefore the exact remaining finite-Wilson leaf is no longer symmetry or Haar
transport: it is the nonnegative quadratic-form theorem for the symmetric
boundary-gauge-projected physical kernel,
`LiteralSU2BoundaryGaugeProjectionRPExact`.

CMP119's configuration-independent vacuum factor is a reflected-half rank-one
factor, leaving exactly E, R-operation, and B as nontrivial physical RP leaves.
The residual/moment compilers remain downstream of the same-object localized
residual weld and a genuine global compact-containment/coercive estimate.
-/

namespace RequestProject.YangMills

/-- Generic compact-group A1: native whole-link Haar is finite product Haar. -/
theorem ym_block_a1_native_equals_product_haar_closed
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    (((fourDimensionalNativeLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)))
    =
    (((fourDimensionalProductLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)) :=
  four_dimensional_native_haar_eq_product_haar_closed G L

/-- Generic compact-group A2: selected reflection preserves native Haar. -/
theorem ym_block_a2_native_haar_reflection_closed
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    FourDimensionalNativeHaarReflectionInvariant G n :=
  four_dimensional_native_haar_reflection_invariant_closed G n

/-- Literal selected reflection preserves the actual quaternion product Haar. -/
theorem ym_block_a_literal_link_haar_reflection
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@su2EvenTimeReflectLinks n)
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))))
    =
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))) :=
  literal_su2_link_haar_reflection_invariant n

/-- Literal Haar splits exactly into positive / boundary / negative factors. -/
theorem ym_block_a_literal_sector_haar_split
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (su2LiteralSectorAssemble n)
      (literalSU2LinkSectorHaar n)
    =
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :=
  literal_su2_link_sector_haar_split n

/-- The abstract complete crossing kernel is RP after continuous integration. -/
theorem ym_block_a_crossing_kernel_integral_rp
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.Measure (SU2CrossingBoundary P))
    [MeasureTheory.SFinite μ]
    (f : SU2CrossingBoundary P → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ left, ∫ right,
      f left * su2WilsonCrossingPlaneKernel crossings β left right * f right ∂μ ∂μ :=
  su2_wilson_crossing_plane_integral_rp
    crossings β hβ μ f hfMeas hfInt

/-- Fixed temporal-boundary conditioning is formally ruled out. -/
theorem ym_block_a_fixed_boundary_route_fails :
    ¬ (0 ≤ fixedBoundaryFirstOrderTwoPointQuadratic
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne) :=
  fixed_boundary_first_order_not_rp

/-- The surviving projected physical Wilson kernel is now theorem-bearing symmetric. -/
theorem ym_block_a_projected_wilson_kernel_symmetric
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      literalSU2BoundaryGaugeProjectedWilsonKernel n β right left :=
  literal_su2_boundary_gauge_projected_kernel_symmetric n β left right

/-- Exact surviving pure-Wilson positivity proposition. -/
abbrev LiteralSU2BoundaryGaugeProjectionRP :=
  LiteralSU2BoundaryGaugeProjectionRPExact

/-- The literal SU(2) Wilson half-action identity is theorem-bearing. -/
theorem ym_maxcut_literal_wilson_half_closed
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct
        (su2EvenTimePositivePlaquettes n)
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2EvenTimeNegativePlaquettes n)
        links β :=
  su2_negative_half_eq_reflected_positive_half n links β

/-- Bounded average plaquette cost is a negative control, not the D producer. -/
theorem ym_maxcut_average_plaquette_cost_is_uniformly_bounded
    (L : ℕ) [NeZero L]
    (hCard : (su2FourDimensionalPlaquettes L).card ≠ 0)
    (links : SU2TorusLinks L) :
    su2AveragePlaquetteCost L links ≤ 2 :=
  (su2_average_plaquette_cost_bounds L hCard links).2

/-- Constant source vacuum is a reflected-half factor. -/
theorem ym_maxcut_constant_vacuum_is_reflected_half
    {ι : Type*} [Fintype ι]
    (vacuumEnergy : ℝ) :
    (cmp119ConstantVacuumCertificate
      (ι := ι) vacuumEnergy).placement =
      CMP119ReflectionPlacement.reflectedHalf := by
  rfl

/-- Only E, R_op and B need nontrivial residual reflection certificates. -/
theorem ym_maxcut_three_sector_residual_rp
    {ι : Type*} [Fintype ι]
    (regularCert rCert boundaryCert : CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          regularCert.kernel i j *
          rCert.kernel i j *
          boundaryCert.kernel i j *
          Real.exp (-vacuumEnergy)) test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j * rCert.kernel i j *
          boundaryCert.kernel i j * Real.exp (-vacuumEnergy)) rfl
  intro test
  exact cmp119_complete_residual_kernel_rp cut test

/-- Wilson RP times the three selected residual certificates gives complete finite RP. -/
theorem ym_maxcut_wilson_three_sector_complete_rp
    {ι : Type*} [Fintype ι]
    (wilsonKernel : ι → ι → ℝ)
    (hWilsonSymm : ∀ i j, wilsonKernel i j = wilsonKernel j i)
    (hWilsonRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic wilsonKernel test)
    (regularCert rCert boundaryCert : CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          wilsonKernel i j *
          (regularCert.kernel i j * rCert.kernel i j *
            boundaryCert.kernel i j * Real.exp (-vacuumEnergy))) test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j * rCert.kernel i j *
          boundaryCert.kernel i j * Real.exp (-vacuumEnergy)) rfl
  simpa only [mul_assoc] using
    (cmp119_wilson_mul_complete_residual_rp
      wilsonKernel hWilsonSymm hWilsonRP cut)

/-- Literal multi-plaquette specialization of the complete finite RP compiler. -/
theorem ym_maxcut_literal_wilson_three_sector_complete_rp
    {P ι : Type*} [DecidableEq P] [Fintype ι]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (boundary : ι → SU2CrossingBoundary P)
    (regularCert rCert boundaryCert : CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          su2WilsonCrossingPlaneKernel crossings β (boundary i) (boundary j) *
          (regularCert.kernel i j * rCert.kernel i j *
            boundaryCert.kernel i j * Real.exp (-vacuumEnergy))) test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j * rCert.kernel i j *
          boundaryCert.kernel i j * Real.exp (-vacuumEnergy)) rfl
  exact cmp119_literal_wilson_crossing_mul_residual_rp
    crossings β hβ boundary cut

/-- Exact source-facing residual leaf set after the vacuum identification. -/
def ymMaxCutResidualCertificateLeaves : Finset CMP119ResidualSector :=
  { CMP119ResidualSector.regularE
  , CMP119ResidualSector.rOperation
  , CMP119ResidualSector.boundaryB }

theorem ym_maxcut_vacuum_not_in_residual_certificate_leaves :
    CMP119ResidualSector.vacuumV ∉ ymMaxCutResidualCertificateLeaves := by
  simp [ymMaxCutResidualCertificateLeaves]

end RequestProject.YangMills
