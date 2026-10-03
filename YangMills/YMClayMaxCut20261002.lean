import Mathlib
import YangMills.LiteralSU2HalfIndexBijection
import YangMills.LiteralSU2WilsonOSFactorization
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

The finite Wilson geometry and native compact-group Haar reflection transport
are now source-written.  The surviving Block-A theorem is the actual
Wilson-weighted OS2 integral/Fubini assembly on the selected positive-time
cylinder algebra.

CMP119's configuration-independent vacuum factor is a reflected-half rank-one
factor.  Therefore complete residual RP still has exactly three physical
source leaves: regular E, R-operation, and boundary B.

The dyadic residual and native moment-transfer compilers remain downstream of
one same-object localized-residual weld and one genuinely global compactness /
coercive estimate.
-/

namespace RequestProject.YangMills

/-- Block A1 is theorem-bearing: native whole-link Haar is the literal product Haar. -/
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

/-- Block A2 is theorem-bearing: the selected reflection preserves native whole-link Haar. -/
theorem ym_block_a2_native_haar_reflection_closed
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    FourDimensionalNativeHaarReflectionInvariant G n :=
  four_dimensional_native_haar_reflection_invariant_closed G n

/-- The literal SU(2) Wilson half-action identity is no longer a hypothesis. -/
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

/--
The easy cutoff-uniform Wilson observable remains a negative control only: it
is bounded and therefore not the missing continuum-coercive producer.
-/
theorem ym_maxcut_average_plaquette_cost_is_uniformly_bounded
    (L : ℕ) [NeZero L]
    (hCard : (su2FourDimensionalPlaquettes L).card ≠ 0)
    (links : SU2TorusLinks L) :
    su2AveragePlaquetteCost L links ≤ 2 :=
  (su2_average_plaquette_cost_bounds L hCard links).2

/-- The source-native constant vacuum factor is a reflected-half factor. -/
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
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          regularCert.kernel i j *
          rCert.kernel i j *
          boundaryCert.kernel i j *
          Real.exp (-vacuumEnergy))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
  intro test
  exact cmp119_complete_residual_kernel_rp cut test

/-- Wilson RP times the three selected residual certificates gives complete finite RP. -/
theorem ym_maxcut_wilson_three_sector_complete_rp
    {ι : Type*} [Fintype ι]
    (wilsonKernel : ι → ι → ℝ)
    (hWilsonSymm : ∀ i j, wilsonKernel i j = wilsonKernel j i)
    (hWilsonRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic wilsonKernel test)
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          wilsonKernel i j *
          (regularCert.kernel i j *
            rCert.kernel i j *
            boundaryCert.kernel i j *
            Real.exp (-vacuumEnergy)))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
  simpa only [mul_assoc] using
    (cmp119_wilson_mul_complete_residual_rp
      wilsonKernel hWilsonSymm hWilsonRP cut)

/-- Literal multi-plaquette Wilson specialization: only E, R_op and B remain physical. -/
theorem ym_maxcut_literal_wilson_three_sector_complete_rp
    {P ι : Type*} [DecidableEq P] [Fintype ι]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (boundary : ι → SU2CrossingBoundary P)
    (regularCert rCert boundaryCert :
      CMP119SectorReflectionCertificate ι)
    (vacuumEnergy : ℝ) :
    ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic
        (fun i j =>
          su2WilsonCrossingPlaneKernel crossings β
            (boundary i) (boundary j) *
          (regularCert.kernel i j *
            rCert.kernel i j *
            boundaryCert.kernel i j *
            Real.exp (-vacuumEnergy)))
        test := by
  let cut : CMP119ResidualReflectionCut ι :=
    cmp119ResidualCutWithConstantVacuum
      regularCert rCert boundaryCert vacuumEnergy
      (fun i j =>
        regularCert.kernel i j *
        rCert.kernel i j *
        boundaryCert.kernel i j *
        Real.exp (-vacuumEnergy))
      rfl
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
