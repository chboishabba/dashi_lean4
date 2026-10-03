import Mathlib
import YangMills.YMClayMaxCut20261002
import YangMills.LiteralSU2BoundaryGaugeProjectionRP
import YangMills.LiteralSU2ReflectedPairOSFactorization
import YangMills.CMP119PolymerReflectionAudit
import YangMills.CMP119PeriodicPolymerReflectionGeometry
import YangMills.CMP119PeriodicPolymerSectorSplit
import YangMills.CMP119RegularComponentPolymerDictionary
import YangMills.CMP119LiteralResidualSourceDictionary
import YangMills.ProjectiveMarginalTightness

/-!
# YM A–D max-cut frontier, 2026-10-03

This file is a status/integration surface only.  It deliberately distinguishes
proved compilers from the physical/source producers still required to close the
corresponding block.

* A: the density under the boundary-Haar projection is now exactly the SAME
  literal positive-half/reflected-half/crossing-kernel OS factorization.  The
  final projected finite-Wilson RP proposition is compiled from an explicit
  same-object projected-kernel producer; the upper/lower half-path Haar
  projection positivity remains the physical leaf.
* B: finite source polymers now live on the actual periodic 4D link-support
  carrier, have an executable + / - / crossing / empty classifier, and sector
  sums split exactly by that placement.  A negative crossing quadratic form is
  an explicit falsifier.  E/R/B reflected-half identities and crossing PSD
  proofs remain physical leaves.
* C: the regular `component ↦ periodic polymer` seam and the full E/R/B/V
  additive source dictionary are explicit.  The latter constructs the existing
  literal dyadic residual weld without duplicating localization arithmetic.
  The source equalities still have to be populated from selected CMP119 data.
* D3: every finite real marginal can be supplied with actual tightness and then
  has a Prokhorov weak subsequence.  Diagonal compatibility and the global
  countable-product/projective-limit measure remain explicit obligations.

Nothing here claims continuum OS reconstruction, clustering, spectral
completeness, or a mass gap.
-/

namespace RequestProject.YangMills

/-- Block A is closed exactly once the literal projected-kernel producer exists. -/
theorem ym_20261003_block_a_compiler
    (hProducer : LiteralSU2BoundaryGaugeProjectionProducerExists) :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_of_exists_producer hProducer

/-- The exact still-open Block-A physical producer proposition. -/
abbrev YM20261003BlockAProducer :=
  LiteralSU2BoundaryGaugeProjectionProducerExists

/-- Same-object factorization of the exact density integrated by the Block-A projection. -/
theorem ym_20261003_block_a_reflected_pair_factorization
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    literalSU2ReflectedPairWilsonDensity n β left boundary right =
      su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary right) β *
      su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks
          (su2AssembleReflectedPair n left boundary right)) β *
      su2WilsonCrossingPlaneKernel
        (su2EvenTimeCrossingPlaquettes n) β
        (su2LiteralCrossingFirstBoundary
          (su2AssembleReflectedPair n left boundary right))
        (su2LiteralCrossingSecondBoundary
          (su2AssembleReflectedPair n left boundary right)) :=
  literal_su2_reflected_pair_os_factorization n β left boundary right

/-- Generic Block-B placement API. -/
def ym_20261003_block_b_polymer_placement
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) : CMP119PolymerPlacement :=
  dict.placement X

/-- Concrete Block-B placement on the literal periodic 4D link-support carrier. -/
noncomputable def ym_20261003_block_b_periodic_polymer_placement
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) : CMP119PolymerPlacement :=
  cmp119PeriodicPolymerPlacement n X

/-- A negative quadratic witness on an actual crossing kernel falsifies that RP leaf. -/
theorem ym_20261003_block_b_crossing_falsifier
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (test : ι → ℝ)
    (hneg : indexedReflectionQuadratic kernel test < 0) :
    ¬ (∀ f : ι → ℝ, 0 ≤ indexedReflectionQuadratic kernel f) :=
  cmp119_crossing_kernel_falsified_by_negative_quadratic
    kernel test hneg

/-- The three non-vacuum source sectors that still require real certificates. -/
abbrev YM20261003BlockBLeaves :=
  cmp119NontrivialReflectionSectors

/-- Exact finite source-sector split on the periodic polymer carrier. -/
theorem ym_20261003_block_b_sector_split
    (n : ℕ) [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n)
    (links : SU2TorusLinks (2 * n)) :
    source.action links =
      source.placementAction CMP119PolymerPlacement.positive links +
      source.placementAction CMP119PolymerPlacement.negative links +
      source.placementAction CMP119PolymerPlacement.crossing links +
      source.placementAction CMP119PolymerPlacement.empty links :=
  source.action_eq_sum_placements links

/-- Block C: the selected source dictionary compiles directly to the existing dyadic weld. -/
def ym_20261003_block_c_weld
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    CMP119LiteralDyadicResidualWeld L :=
  dict.toDyadicResidualWeld

/-- The regular-E `component ↦ X_c` seam is represented explicitly. -/
def ym_20261003_block_c_regular_component_polymer
    {L : ℕ}
    (dict : CMP119RegularComponentPolymerDictionary L)
    (c : dict.Component) : Finset (FourDimensionalLinkIndex L) :=
  dict.componentPolymer c

/-- Block C inherits the existing literal residual oscillation theorem directly. -/
theorem ym_20261003_block_c_pairwise_oscillation
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L)
    (x y : SU2TorusLinks L) :
    |su2FullResidual
        dict.literalRegular dict.literalROperation
        dict.literalBoundary dict.literalVacuum x -
      su2FullResidual
        dict.literalRegular dict.literalROperation
        dict.literalBoundary dict.literalVacuum y| ≤
      cmp119DyadicTailMajorant dict.depth :=
  dict.literalResidualPairwiseOscillation x y

/-- Block D3 finite-marginal output: a genuine weak subsequence for each fixed marginal. -/
theorem ym_20261003_block_d3_each_marginal_subsequence
    (producer : RealProjectiveMarginalTightnessProducer) :
    ∀ m : ℕ,
      ∃ μ∞ : MeasureTheory.ProbabilityMeasure (Fin m → ℝ),
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Filter.Tendsto (producer.marginal m ∘ φ)
            Filter.atTop (𝓝 μ∞) :=
  exists_each_real_finite_marginal_weak_subsequence producer

/-- The global countable-product/projective-limit theorem remains explicit. -/
abbrev YM20261003BlockD3GlobalObligation :=
  RealProjectiveLimitExistenceObligation

end RequestProject.YangMills
