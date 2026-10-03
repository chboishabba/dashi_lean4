import Mathlib
import YangMills.YMClayMaxCut20261002
import YangMills.LiteralSU2BoundaryGaugeProjectionRP
import YangMills.CMP119PolymerReflectionAudit
import YangMills.CMP119LiteralResidualSourceDictionary
import YangMills.ProjectiveMarginalTightness

/-!
# YM A–D max-cut frontier, 2026-10-03

This file is a status/integration surface only.  It deliberately distinguishes
proved compilers from the physical/source producers still required to close the
corresponding block.

* A: the final projected finite-Wilson RP proposition is compiled from an
  explicit same-object projected-kernel producer; construction of that producer
  from the literal upper/lower half-path + boundary-Haar calculation remains the
  finite Wilson leaf.
* B: source polymers now have an executable four-way time-support classifier,
  and any negative crossing quadratic form is an explicit falsifier.  Actual
  E/R/B source dictionaries and PSD proofs remain physical leaves.
* C: an exact source dictionary now constructs the existing literal dyadic
  residual weld without duplicating localization arithmetic.  The dictionary
  fields remain to be populated from the selected CMP119 source.
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

/-- Block-B source placement is executable once actual support-touching data are supplied. -/
def ym_20261003_block_b_polymer_placement
    {Polymer : Type*}
    (dict : CMP119PolymerReflectionDictionary Polymer)
    (X : Polymer) : CMP119PolymerPlacement :=
  dict.placement X

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

/-- Block C: the selected source dictionary compiles directly to the existing dyadic weld. -/
def ym_20261003_block_c_weld
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    CMP119LiteralDyadicResidualWeld L :=
  dict.toDyadicResidualWeld

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
