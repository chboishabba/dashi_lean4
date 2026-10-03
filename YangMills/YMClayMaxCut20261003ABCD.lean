import Mathlib
import YangMills.YMClayMaxCut20261002
import YangMills.LiteralSU2BoundaryGaugeProjectionRP
import YangMills.LiteralSU2ReflectedPairOSFactorization
import YangMills.CMP119PolymerReflectionAudit
import YangMills.CMP119PeriodicPolymerReflectionGeometry
import YangMills.CMP119PeriodicPolymerSectorSplit
import YangMills.CMP119RegularComponentPolymerDictionary
import YangMills.CMP119LiteralResidualSourceDictionary
import YangMills.CanonicalProjectiveMarginals
import YangMills.ProjectiveMarginalMomentTightness
import YangMills.ProjectiveMarginalDiagonalTightness
import YangMills.ProjectiveMarginalLimitConsistency
import YangMills.ProjectiveCylinderMeasure
import YangMills.SequentialProjectiveCylinderMeasure

/-!
# YM A–D3 max-cut frontier, 2026-10-03

This file is a status/integration surface only. It distinguishes proved
compilers from physical/source producers still required to close a block.

* A: the density under boundary-Haar projection is exactly the SAME literal
  positive-half/reflected-half/crossing-kernel OS factorization. The remaining
  physical leaf is the upper/lower half-path boundary-Haar projection PSD
  calculation.
* B: finite source polymers live on the actual periodic 4D link-support carrier,
  have an executable + / - / crossing / empty classifier, and sector sums split
  exactly by placement. Negative crossing quadratic forms formally falsify the
  route. E/R/B reflected-half identities and crossing PSD remain source leaves.
* C: the regular `component ↦ periodic polymer` seam and full E/R/B/V additive
  source dictionary are explicit and compile directly to the existing dyadic
  residual weld. No additional localization machinery is needed; the selected
  CMP119 equalities themselves remain to be instantiated.
* D3.1: finite marginals now come from ONE cutoff-law family by selected maps.
* D3.2: per-marginal coercive moment bounds compile to genuine tightness.
* D3.3: coordinatewise tightness yields ONE simultaneous subsequence by
  Tychonoff compactness of the product of compact marginal closures.
* D3.4: finite-cutoff prefix consistency passes automatically to simultaneous
  weak limits by the continuous mapping theorem.
* D3.5: for a consistent sequential prefix family, mathlib's `inducedFamily`
  gives an all-finset projective family; sigma-subadditivity of its canonical
  cylinder content then produces an ACTUAL global probability measure by
  Carathéodory with exactly those finite marginals.
* D3.6: a global measure with those complete finite marginals is unique by
  projective-limit uniqueness.

Thus the generic D3 construction is no longer an opaque projective-limit
existence postulate. The remaining analytic/source inputs are the actual CMP
marginal maps and uniform moment/tail estimates, plus sigma-subadditivity of the
resulting projective cylinder content (or an equivalent Ionescu--Tulcea/kernel
producer).

Nothing here claims continuum OS reconstruction, clustering, spectral
completeness, or a mass gap.
-/

namespace RequestProject.YangMills

/-- Block A is closed exactly once the literal projected-kernel producer exists. -/
theorem ym_20261003_block_a_compiler
    (hProducer : LiteralSU2BoundaryGaugeProjectionProducerExists) :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_of_exists_producer hProducer

abbrev YM20261003BlockAProducer :=
  LiteralSU2BoundaryGaugeProjectionProducerExists

/-- Same-object factorization of the exact density integrated by Block A. -/
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
  cmp119_crossing_kernel_falsified_by_negative_quadratic kernel test hneg

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

/-- Block C compiles the selected source dictionary directly to the dyadic weld. -/
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

/-- D3.2: physical marginal moment estimates compile to tightness. -/
def ym_20261003_block_d3_moment_to_tightness
    (producer : RealMarginalMomentTightnessProducer) :
    RealProjectiveMarginalTightnessProducer :=
  producer.toTightnessProducer

/-- D3.3: one simultaneous subsequence follows from all marginal tightness bounds. -/
theorem ym_20261003_block_d3_simultaneous_subsequence
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        MeasureTheory.IsTightMeasureSet
          {ν : MeasureTheory.Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : MeasureTheory.ProbabilityMeasure (Fin m → ℝ)) :
                MeasureTheory.Measure (Fin m → ℝ)) = ν}) :
    Nonempty (RealSimultaneousMarginalSubsequence family) :=
  exists_simultaneous_marginal_subsequence_of_tight family hTight

/-- D3.3+D3.4: the simultaneous limits are canonically projectively consistent. -/
theorem ym_20261003_block_d3_simultaneous_consistent_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        MeasureTheory.IsTightMeasureSet
          {ν : MeasureTheory.Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : MeasureTheory.ProbabilityMeasure (Fin m → ℝ)) :
                MeasureTheory.Measure (Fin m → ℝ)) = ν}) :
    ∃ diag : RealSimultaneousMarginalSubsequence family,
      ∀ (m n : ℕ) (h : m ≤ n),
        realFinPrefixMap m n h (diag.limit n) = diag.limit m :=
  exists_simultaneous_consistent_marginal_limits_of_tight family hTight

/-- D3.5: a cylinder-extension producer constructs a genuine continuum law. -/
noncomputable def ym_20261003_block_d3_global_probability
    (producer : RealSequentialCylinderExtensionProducer) :
    MeasureTheory.ProbabilityMeasure (ℕ → ℝ) :=
  producer.globalProbabilityMeasure

/-- D3.5 exact finite-prefix recovery. -/
theorem ym_20261003_block_d3_global_prefix
    (producer : RealSequentialCylinderExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (Preorder.frestrictLe n) =
      (producer.sequence.marginal n :
        MeasureTheory.Measure ((i : Set.Iic n) → ℝ)) :=
  producer.globalMeasure_prefix n

/-- The narrowed D3.5 analytic wall: sigma-subadditivity of the canonical cylinder content. -/
def YM20261003BlockD3CylinderSigmaSubadditivity : Prop :=
  ∀ sequence : RealSequentialProjectiveFamily,
    (MeasureTheory.projectiveFamilyContent
      sequence.toProbabilityProjectiveFamily.projective).IsSigmaSubadditive

end RequestProject.YangMills
