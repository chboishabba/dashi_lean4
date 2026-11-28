import Mathlib
import YangMills.YMClayMaxCut20261003ABCD
import YangMills.SequentialProjectiveConditionalKernel
import YangMills.CanonicalMarginalMomentSource
import YangMills.LiteralSU2BoundaryProjectedKernelPlaneSplit
import YangMills.LiteralSU2CrossingGaugeSumReadback
import YangMills.LiteralSU2CrossingGaugePlaneLocality

/-!
# D3-extension-closed and A-readback-compressed max-cut surface

This file records the stronger frontier after two independent compressions.

## D3

For any consistent `RealSequentialProjectiveFamily`:

1. each one-step regular conditional distribution exists as a Markov kernel;
2. projective consistency gives the exact selected one-step factorization;
3. Ionescu--Tulcea constructs an actual probability measure on `ℕ → ℝ`;
4. every selected prefix is recovered exactly;
5. the global law is unique from those prefixes.

Thus generic D3 extension no longer requires a separately proved cylinder
sigma-subadditivity theorem on the real sequential route.  The remaining D3
work is physical/source-facing: choose the actual selected observable family
and prove uniform coercive/tail estimates. `RealCanonicalMarginalMomentSource`
places those estimates on the SAME cutoff law and transports them to marginal
tightness by pushforward identity.

## A

The actual boundary-projected Wilson kernel now has an exact two-plane Haar
readback.  The literal upper/lower crossing plaquettes have been classified on
the physical link carrier, their half paths read back to the exact
boundary-gauged positive-copy edges, and the complete crossing trace/kernel is
rewritten as upper plus lower gauged sums.  Those two sums are theorem-bearingly
local to the independent upper and lower boundary-plane fields.

Consequently the remaining A leaf is no longer lattice geometry or source
identification.  It is the final positivity/Fubini calculation for the explicit
two-plane projected kernel, together with the noncrossing-half boundary
independence needed to pull the positive half factors outside that average.

Nothing here claims that final A positivity, physical CMP marginal estimates,
complete-action CMP119 RP, continuum OS reconstruction, clustering, spectral
completeness, or a mass gap before their named source producers are proved.
-/

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- Generic D3 extension is an actual countable probability measure. -/
noncomputable def ym_20261003_d3_ext_measure
    (sequence : RealSequentialProjectiveFamily) :
    Measure (ℕ → ℝ) :=
  sequence.conditionalGlobalMeasure

instance ym_20261003_d3_ext_measure_probability
    (sequence : RealSequentialProjectiveFamily) :
    IsProbabilityMeasure (ym_20261003_d3_ext_measure sequence) := by
  unfold ym_20261003_d3_ext_measure
  infer_instance

/-- Exact recovery of every selected sequential prefix. -/
theorem ym_20261003_d3_ext_prefix
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) :
    (ym_20261003_d3_ext_measure sequence).map (frestrictLe n) =
      (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) := by
  exact sequence.conditionalGlobalMeasure_prefix n

/-- D3.6: the constructed global law is unique from its complete prefix family. -/
theorem ym_20261003_d3_ext_unique
    (sequence : RealSequentialProjectiveFamily)
    (ν : Measure (ℕ → ℝ))
    (hν :
      ∀ n : ℕ,
        ν.map (frestrictLe n) =
          (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    ν = ym_20261003_d3_ext_measure sequence := by
  exact sequence.conditionalGlobalMeasure_unique ν hν

/-- Same-source physical moment estimates feed D3.2 directly. -/
def ym_20261003_d3_phys_moment_compiler
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω) :
    RealMarginalMomentTightnessProducer :=
  source.toMomentTightnessProducer

/-- Same-source physical moment estimates therefore produce tight finite marginals. -/
theorem ym_20261003_d3_phys_marginal_tight
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω)
    (m : ℕ) :
    IsTightMeasureSet
      {ν : Measure (Fin m → ℝ) |
        ∃ p ∈ Set.range (source.family.marginal m),
          ((p : ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)) = ν} :=
  source.marginal_tight m

/--
The remaining D3 Clay-facing producer: instantiate the canonical selected
observable family and its native cutoff-law coercive moments.
-/
def YM20261003D3PhysicalMomentProducerExists
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω) : Prop :=
  ∃ source : RealCanonicalMarginalMomentSource Ω,
    source.family = family

/-- Exact A readback onto the independent upper/lower boundary-plane carrier. -/
theorem ym_20261003_block_a_projected_kernel_plane_split
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      ∫ planes : SU2BoundaryPlaneFields n,
        literalSU2ReflectedPairWilsonDensity n β left
          (su2BoundaryTemporalPlaneAssemble n planes) right
        ∂(literalSU2BoundaryPlaneHaar n) :=
  literal_su2_boundary_projected_kernel_plane_split n β left right

/-- Exact A crossing kernel readback after the physical half-path calculation. -/
theorem ym_20261003_block_a_crossing_kernel_gauge_readback
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2WilsonCrossingPlaneKernel
      (su2EvenTimeCrossingPlaquettes n) β
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right)) =
    Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
      Real.exp (β *
        (su2UpperGaugedCrossingTraceSum n left right boundary +
         su2LowerGaugedCrossingTraceSum n left right boundary)) :=
  su2_literal_crossing_kernel_gauge_sum_readback n β left right boundary

/-- Upper crossing dependence reads only the upper boundary-plane coordinate. -/
theorem ym_20261003_block_a_upper_plane_locality
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2UpperGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2UpperPlaneGaugedCrossingTraceSum n left right planes.1 :=
  su2_upper_gauged_crossing_sum_plane_readback n left right planes

/-- Lower crossing dependence reads only the lower boundary-plane coordinate. -/
theorem ym_20261003_block_a_lower_plane_locality
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2LowerGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2LowerPlaneGaugedCrossingTraceSum n left right planes.2 :=
  su2_lower_gauged_crossing_sum_plane_readback n left right planes

end RequestProject.YangMills
