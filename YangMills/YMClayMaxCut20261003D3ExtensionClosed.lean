import Mathlib
import YangMills.YMClayMaxCut20261003ABCD
import YangMills.SequentialProjectiveConditionalKernel
import YangMills.CanonicalMarginalMomentSource

/-!
# D3 extension-closed max-cut surface

This file records the stronger frontier after replacing the generic cylinder
sigma-subadditivity obligation with the regular-conditional/Ionescu--Tulcea
route available for real sequential prefixes.

For any consistent `RealSequentialProjectiveFamily`:

1. each one-step regular conditional distribution exists as a Markov kernel;
2. projective consistency gives the exact selected one-step factorization;
3. Ionescu--Tulcea constructs an actual probability measure on `ℕ → ℝ`;
4. every selected prefix is recovered exactly;
5. the global law is unique from those prefixes.

Thus the remaining D3 work is no longer generic measure extension.  It is the
physical/source side: choose the actual selected observable family and prove
uniform coercive/tail estimates.  `RealCanonicalMarginalMomentSource` exposes
that source estimate on the SAME cutoff law and transports it to the marginal
moment compiler by pushforward identity.
-/

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- Generic D3 extension is now an actual countable probability measure. -/
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

end RequestProject.YangMills
