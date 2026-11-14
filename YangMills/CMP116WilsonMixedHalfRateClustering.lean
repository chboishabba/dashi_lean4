import Mathlib
import YangMills.ContinuumWilsonCovariance

open Filter MeasureTheory

/-!
# Mixed-pair Wilson half-rate clustering

Agda R551 is a genuinely mixed left/right statement: for arbitrary selected
Wilson observables `left` and `right`, the right observable is translated in
Euclidean time and the connected covariance obeys the source half-rate.

This Lean owner mirrors that stronger source shape.  The only continuum input
is weak convergence of the same cutoff laws; same-family and physical
support-distance/time identifications remain source-facing obligations when an
inhabitant is constructed.
-/

namespace RequestProject.YangMills

structure CMP116WilsonMixedHalfRateClusteringSource
    (Ω Obs : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  continuumLaw : ProbabilityMeasure Ω
  wilson : Obs → BoundedContinuousFunction Ω ℝ
  timeTranslate : Obs → ℕ → BoundedContinuousFunction Ω ℝ
  finiteHalfRate :
    ∀ (cutoff : ℕ) (left right : Obs) (time : ℕ),
      |probabilityCovariance (cutoffLaw cutoff)
          (wilson left) (timeTranslate right time)| ≤
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time

namespace CMP116WilsonMixedHalfRateClusteringSource

/-- The exact finite mixed-pair half-rate consumed by the continuum compiler. -/
theorem finite_mixed_half_rate
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (source : CMP116WilsonMixedHalfRateClusteringSource Ω Obs)
    (cutoff : ℕ) (left right : Obs) (time : ℕ) :
    |probabilityCovariance (source.cutoffLaw cutoff)
        (source.wilson left) (source.timeTranslate right time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
  source.finiteHalfRate cutoff left right time

/-- The same mixed Wilson estimate survives the weak continuum limit. -/
theorem continuum_mixed_half_rate
    {Ω Obs : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (source : CMP116WilsonMixedHalfRateClusteringSource Ω Obs)
    (hconv : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw))
    (left right : Obs) (time : ℕ) :
    |probabilityCovariance source.continuumLaw
        (source.wilson left) (source.timeTranslate right time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  exact probabilityCovariance_abs_le_of_weak_limit
    hconv
    (source.wilson left)
    (source.timeTranslate right time)
    ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time)
    (fun cutoff => source.finiteHalfRate cutoff left right time)

/-- Exact mixed R551 producer; no inhabitant is manufactured here. -/
def ProducerExists
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] : Prop :=
  Nonempty (CMP116WilsonMixedHalfRateClusteringSource Ω Obs)

end CMP116WilsonMixedHalfRateClusteringSource

end RequestProject.YangMills
