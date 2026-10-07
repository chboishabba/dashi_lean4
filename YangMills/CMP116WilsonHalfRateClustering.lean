import Mathlib
import YangMills.ContinuumWilsonCovariance

/-!
# Source-faithful Wilson half-rate clustering transport

Agda R491/R551 use the selected Wilson pair directly and prove the finite bound

  |Cov(W_L,W_R)| ≤ 1/4 * (1/2)^t

once physical support distance has been identified with Euclidean time.  This
Lean owner records exactly that source shape and transports it through the same
weak continuum limit.  It deliberately does not reintroduce the obsolete
printed-J presentation.
-/

open Filter MeasureTheory

namespace RequestProject.YangMills

structure CMP116WilsonHalfRateClusteringSource
    (Ω Obs : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  continuumLaw : ProbabilityMeasure Ω
  left right : Obs → ℕ → BoundedContinuousFunction Ω ℝ
  finiteHalfRate :
    ∀ (cutoff : ℕ) (obs : Obs) (time : ℕ),
      |probabilityCovariance (cutoffLaw cutoff)
          (left obs time) (right obs time)| ≤
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time

namespace CMP116WilsonHalfRateClusteringSource

/-- The exact source-facing finite R491/R551 half-rate bound. -/
theorem finite_half_rate
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (source : CMP116WilsonHalfRateClusteringSource Ω Obs)
    (cutoff : ℕ) (obs : Obs) (time : ℕ) :
    |probabilityCovariance (source.cutoffLaw cutoff)
        (source.left obs time) (source.right obs time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time :=
  source.finiteHalfRate cutoff obs time

/-- The same Wilson half-rate estimate survives the weak continuum limit. -/
theorem continuum_half_rate
    {Ω Obs : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (source : CMP116WilsonHalfRateClusteringSource Ω Obs)
    (hconv : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw))
    (obs : Obs) (time : ℕ) :
    |probabilityCovariance source.continuumLaw
        (source.left obs time) (source.right obs time)| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  exact probabilityCovariance_abs_le_of_weak_limit
    hconv
    (source.left obs time)
    (source.right obs time)
    ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time)
    (fun cutoff => source.finiteHalfRate cutoff obs time)

/-- Exact F1 source producer after removing the obsolete printed-J seam. -/
def ProducerExists
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] : Prop :=
  Nonempty (CMP116WilsonHalfRateClusteringSource Ω Obs)

end CMP116WilsonHalfRateClusteringSource

end RequestProject.YangMills
