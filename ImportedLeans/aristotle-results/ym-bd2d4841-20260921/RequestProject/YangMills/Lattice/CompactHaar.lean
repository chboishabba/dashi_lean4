/-
# Normalised Haar measure on a compact gauge group

The literal lattice Yang–Mills construction needs one genuine measure to start
from: the normalised Haar (probability) measure of the compact gauge group, and
its invariance under the two-sided translations `u ↦ a * u * b` that a gauge
transformation performs on a single link variable.

Everything here is proved, not assumed:

* `haarProb` — Haar measure normalised to total mass one, a probability measure
  on any compact Hausdorff topological group with the Borel σ-algebra;
* right invariance is derived from uniqueness of the Haar probability measure
  (the pushforward under a right translation is again a Haar probability
  measure), so no unimodularity input is taken on faith;
* `measurePreserving_mul_left_mul_right` — the two-sided translation of one link
  variable preserves `haarProb`.
-/
import Mathlib

namespace RequestProject.YangMills.Lattice

open MeasureTheory

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The normalised Haar measure of a compact group. -/
noncomputable def haarProb : Measure G := Measure.haarMeasure ⊤

instance haarProb.isProbabilityMeasure : IsProbabilityMeasure (haarProb G) :=
  ⟨by
    simpa [haarProb] using
      Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))⟩

instance haarProb.isMulLeftInvariant : (haarProb G).IsMulLeftInvariant := by
  unfold haarProb; infer_instance

instance haarProb.isHaarMeasure : (haarProb G).IsHaarMeasure := by
  unfold haarProb; infer_instance

instance haarProb.isMulRightInvariant : (haarProb G).IsMulRightInvariant := by
  constructor
  intro b
  haveI : IsProbabilityMeasure (Measure.map (fun u : G => u * b) (haarProb G)) := by
    constructor
    rw [Measure.map_apply ((continuous_mul_right b).measurable) MeasurableSet.univ]
    simp
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable {G}

/-- A two-sided translation of a single link variable preserves the normalised
Haar measure.  This is the measure-theoretic content of gauge covariance of one
link. -/
theorem measurePreserving_mul_left_mul_right (a b : G) :
    MeasurePreserving (fun u : G => a * u * b) (haarProb G) (haarProb G) :=
  (measurePreserving_mul_right (haarProb G) b).comp
    (measurePreserving_mul_left (haarProb G) a)

end RequestProject.YangMills.Lattice
