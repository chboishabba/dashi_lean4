import Mathlib
import YangMills.WilsonCylinderCutoffLaw
import YangMills.WilsonDF2UnifiedSource

/-!
# Canonical D source directly on the Wilson-cylinder carrier

The raw finite Yang--Mills cutoff laws are first pushed to the compact cylinder
state.  On that carrier, the coordinate projections are continuous and jointly
injective by construction.  The existing bounded determining-family theorem
therefore yields the exact D source without coercive moments or a later
pullback/support theorem.
-/

namespace RequestProject.YangMills

/--
The selected finite cutoff laws plus measurable Wilson coordinates produce the
bounded determining source directly on the canonical cylinder compactification.
-/
noncomputable def wilsonCylinderDeterminingSource
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  (wilsonCylinderDF2Source raw).determiningSource
    (wilsonCylinderCutoffLaw raw hMeas cutoffLaw)

/-- The canonical projective/global coordinate law is a probability measure. -/
noncomputable def wilsonCylinderGlobalCoordinateMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    Measure (ℕ → ℝ) :=
  (wilsonCylinderDeterminingSource raw hMeas cutoffLaw).globalCoordinateMeasure

instance wilsonCylinderGlobalCoordinateMeasure_isProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    IsProbabilityMeasure
      (wilsonCylinderGlobalCoordinateMeasure raw hMeas cutoffLaw) := by
  unfold wilsonCylinderGlobalCoordinateMeasure
  infer_instance

end RequestProject.YangMills
