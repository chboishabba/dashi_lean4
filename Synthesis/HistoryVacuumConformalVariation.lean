import Mathlib

namespace Synthesis.HistoryVacuumConformalVariation

/-- Four-dimensional conformal volume factor for g ↦ e^{2s} g. -/
def conformalVolume (s : ℝ) : ℝ := Real.exp (4 * s)

/-- Vacuum contribution to the effective action for a positive amplitude λ.
The sign convention matches T_ab = -λ g_ab on the source side. -/
def vacuumAction (λ s : ℝ) : ℝ := -λ * conformalVolume s

/-- The conformal volume derivative is 4e^{4s}. -/
theorem conformalVolume_hasDerivAt (s : ℝ) :
    HasDerivAt conformalVolume (4 * Real.exp (4 * s)) s := by
  have hlin : HasDerivAt (fun x : ℝ => 4 * x) 4 s := by
    simpa using (hasDerivAt_id s).const_mul 4
  simpa [conformalVolume, mul_assoc, mul_left_comm, mul_comm] using hlin.exp

/-- The vacuum action derivative is -4 λ e^{4s}. -/
theorem vacuumAction_hasDerivAt (λ s : ℝ) :
    HasDerivAt (vacuumAction λ) (-4 * λ * Real.exp (4 * s)) s := by
  have h := (conformalVolume_hasDerivAt s).const_mul (-λ)
  simpa [vacuumAction, mul_assoc, mul_left_comm, mul_comm] using h

@[simp] theorem vacuumAction_zero (λ : ℝ) : vacuumAction λ 0 = -λ := by
  simp [vacuumAction, conformalVolume]

/-- At the reference metric, the conformal trace derivative is -4λ. -/
theorem vacuumAction_hasDerivAt_zero (λ : ℝ) :
    HasDerivAt (vacuumAction λ) (-4 * λ) 0 := by
  simpa using vacuumAction_hasDerivAt λ 0

/-- Trace coordinate extracted from the one-parameter conformal variation. -/
def vacuumTrace (λ : ℝ) : ℝ := -4 * λ

/-- Any positive vacuum amplitude has negative conformal trace. -/
theorem vacuumTrace_neg {λ : ℝ} (hλ : 0 < λ) : vacuumTrace λ < 0 := by
  dsimp [vacuumTrace]
  nlinarith

/-- Low finite birthmark-model amplitude λ=21/64. -/
theorem lowBirthmarkVacuumTrace : vacuumTrace (21 / 64 : ℝ) = -21 / 16 := by
  norm_num [vacuumTrace]

/-- High finite birthmark-model amplitude λ=3/8. -/
theorem highBirthmarkVacuumTrace : vacuumTrace (3 / 8 : ℝ) = -3 / 2 := by
  norm_num [vacuumTrace]

/-- Model-level metric-variation sign is now explicit. -/
def modelConformalMetricVariationSignOwned : Bool := true

/-- This theorem does not derive the raw CMP119 Eq.(2.23) variation callback. -/
def cmp119SourceNativeMetricVariationStillRequired : Bool := true

end Synthesis.HistoryVacuumConformalVariation
