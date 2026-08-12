import Mathlib

/-!
# Lean mirror of the cancellation-pressure interface cluster (genuine witnesses)

Faithful transcription of:
* `DASHI/Arithmetic/CancellationPressureCore.agda` — the thin arithmetic surface
  fixing carrier, step, and the monotone pressure seam;
* `DASHI/Arithmetic/CancellationPressureBound.agda` — the bound seam on top of a
  core.

Following the honesty discipline, the abstract interfaces are transcribed as Lean
structures (assumptions are honest fields, never axioms) and each is backed by a
genuine concrete witness (`Nat` with `Nat.pred` as the contracting step).
-/

namespace AgdaMirror.CancellationPressure

/-- The cancellation-pressure core: a carrier with a step that does not increase
the pressure. -/
structure CancellationPressureCore where
  Carrier : Type
  step : Carrier → Carrier
  cancellationPressure : Carrier → Nat
  pressure_step : ∀ x, cancellationPressure (step x) ≤ cancellationPressure x

/-- A genuine witness: `Nat` with the predecessor step and identity pressure. -/
def natCore : CancellationPressureCore where
  Carrier := Nat
  step := Nat.pred
  cancellationPressure := id
  pressure_step x := Nat.pred_le x

/-- A bound surface on top of a core. -/
structure CancellationPressureBound (Core : CancellationPressureCore) where
  pressureBound : Core.Carrier → Nat
  pressure_le_bound : ∀ x, Core.cancellationPressure x ≤ pressureBound x
  bound_step : ∀ x, pressureBound (Core.step x) ≤ pressureBound x

/-- A genuine witness for the `natCore`: identity bound. -/
def natBound : CancellationPressureBound natCore where
  pressureBound := id
  pressure_le_bound _ := le_refl _
  bound_step x := Nat.pred_le x

end AgdaMirror.CancellationPressure
