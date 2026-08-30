import Mathlib
import AgdaMirror.CRTPeriod
import AgdaMirror.JFixedPoint

/-!
# Lean mirror of `CRTJFixedPointBridge.agda` (genuine, fully proved)

Faithful transcription of `CRTJFixedPointBridge.agda`, which ties together the
CRT period module and the `j`-fixed-point module: `period + 1 = 196884`, the
unit/stack observation contractions all equal `period + 1`, and the digit
periodicity instantiated at the moonshine value.
-/

namespace AgdaMirror.CRTJFixedPointBridge

open AgdaMirror

theorem period_plus_one : CRTPeriod.period + 1 = 196884 := rfl

theorem unit_contract_period_plus_one :
    JFixedPoint.contract JFixedPoint.unitObs = CRTPeriod.period + 1 := by
  rw [JFixedPoint.unit_converges]; exact period_plus_one.symm

theorem stack_contract_period_plus_one (n : Nat) :
    JFixedPoint.contract (JFixedPoint.stack n) = CRTPeriod.period + 1 := by
  rw [JFixedPoint.stack_converges]; exact period_plus_one.symm

theorem crt_periodicity_at_moonshine_minus_one (k : Nat) :
    CRTPeriod.dig (CRTPeriod.period + k * CRTPeriod.period) = CRTPeriod.dig CRTPeriod.period :=
  CRTPeriod.period_thm CRTPeriod.period k

/-- The bundled bridge record, exactly as in the Agda surface. -/
structure Bridge where
  crtPeriodPlusOne : CRTPeriod.period + 1 = 196884
  unitContractMatchesPeriodPlusOne :
    JFixedPoint.contract JFixedPoint.unitObs = CRTPeriod.period + 1
  stackContractMatchesPeriodPlusOne :
    ∀ n : Nat, JFixedPoint.contract (JFixedPoint.stack n) = CRTPeriod.period + 1
  moonshineMinusOnePeriodicity :
    ∀ k : Nat, CRTPeriod.dig (CRTPeriod.period + k * CRTPeriod.period) = CRTPeriod.dig CRTPeriod.period

def crtJFixedPointBridgeSurface : Bridge where
  crtPeriodPlusOne := period_plus_one
  unitContractMatchesPeriodPlusOne := unit_contract_period_plus_one
  stackContractMatchesPeriodPlusOne := stack_contract_period_plus_one
  moonshineMinusOnePeriodicity := crt_periodicity_at_moonshine_minus_one

end AgdaMirror.CRTJFixedPointBridge
