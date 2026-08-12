import Mathlib
import AgdaMirror.CRTPeriod
import AgdaMirror.JFixedPoint

/-!
# Lean mirror of `DASHI/Algebra/MoonshineBridge.agda` (genuine, fully proved)

Bridges the CRT period and the `j`-fixed-point contraction into the moonshine
coefficient: `period + 1 = 196884 = contract(unitObs)`.  All genuine
definitional identities, fully proved.
-/

namespace AgdaMirror.MoonshineBridge

open AgdaMirror.CRTPeriod (period)
open AgdaMirror.JFixedPoint (contract unitObs)

/-- McKay's moonshine coefficient. -/
def moonshineCoefficient : Nat := 196884

theorem crtPeriodPlusOne : period + 1 = moonshineCoefficient := rfl

theorem jUnitContract : contract unitObs = moonshineCoefficient := rfl

/-- The bridge: the CRT period (+1) equals the `j`-fixed contraction. -/
theorem moonshineBridge : period + 1 = contract unitObs := rfl

/-- The packaged scalar bridge. -/
structure MoonshineScalarBridge where
  periodPlusOne : period + 1 = moonshineCoefficient
  unitContract : contract unitObs = moonshineCoefficient
  bridge : period + 1 = contract unitObs

/-- The canonical witness. -/
def moonshineScalarBridgeSurface : MoonshineScalarBridge :=
  ⟨crtPeriodPlusOne, jUnitContract, moonshineBridge⟩

end AgdaMirror.MoonshineBridge
