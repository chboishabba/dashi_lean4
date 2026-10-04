import Synthesis.MillenniumHodgeFundamentalCycleExact
import Synthesis.MillenniumHodgeCycleIsoPostcompositionExact
import Synthesis.MillenniumHodgeRulingCycleSwapMaxCutExact

/-!
# Hodge regression: actual P¹ ruling cycles and factor-swap exchange

This owner contains no synthetic ruling lattice.  Under the standard geometric
instances required by Mathlib's genuine cycle pushforward, it defines

  D₁ = (i₁)_* [P¹_Q],   D₂ = (i₂)_* [P¹_Q]

on the literal `P1QSelfProductOverQ` and proves that the actual pullback
symmetry exchanges them.  The existing anti-invariant theorem then gives
σ_*(D₁-D₂)=-(D₁-D₂).
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry

noncomputable section

section SelectedRulingCycles

variable [IrreducibleSpace P1QScheme]
local noncomputable instance : DecidableEq P1QScheme := Classical.decEq _
variable [QuasiCompact p1QRulingOne] [QuasiCompact p1QRulingTwo]

/-- Actual fundamental cycle of the selected projective line. -/
noncomputable def p1QFundamentalCycle : AlgebraicCycle P1QScheme ℤ :=
  fundamentalCycle P1QScheme

/-- First genuine ruling cycle `(i₁)_*[P¹]`. -/
noncomputable def p1QRulingCycleOne :
    AlgebraicCycle P1QSelfProductOverQ ℤ :=
  actualCyclePushforward p1QRulingOne p1QFundamentalCycle

/-- Second genuine ruling cycle `(i₂)_*[P¹]`. -/
noncomputable def p1QRulingCycleTwo :
    AlgebraicCycle P1QSelfProductOverQ ℤ :=
  actualCyclePushforward p1QRulingTwo p1QFundamentalCycle

/-- The actual factor swap sends the first genuine ruling cycle to the second. -/
theorem p1QRulingCycleOne_swap :
    actualCyclePushforward p1QFactorSwapOverQ.hom p1QRulingCycleOne =
      p1QRulingCycleTwo := by
  unfold p1QRulingCycleOne p1QRulingCycleTwo
  rw [actualCyclePushforward_postcompose_iso]
  rw [p1QRulingOne_swap]

/-- The actual factor swap sends the second genuine ruling cycle to the first. -/
theorem p1QRulingCycleTwo_swap :
    actualCyclePushforward p1QFactorSwapOverQ.hom p1QRulingCycleTwo =
      p1QRulingCycleOne := by
  unfold p1QRulingCycleOne p1QRulingCycleTwo
  rw [actualCyclePushforward_postcompose_iso]
  rw [p1QRulingTwo_swap]

/-- The selected ruling cycles satisfy the exact exchange interface already
consumed by the genuine anti-invariant cycle theorem. -/
theorem p1QRulingCycleExchange :
    P1QRulingCycleExchange p1QRulingCycleOne p1QRulingCycleTwo := by
  exact ⟨p1QRulingCycleOne_swap, p1QRulingCycleTwo_swap⟩

/-- Genuine cycle-side regression theorem on the selected P¹×P¹. -/
theorem p1QRulingDifference_antiInvariant :
    actualCyclePushforward p1QFactorSwapOverQ.hom
        (p1QRulingCycleOne - p1QRulingCycleTwo) =
      -(p1QRulingCycleOne - p1QRulingCycleTwo) :=
  p1Q_ruling_difference_antiInvariant_of_exchange
    p1QRulingCycleOne p1QRulingCycleTwo p1QRulingCycleExchange

end SelectedRulingCycles

/-!
MAX-CUT STATUS

THE CYCLE-SIDE REGRESSION IS NOW A REAL THEOREM PARAMETRIZED ONLY BY STANDARD
MATHLIB GEOMETRIC INSTANCES:
* `IrreducibleSpace P1QScheme`;
* `QuasiCompact p1QRulingOne`;
* `QuasiCompact p1QRulingTwo`.

No additional cycle representation or map-composition theorem remains.  The
next implementation cut is to discharge/infer those instances for the literal
Proj/ruling morphisms.  After that, the next genuinely separate boundary is a
scheme-level cycle-class map and its proper-pushforward naturality.
-/

end

end Synthesis.Millennium.Hodge
