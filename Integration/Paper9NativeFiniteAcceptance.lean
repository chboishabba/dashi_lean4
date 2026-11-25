import Integration.Paper9LiteralCross

/-! Local acceptance target, UNCOMPILED. This is deliberately a
separate entrypoint. Each finite predicate must be inhabited by the
Lean kernel; external arithmetic receipts are not used as proof terms.
Run locally with the pinned toolchain and a bounded timeout. If
`decide` is too expensive, repair the verified checker rather than
substitute an axiom or trust an external Boolean. -/
namespace Integration.Paper9NativeFiniteAcceptance
open Integration.Paper9ExecutableCM163
open Integration.Paper9CMShiftCheck
open Integration.Paper9ScalarCross
open Integration.Paper9CMOriginalMachinWindow
open Integration.Paper9CMNormalizedCuspWindow
open Integration.Paper9LiteralCross

theorem unitChecked : unitOK=true := by decide
theorem diagonalChecked : diagOK=true := by decide
theorem shiftChecked : shiftOK=true := by decide
theorem sliceChecked : sliceOK=true := by decide
theorem jetChecked : jetOK=true := by decide
theorem piChecked : piRoundOK := by decide
theorem sqrtChecked : sqrtRoundOK := by decide
theorem expChecked : expWindowOK := by decide

theorem universalRawCross : ∀ k, RawCross k :=
  rawCrossFromFiniteChecks unitChecked diagonalChecked shiftChecked
    sliceChecked jetChecked piChecked sqrtChecked expChecked

#print axioms universalRawCross
end Integration.Paper9NativeFiniteAcceptance
