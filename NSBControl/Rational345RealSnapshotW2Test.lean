import NSBControl.Rational345RealInitialState

/-!
# W2 regression target

This is intentionally the first executable target for the R830 backend weld:
the genuine real radius-four selected observable must specialize at the real
3-4-5 initial state to the exact R850 value.

The proof is deliberately not supplied here by a duplicate certificate; this
module stays as the consumer/regression test for the production W2 theorem.
-/

namespace NSBControl
namespace Rational345RealSnapshotW2Test

open Rational345RealRadius4
open Rational345RealInitialState

example : selectedRate u₀ = expectedInitialRate := by
  simp [selectedRate]

end Rational345RealSnapshotW2Test
end NSBControl
