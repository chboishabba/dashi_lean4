import NSBControl.Rational345RealSnapshotW2

/-!
# W2 regression target

The genuine real radius-four selected observable must specialize at the real
3-4-5 initial state to the exact R850 value.  This module is intentionally only
a consumer of the production theorem.
-/

namespace NSBControl
namespace Rational345RealSnapshotW2Test

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotW2

example : selectedRate u₀ = expectedInitialRate := by
  exact selectedRate_u₀_exact

example : selectedRate u₀ < 0 := by
  exact selectedRate_u₀_negative

end Rational345RealSnapshotW2Test
end NSBControl
