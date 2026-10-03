import NSBControl.Rational345Round71W1

namespace NSBControl
namespace Rational345Round71W1Test

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71W1

example : decodeInitial = u₀ := by
  exact decodeInitial_exact

example : decodeInitialRHS = galerkinField u₀ := by
  exact decodeInitialRHS_exact

end Rational345Round71W1Test
end NSBControl
