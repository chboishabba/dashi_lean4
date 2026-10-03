import NSBControl.Rational345BPBudget
import NSBControl.Rational345ShortTime

namespace NSBControl
namespace Rational345BPBudgetTest

open Rational345BPBudget
open Rational345ShortTime

example : selectedRateLipschitzBudget ≤ rateLipschitzBound := by
  exact selectedRateLipschitzBudget_le_certified

end Rational345BPBudgetTest
end NSBControl
