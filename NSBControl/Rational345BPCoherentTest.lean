import NSBControl.Rational345BPCoherent

namespace NSBControl
namespace Rational345BPCoherentTest

open Rational345BPMaxCut
open Rational345BPCoherent

example (leaves : CoherentOperatorLeaves) : CoherentLeaf := by
  exact coherentLeaf_of_operator_leaves leaves

end Rational345BPCoherentTest
end NSBControl
