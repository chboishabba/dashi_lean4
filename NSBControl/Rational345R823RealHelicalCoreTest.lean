import NSBControl.Rational345R823RealHelicalCore

namespace NSBControl
namespace Rational345R823RealHelicalCoreTest

open Rational345RealRadius4
open Rational345R823RealHelicalCore

example (sign : HelicitySign) (k : Mode) : ℝ :=
  signedEigenvalue sign k

example (sign : HelicitySign) (u : State) (k : Mode) : Vec3 :=
  helicalComponent sign u k

example (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (htrans : bilinearDot (kComplex k) (u k) = 0) :
    helicalComponent plus u k + helicalComponent minus u k = u k := by
  exact helical_decomposition_of_transverse u k hk htrans

example (u : State) (p q k : Mode)
    (hres : Resonates p q k)
    (hp : nonzeroMode p) (hq : nonzeroMode q)
    (hpt : bilinearDot (kComplex p) (u p) = 0)
    (hqt : bilinearDot (kComplex q) (u q) = 0) :
    pairedInteraction u p q k = fourComponentPairInteraction u p q k := by
  exact pairedInteraction_expands_four_components
    u p q k hres hp hq hpt hqt

example (u : State) (p q k : Mode) : Vec3 :=
  fourSignInner u p q k

end Rational345R823RealHelicalCoreTest
end NSBControl
