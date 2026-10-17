import Synthesis.MonsterGriessMaschkeComplement

namespace Synthesis.MonsterGriessMaschkeComplementRegression

open Synthesis.MonsterGriessMaschkeComplement

noncomputable section

universe u

variable {k G V : Type u}
variable [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

example
    (rho : Representation k G V)
    (omega : V)
    (homega : omega != 0)
    (hfixed : forall g : G, rho g omega = omega)
    (hdim : Module.finrank k V = 196884) :
    Exists fun C : Subrepresentation rho =>
      IsCompl (fixedConformalLine rho omega hfixed) C /\
      Module.finrank k C.toSubmodule = 196883 :=
  existsGriessComplement rho omega homega hfixed hdim

end

end Synthesis.MonsterGriessMaschkeComplementRegression
