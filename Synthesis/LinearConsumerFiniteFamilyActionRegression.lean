import Synthesis.LinearConsumerFiniteFamilyAction

/-!
Regression surface for the common-module/linearity weld used by the RSA
consumer-family route.
-/

namespace Synthesis

universe uR uC uW uI

variable {R : Type uR} {C : Type uC} {W : Type uW} {ι : Type uI}
variable [Semiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid W] [Module R W] [Fintype ι]

#check finiteFamilyAction
#check finiteFamilyAction_apply

end Synthesis
