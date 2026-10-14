import Mathlib.LinearAlgebra.Basic

/-!
# Centralizer action makes the source-native C2 norm equivariant

For the weight-two 2B Tate sequence the integral/mod-2 norm is `1 + a`, where
`a` is the selected involution.  Every operator coming from the centralizer of
`a` commutes with `a`; therefore it commutes with the norm as a purely linear
identity.  No separate matrix-level norm-equivariance acquisition is needed.

The concrete Monster/Co1 action and the fact that a chosen operator lies in the
centralizer remain source/same-object inputs.  This file compiles those inputs
to the norm-commutation equation consumed by the residual range weld.
-/

namespace Integration.OggSSP2BCentralizerNormEquivariance

variable {K V : Type*}
  [Semiring K]
  [AddCommMonoid V] [Module K V]

/-- The additive C2 norm operator `1 + a`. -/
def normMap (a : V →ₗ[K] V) : V →ₗ[K] V :=
  LinearMap.id + a

/-- Any linear operator commuting with the selected involution also commutes
with its norm `1+a`. -/
theorem norm_commutes
    (a g : V →ₗ[K] V)
    (hcomm : g.comp a = a.comp g) :
    g.comp (normMap a) = (normMap a).comp g := by
  ext x
  change g (x + a x) = g x + a (g x)
  rw [g.map_add]
  have hx : g (a x) = a (g x) :=
    congrArg (fun f : V →ₗ[K] V => f x) hcomm
  exact congrArg (fun y => g x + y) hx

end Integration.OggSSP2BCentralizerNormEquivariance
