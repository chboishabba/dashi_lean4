import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Finite-family linear consumer action

A domain-neutral common-module/linearity donor for the RSA consumer-family
lane.  Given finitely many linear layer actions `L i : C →ₗ[R] W`, evaluating
a coefficient family by summing the layer actions is itself a linear map from
the common function module `ι → C` to `W`.

This file does not identify a CADO generator carrier, Krylov block, prepared
operator, solution range, or production RSA-260 object.  Those same-object
bindings remain separate.
-/

namespace Synthesis

open scoped BigOperators

universe uR uC uW uI

variable {R : Type uR} {C : Type uC} {W : Type uW} {ι : Type uI}
variable [Semiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid W] [Module R W] [Fintype ι]

/-- Sum the declared linear layer actions over a finite coefficient family. -/
def finiteFamilyAction (L : ι → C →ₗ[R] W) : (ι → C) →ₗ[R] W where
  toFun F := ∑ i, L i (F i)
  map_add' F F' := by
    simp [Finset.sum_add_distrib]
  map_smul' r F := by
    simp

@[simp]
theorem finiteFamilyAction_apply (L : ι → C →ₗ[R] W) (F : ι → C) :
    finiteFamilyAction L F = ∑ i, L i (F i) :=
  rfl

end Synthesis
