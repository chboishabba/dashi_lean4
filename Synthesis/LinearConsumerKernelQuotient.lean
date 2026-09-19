import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Linear consumer-family kernel quotient donor

Generic algebra for consumer-indexed compression.

Given a family of linear consumers `A i : V →ₗ[R] W`, two states are
observationally equal for the whole family exactly when their difference lies
in the intersection of the consumer kernels. Consequently a trivial joint
kernel makes the consumer family jointly injective.

This file is deliberately domain-neutral. It does not mention RSA-260, CADO,
Block Wiedemann, `F.sols`, `mksol`, or any production artifact identity.
-/

namespace Synthesis

universe uR uV uW uI

variable {R : Type uR} {V : Type uV} {W : Type uW} {ι : Type uI}
variable [Ring R] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- The subspace invisible to every linear consumer in the declared family. -/
def jointKernel (A : ι → V →ₗ[R] W) : Submodule R V :=
  ⨅ i, LinearMap.ker (A i)

/-- Membership in the joint kernel means that every declared consumer
annihilates the vector. -/
theorem mem_jointKernel_iff (A : ι → V →ₗ[R] W) (v : V) :
    v ∈ jointKernel A ↔ ∀ i, A i v = 0 := by
  simp [jointKernel]

/-- Two states have identical outputs for every consumer exactly when their
difference lies in the intersection of all consumer kernels. -/
theorem same_outputs_iff_sub_mem_iInf_ker
    (A : ι → V →ₗ[R] W) (x y : V) :
    (∀ i, A i x = A i y) ↔ x - y ∈ jointKernel A := by
  rw [mem_jointKernel_iff]
  constructor
  · intro h i
    simpa [map_sub, h i]
  · intro h i
    have hz := h i
    simpa [map_sub, sub_eq_zero] using hz

/-- If the intersection of the consumer kernels is trivial, equality of every
consumer output forces equality of the original states. -/
theorem jointly_injective_of_iInf_ker_eq_bot
    (A : ι → V →ₗ[R] W)
    (hker : jointKernel A = ⊥)
    {x y : V}
    (houtputs : ∀ i, A i x = A i y) :
    x = y := by
  have hmem : x - y ∈ jointKernel A :=
    (same_outputs_iff_sub_mem_iInf_ker A x y).mp houtputs
  rw [hker] at hmem
  have hzero : x - y = 0 := by
    simpa using hmem
  exact sub_eq_zero.mp hzero

end Synthesis
