import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Unique invariant 24-submodule forces the residual image

The preferred post-Brauer route need not identify the quotient source
`M / ker(residual)` with a chosen natural 24-dimensional model if the target
`Sym^2(24)` has a unique invariant 24-dimensional submodule.

The runtime candidate is the explicit Frobenius-square image.  Once the actual
residual map is known independently to have rank 24 and to have invariant
range, uniqueness forces literal equality of submodules:

  range(residual) = range(Frobenius).

This is exactly the equality required by the existing cokernel compiler.
-/

namespace Integration.OggSSP2BUniqueInvariant24Range

variable {K S V : Type*}
  [DivisionRing K]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Runtime/theorem interface for the target module.  `IsInvariant` is kept
abstract so concrete Co1 action infrastructure remains owned by the source
module rather than duplicated here. -/
structure UniqueInvariant24SubmoduleReceipt
    (frobenius : V →ₗ[K] S)
    (IsInvariant : Submodule K S → Prop) : Prop where
  frobenius_range_finrank_eq_24 : Module.finrank K frobenius.range = 24
  frobenius_invariant : IsInvariant frobenius.range
  unique_invariant_24 :
    ∀ W : Submodule K S,
      Module.finrank K W = 24 → IsInvariant W → W = frobenius.range

namespace UniqueInvariant24SubmoduleReceipt

variable {frobenius : V →ₗ[K] S}
variable {IsInvariant : Submodule K S → Prop}
variable (u : UniqueInvariant24SubmoduleReceipt frobenius IsInvariant)

/-- Any invariant residual image with the forced rank 24 is the Frobenius image
as a literal submodule, with no quotient-source chart required. -/
theorem range_eq_frobenius
    {M : Type*} [AddCommGroup M] [Module K M]
    (residual : M →ₗ[K] S)
    (hrank : Module.finrank K residual.range = 24)
    (hinvariant : IsInvariant residual.range) :
    residual.range = frobenius.range :=
  u.unique_invariant_24 residual.range hrank hinvariant

end UniqueInvariant24SubmoduleReceipt

end Integration.OggSSP2BUniqueInvariant24Range
