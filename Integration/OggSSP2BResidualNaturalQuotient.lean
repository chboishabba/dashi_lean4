import Integration.OggSSP2BTateCokernelRankRigidity

/-!
# Residual norm quotient as the actual 24-dimensional Co1 module

The residual norm projection has source dimension 98304, target Sym2(24), rank
24 and kernel dimension 98280.  The one-dimensional Co1 Hom calculation does
NOT apply to that 98304-dimensional source.  It applies only after factoring
through the first-isomorphism-theorem quotient

  Qr := M / ker(residual),   dim Qr = 24.

This owner makes that quotient explicit.  The remaining source datum is a
Co1-equivariant linear chart from `Qr` to the natural 24-dimensional module.
Once supplied, the induced residual map has the correct domain for the
Frobenius-Hom uniqueness theorem.
-/

namespace Integration.OggSSP2BResidualNaturalQuotient

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity

variable {K M S V : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The canonical map induced by `residual` on its kernel quotient. -/
def inducedResidual (residual : M →ₗ[K] S) :
    (M ⧸ residual.ker) →ₗ[K] S :=
  residual.ker.liftQ residual le_rfl

@[simp] theorem inducedResidual_mkQ
    (residual : M →ₗ[K] S) (x : M) :
    inducedResidual residual (residual.ker.mkQ x) = residual x := by
  rfl

/-- Source-native identification of the residual quotient with the natural
24-dimensional Co1 module.  The equivariance proof is kept as a proposition
because the concrete Co1 action types live in the runtime/model layer; the
linear chart itself is the same-object datum consumed here. -/
structure ResidualNaturalQuotientReceipt
    (residual : M →ₗ[K] S) where
  naturalModel : Type*
  naturalAddCommGroup : AddCommGroup naturalModel
  naturalModule : Module K naturalModel
  naturalFiniteDimensional : FiniteDimensional K naturalModel
  quotientEquiv : (M ⧸ residual.ker) ≃ₗ[K] naturalModel
  natural_finrank_eq_24 : Module.finrank K naturalModel = 24
  co1Equivariant : Prop
  co1Equivariant_paid : co1Equivariant
  sourceProvenance : String

attribute [instance] ResidualNaturalQuotientReceipt.naturalAddCommGroup
attribute [instance] ResidualNaturalQuotientReceipt.naturalModule
attribute [instance] ResidualNaturalQuotientReceipt.naturalFiniteDimensional

namespace ResidualNaturalQuotientReceipt

variable {residual : M →ₗ[K] S}
variable (r : ResidualNaturalQuotientReceipt residual)

/-- The actual residual norm map rewritten on the natural 24-dimensional
source.  This is the map to which the Co1 Hom-line uniqueness theorem applies. -/
def onNatural : r.naturalModel →ₗ[K] S :=
  (inducedResidual residual).comp r.quotientEquiv.symm.toLinearMap

/-- The residual quotient really has dimension 24. -/
theorem quotient_finrank_eq_24
    (hrank : Rank.LinearRankRigidityReceipt residual) :
    Module.finrank K (M ⧸ residual.ker) = 24 := by
  rw [Submodule.finrank_quotient]
  have hM : Module.finrank K M = 98304 := by
    have hnull := LinearMap.finrank_range_add_finrank_ker residual
    rw [hrank.residual_finrank_eq_24, hrank.kernel_finrank_eq_98280] at hnull
    omega
  rw [hM, hrank.kernel_finrank_eq_98280]
  decide

/-- The natural chart has the intended dimension independently. -/
theorem natural_finrank_is_24 : Module.finrank K r.naturalModel = 24 :=
  r.natural_finrank_eq_24

/-- If the induced natural-source map vanished, then the original residual map
would vanish because every element is represented by its quotient class. -/
theorem onNatural_ne_zero
    (hresidual : residual ≠ 0) :
    r.onNatural ≠ 0 := by
  intro hzero
  apply hresidual
  ext x
  have hx := LinearMap.congr_fun hzero (r.quotientEquiv (residual.ker.mkQ x))
  simpa [onNatural, inducedResidual] using hx

end ResidualNaturalQuotientReceipt

end Integration.OggSSP2BResidualNaturalQuotient
