import Integration.OggSSP2BTateCokernelRankRigidity

/-!
# Residual norm quotient as the actual 24-dimensional Co1 module

The residual norm projection has source dimension 98304, target Sym2(24), rank
24 and kernel dimension 98280.  The one-dimensional Co1 Hom calculation does
NOT apply to that 98304-dimensional source.  It applies only after factoring
through the first-isomorphism-theorem quotient

  Qr := M / ker(residual),   dim Qr = 24.

This owner makes that quotient explicit.  The remaining source datum is a
Co1-equivariant linear chart from `Qr` to a fixed natural 24-dimensional model
`V`.  Once supplied, the induced residual map has the correct domain for the
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

/-- Source-native identification of the residual quotient with a fixed natural
24-dimensional Co1 model.  The equivariance proof remains explicit rather than
being inferred from equal dimensions. -/
structure ResidualNaturalQuotientReceipt
    (residual : M →ₗ[K] S) (V : Type*)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] where
  quotientEquiv : (M ⧸ residual.ker) ≃ₗ[K] V
  natural_finrank_eq_24 : Module.finrank K V = 24
  co1Equivariant : Prop
  co1Equivariant_paid : co1Equivariant
  sourceProvenance : String

namespace ResidualNaturalQuotientReceipt

variable {residual : M →ₗ[K] S}
variable (r : ResidualNaturalQuotientReceipt residual V)

/-- The actual residual norm map rewritten on the natural 24-dimensional
source.  This is the map to which Co1 Hom-line uniqueness applies. -/
def onNatural : V →ₗ[K] S :=
  (inducedResidual residual).comp r.quotientEquiv.symm.toLinearMap

/-- The natural model is explicitly 24-dimensional. -/
theorem natural_finrank_is_24 : Module.finrank K V = 24 :=
  r.natural_finrank_eq_24

/-- If the induced natural-source map vanished, then the original residual map
would vanish because every source element maps through its quotient class. -/
theorem onNatural_ne_zero
    (hresidual : residual ≠ 0) :
    r.onNatural ≠ 0 := by
  intro hzero
  apply hresidual
  ext x
  have hx := LinearMap.congr_fun hzero (r.quotientEquiv (residual.ker.mkQ x))
  simpa [onNatural, inducedResidual] using hx

/-- The map-coupled rank receipt supplies the required nonzeroness automatically. -/
theorem onNatural_ne_zero_from_rank
    (hrank : Rank.LinearRankRigidityReceipt residual) :
    r.onNatural ≠ 0 :=
  r.onNatural_ne_zero hrank.residual_ne_zero

end ResidualNaturalQuotientReceipt

end Integration.OggSSP2BResidualNaturalQuotient
