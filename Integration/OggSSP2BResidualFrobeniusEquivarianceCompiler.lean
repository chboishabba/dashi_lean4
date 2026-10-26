import Integration.OggSSP2BEquivariantResidualQuotient
import Integration.OggSSP2BResidualFrobeniusWeld

/-!
# Compile Co1 equivariance of the induced residual map

`ResidualFrobeniusReceipt` previously exposed equivariance of the induced
24-dimensional residual map as a field.  That field is not independent.

Let

  residual : M -> S
  pi       : M -> V24
  f        : V24 -> S

with `f (pi x) = residual x`.  The canonical residual quotient makes `pi`
surjective.  Therefore equivariance of `pi` and of the source-native residual
map forces equivariance of `f` by `EquivariantResidualQuotient`.

The only representation-facing inputs retained here are the actual Co1 actions,
equivariance of the quotient chart/residual map, and agreement between that
concrete equivariance predicate and the predicate used by the already-paid
unique Hom-line receipt.
-/

namespace Integration.OggSSP2BResidualFrobeniusEquivarianceCompiler

namespace E := Integration.OggSSP2BEquivariantResidualQuotient
namespace Q := Integration.OggSSP2BResidualNaturalQuotient
namespace RF := Integration.OggSSP2BResidualFrobeniusWeld

variable {K M S V : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The actual quotient presentation `M -> V24`. -/
def naturalProjection
    {residual : M →ₗ[K] S}
    (q : Q.ResidualNaturalQuotientReceipt residual V) : M → V :=
  fun x => q.quotientEquiv (residual.ker.mkQ x)

/-- The canonical quotient presentation is surjective. -/
theorem naturalProjection_surjective
    {residual : M →ₗ[K] S}
    (q : Q.ResidualNaturalQuotientReceipt residual V) :
    Function.Surjective (naturalProjection q) := by
  intro v
  obtain ⟨x, hx⟩ := residual.ker.mkQ_surjective (q.quotientEquiv.symm v)
  refine ⟨x, ?_⟩
  change q.quotientEquiv (residual.ker.mkQ x) = v
  rw [hx]
  simp

/-- The map on the natural 24-space is literally the descent of the original
residual coordinate through the quotient presentation. -/
theorem onNatural_descent
    {residual : M →ₗ[K] S}
    (q : Q.ResidualNaturalQuotientReceipt residual V)
    (x : M) :
    q.onNatural (naturalProjection q x) = residual x := by
  simp [naturalProjection, Q.ResidualNaturalQuotientReceipt.onNatural,
    Q.inducedResidual]

/-- Concrete action data sufficient to remove induced-map equivariance as an
independent proof obligation. -/
structure Co1QuotientActionReceipt
    {G : Type*}
    {residual : M →ₗ[K] S}
    {frobenius : V →ₗ[K] S}
    (q : Q.ResidualNaturalQuotientReceipt residual V)
    (unique : RF.UniqueNonzeroMapReceipt frobenius) : Prop where
  actM : G → M → M
  actV : G → V → V
  actS : G → S → S
  quotientProjection_equivariant :
    E.Equivariant actM actV (naturalProjection q)
  residual_equivariant :
    E.Equivariant actM actS residual
  homPredicate_agrees :
    ∀ f : V →ₗ[K] S,
      unique.IsEquivariant f ↔ E.Equivariant actV actS f

namespace Co1QuotientActionReceipt

variable {G : Type*}
variable {residual : M →ₗ[K] S}
variable {frobenius : V →ₗ[K] S}
variable (q : Q.ResidualNaturalQuotientReceipt residual V)
variable (unique : RF.UniqueNonzeroMapReceipt frobenius)
variable (a : Co1QuotientActionReceipt (G := G) q unique)

/-- Equivariance of the induced map is forced by quotient descent. -/
theorem onNatural_equivariant :
    unique.IsEquivariant q.onNatural := by
  apply (a.homPredicate_agrees q.onNatural).2
  exact E.equivariant_of_surjective_descent
    (naturalProjection q)
    residual
    q.onNatural
    (naturalProjection_surjective q)
    (onNatural_descent q)
    a.quotientProjection_equivariant
    a.residual_equivariant

/-- Compile directly into the existing residual-Frobenius receipt. -/
def toResidualFrobeniusReceipt :
    RF.ResidualFrobeniusReceipt residual frobenius where
  quotientNatural := q
  uniqueNonzeroHom := unique
  inducedResidual_equivariant := a.onNatural_equivariant q unique

end Co1QuotientActionReceipt

end Integration.OggSSP2BResidualFrobeniusEquivarianceCompiler
