import Integration.OggSSP2BResidualNaturalQuotient

/-!
# Residual quotient -> Frobenius weld

The actual residual norm projection has type

  residual : M_98304 -> Sym2(24)_300.

The Co1 Hom-line theorem does not apply to this source.  Factor first through

  Qr = M / ker(residual) ≃ V24.

The induced map on `V24` is nonzero by map-coupled rank rigidity.  The unique
nonzero **Co1-equivariant** Hom line therefore forces this induced map to equal
the Frobenius-square embedding.  Since quotienting by the kernel does not
change the image, the original residual map and Frobenius have the same range.

The equivariance predicate is part of the uniqueness receipt itself.  This is
crucial: `Hom_K(V24,Sym2(24))` is not one-dimensional as a plain linear Hom
space; the runtime statement concerns `Hom_Co1` only.
-/

namespace Integration.OggSSP2BResidualFrobeniusWeld

namespace Q := Integration.OggSSP2BResidualNaturalQuotient
namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity

variable {K M S V : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Proof-bearing version of the runtime theorem that `frobenius` spans the
unique nonzero **equivariant** Hom line.  `IsEquivariant` is deliberately kept
abstract here so this linear-algebra owner does not invent a second group-action
framework. -/
structure UniqueNonzeroMapReceipt
    (frobenius : V →ₗ[K] S) : Prop where
  IsEquivariant : (V →ₗ[K] S) → Prop
  frobenius_equivariant : IsEquivariant frobenius
  frobenius_ne_zero : frobenius ≠ 0
  unique_nonzero_equivariant :
    ∀ f : V →ₗ[K] S, IsEquivariant f → f ≠ 0 → f = frobenius

namespace Q.ResidualNaturalQuotientReceipt

variable {residual : M →ₗ[K] S}
variable (q : Q.ResidualNaturalQuotientReceipt residual V)

/-- Rewriting the source by the kernel quotient does not change the image of
the residual norm map. -/
theorem onNatural_range_eq_residual_range :
    q.onNatural.range = residual.range := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    obtain ⟨x, hx⟩ := residual.ker.mkQ_surjective (q.quotientEquiv.symm v)
    refine ⟨x, ?_⟩
    change Q.inducedResidual residual (q.quotientEquiv.symm v) = residual x
    rw [← hx]
    simp [Q.inducedResidual]
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨q.quotientEquiv (residual.ker.mkQ x), ?_⟩
    simp [Q.ResidualNaturalQuotientReceipt.onNatural, Q.inducedResidual]

end Q.ResidualNaturalQuotientReceipt

/-- Proof-bearing residual Frobenius identification on the correct 24d source. -/
structure ResidualFrobeniusReceipt
    (residual : M →ₗ[K] S)
    (frobenius : V →ₗ[K] S) : Prop where
  quotientNatural : Q.ResidualNaturalQuotientReceipt residual V
  uniqueNonzeroHom : UniqueNonzeroMapReceipt frobenius
  inducedResidual_equivariant :
    uniqueNonzeroHom.IsEquivariant quotientNatural.onNatural

namespace ResidualFrobeniusReceipt

variable {residual : M →ₗ[K] S}
variable {frobenius : V →ₗ[K] S}
variable (r : ResidualFrobeniusReceipt residual frobenius)

/-- Rank rigidity supplies nonzeroness of the induced 24 -> 300 map; the
explicit equivariance witness then places it on the unique Co1 Hom line. -/
theorem onNatural_eq_frobenius
    (hrank : Rank.LinearRankRigidityReceipt residual) :
    r.quotientNatural.onNatural = frobenius :=
  r.uniqueNonzeroHom.unique_nonzero_equivariant _
    r.inducedResidual_equivariant
    (r.quotientNatural.onNatural_ne_zero_from_rank hrank)

/-- Correct image-level conclusion for the original 98304 -> 300 residual map. -/
theorem residual_range_eq_frobenius_range
    (hrank : Rank.LinearRankRigidityReceipt residual) :
    residual.range = frobenius.range := by
  calc
    residual.range = r.quotientNatural.onNatural.range :=
      (r.quotientNatural.onNatural_range_eq_residual_range).symm
    _ = frobenius.range := by rw [r.onNatural_eq_frobenius hrank]

end ResidualFrobeniusReceipt

end Integration.OggSSP2BResidualFrobeniusWeld
