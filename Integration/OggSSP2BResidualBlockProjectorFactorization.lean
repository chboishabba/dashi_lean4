import Integration.OggSSP2BResidualSupportFromFactorization

/-!
# Canonical source-block factorization of the actual residual norm coordinate

The strengthened CTBlocks computation identifies one unique 24-dimensional
source residual block, disjoint from the common 98280 support.  For a
centralizer-equivariant norm map, the residual target block can only see this
source block.

Rather than postulating an arbitrary factorization through some 24-space, this
owner packages the canonical map-level statement using an idempotent source
projector `e24`:

  e24^2 = e24,
  finrank range(e24) = 24,
  residual ∘ e24 = residual.

The last equation is precisely the block-equivariance content needed from the
actual norm map.  It constructs the literal factorization

  M --e24--> range(e24) --> S

and therefore supplies the support upper bound used by the no-slack rank
squeeze.
-/

namespace Integration.OggSSP2BResidualBlockProjectorFactorization

namespace F := Integration.OggSSP2BResidualSupportFromFactorization
namespace Squeeze := Integration.OggSSP2BResidualSupportSqueeze

variable {K M S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Canonical residual source block attached to the actual residual coordinate. -/
structure ResidualBlockProjectorReceipt (residual : M →ₗ[K] S) : Prop where
  e24 : M →ₗ[K] M
  idempotent : e24.comp e24 = e24
  range_finrank_eq_24 : Module.finrank K e24.range = 24
  residual_comp_projector : residual.comp e24 = residual
  blockProvenance : String

namespace ResidualBlockProjectorReceipt

variable {residual : M →ₗ[K] S}
variable (r : ResidualBlockProjectorReceipt residual)

/-- Project canonically to the residual source block. -/
def sourceProjection : M →ₗ[K] r.e24.range where
  toFun x := ⟨r.e24 x, ⟨x, rfl⟩⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- Restrict the actual residual coordinate to the residual source block. -/
def residualOn24 : r.e24.range →ₗ[K] S :=
  residual.domRestrict r.e24.range

/-- The block-equivariance equation gives the literal map factorization. -/
theorem factorization :
    residual = r.residualOn24.comp r.sourceProjection := by
  ext x
  change residual x = residual (r.e24 x)
  have h := LinearMap.congr_fun r.residual_comp_projector x
  exact h.symm

/-- Compile the canonical block projector into the generic 24-factorization
receipt used by the support/rank squeeze. -/
def toFactorizationReceipt :
    F.Residual24FactorizationReceipt (R24 := r.e24.range) residual where
  sourceProjection := r.sourceProjection
  residualOn24 := r.residualOn24
  factorization := r.factorization
  residualSource_finrank_eq_24 := r.range_finrank_eq_24
  sourceProvenance := r.blockProvenance

/-- Therefore the actual residual image has finrank at most 24. -/
def toSupportUpperBound : Squeeze.ResidualSupportUpperBoundReceipt residual :=
  r.toFactorizationReceipt.toSupportUpperBound

end ResidualBlockProjectorReceipt

end Integration.OggSSP2BResidualBlockProjectorFactorization
