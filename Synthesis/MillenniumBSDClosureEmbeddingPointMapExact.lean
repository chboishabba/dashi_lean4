import Synthesis.MillenniumBSDOriginalKummerLocalizationValueExact

/-!
Actual elliptic base-change point map along an embedding of algebraic
closures, not a freely chosen additive map. The source W remains fixed
throughout. The compatible closure embedding, continuous restriction of
absolute Galois groups, and the iterated local curve base-change
identification are the remaining field-level localization obligations.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable [Algebra K L] [Algebra K (AlgebraicClosure L)]
variable [IsScalarTower K L (AlgebraicClosure L)]
variable (W : WeierstrassCurve K) [W.IsElliptic]

abbrev LocalClosurePoint := (W⁄(AlgebraicClosure L)).toAffine.Point

/-- Literal addition-preserving Mathlib map induced by the chosen
closure embedding of the actual field, using the same W. -/
def closureGeometricPointMap
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    GeometricPoint W →+ LocalClosurePoint (L := L) W :=
  WeierstrassCurve.Affine.Point.map (W' := W.toAffine) e

def localClosureAction (σ : Field.absoluteGaloisGroup L) :
    LocalClosurePoint (L := L) W →+ LocalClosurePoint (L := L) W :=
  WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
    (σ.toAlgHom.restrictScalars K)

/-- An actual field-intertwining identity is sufficient for the
geometric-point equivariance needed in the continuous H1 weld.
No extra unrelated point-map equivariance hypothesis. -/
theorem closureGeometricPointMap_equivariant
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ρ : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup K)
    (h : ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
      σ (e x) = e (ρ σ x))
    (σ : Field.absoluteGaloisGroup L) (P : GeometricPoint W) :
    closureGeometricPointMap W e (galoisPointMap W (ρ σ) P) =
      localClosureAction W σ (closureGeometricPointMap W e P) := by
  have he : e.comp (ρ σ).toAlgHom =
      (σ.toAlgHom.restrictScalars K).comp e := by
    ext x
    exact (h σ x).symm
  unfold closureGeometricPointMap localClosureAction galoisPointMap
  rw [WeierstrassCurve.Affine.Point.map_map (W' := W.toAffine),
      WeierstrassCurve.Affine.Point.map_map (W' := W.toAffine), he]

/-- The actual rational point first embedded in the global geometric
closure and then in the local closure equals the direct base change
through the same structural field embedding. -/
theorem closureGeometricPointMap_basePoint
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (P : BasePoint W) :
    closureGeometricPointMap W e (basePointToGeometric W P) =
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
        (Algebra.ofId K (AlgebraicClosure L)) P := by
  have he : e.comp (Algebra.ofId K (AlgebraicClosure K)) =
      Algebra.ofId K (AlgebraicClosure L) := by
    ext x
    exact e.commutes x
  unfold closureGeometricPointMap basePointToGeometric
  rw [WeierstrassCurve.Affine.Point.map_map (W' := W.toAffine), he]

end
end BSDCohomology
