import Synthesis.MillenniumBSDClosureEmbeddingPointMapExact
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.KrullTopology

/-!
Use the pinned Mathlib algebraic-closure lift and normal restriction,
rather than postulating an arbitrary map between absolute Galois groups.
The same chosen closure embedding controls the field and point maps.
For a completion use L=K_v and its structural K-algebra. Continuity of
the restriction in Krull topologies is proved via finite fixing sets
in the companion next cut; this file pays the algebraic field map.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable [Algebra K L] [Algebra K (AlgebraicClosure L)]
variable [IsScalarTower K L (AlgebraicClosure L)]

/-- A genuine embedding of the chosen algebraic closure of K into
the algebraically closed Lbar. No surjectivity onto Lbar is assumed. -/
def chooseClosureEmbedding : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
  IsAlgClosed.lift

/-- The structural K-algebra and the new Kbar-algebra have identical
K→Lbar maps, so normal restriction applies to precisely this embedding. -/
def closureEmbeddingTower
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
      e.toRingHom.toAlgebra
    IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    e.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)

/-- Restrict the actual local automorphism to the embedded normal
algebraic closure, not to an independently selected isomorphic field. -/
def restrictClosureAutomorphism
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (σ : Field.absoluteGaloisGroup L) : Field.absoluteGaloisGroup K := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    e.toRingHom.toAlgebra
  letI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    closureEmbeddingTower e
  exact (σ.toAlgHom.restrictScalars K).restrictNormal' (AlgebraicClosure K)

theorem restrictClosureAutomorphism_commutes
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    σ (e x) = e (restrictClosureAutomorphism e σ x) := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    e.toRingHom.toAlgebra
  letI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    closureEmbeddingTower e
  exact ((σ.toAlgHom.restrictScalars K).restrictNormal_commutes
    (AlgebraicClosure K) x).symm

def closureRestrictionHom
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K where
  toFun := restrictClosureAutomorphism e
  map_one' := by
    ext x
    apply e.injective
    rw [← restrictClosureAutomorphism_commutes]
    rfl
  map_mul' σ τ := by
    ext x
    apply e.injective
    change e (restrictClosureAutomorphism e (σ*τ) x) =
      e (restrictClosureAutomorphism e σ (restrictClosureAutomorphism e τ x))
    rw [← restrictClosureAutomorphism_commutes,← restrictClosureAutomorphism_commutes,
      ← restrictClosureAutomorphism_commutes]
    rfl

/-- The earlier actual elliptic point-map theorem is now inhabited by
the field-level normal restriction; no new equivariance assumption. -/
theorem chosenClosurePointMap_equivariant
    (W : WeierstrassCurve K) [W.IsElliptic]
    (σ : Field.absoluteGaloisGroup L) (P : GeometricPoint W) :
    closureGeometricPointMap W (chooseClosureEmbedding (K:=K) (L:=L))
      (galoisPointMap W
        (closureRestrictionHom (chooseClosureEmbedding (K:=K) (L:=L)) σ) P) =
    localClosureAction W σ
      (closureGeometricPointMap W (chooseClosureEmbedding (K:=K) (L:=L)) P) := by
  exact closureGeometricPointMap_equivariant W _
    (closureRestrictionHom (chooseClosureEmbedding (K:=K) (L:=L)))
    (restrictClosureAutomorphism_commutes _) σ P

end
end BSDCohomology
