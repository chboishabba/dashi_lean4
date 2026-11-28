import Synthesis.MillenniumBSDClosureEmbeddingPointMapExact
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.KrullTopology

/-!
Use the pinned Mathlib algebraic-closure lift and normal restriction,
rather than postulating an arbitrary map between absolute Galois groups.
The same chosen closure embedding controls the field and point maps.
For a completion use L=K_v and its structural K-algebra. The Krull continuity proof below uses finite fixing subextensions.
-/
namespace BSDCohomology
open WeierstrassCurve
open scoped Topology BigOperators
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

/-- Continuity in the actual Krull topologies. For each finite global
subextension, adjoin the finitely many embedded basis vectors to L.
Its open fixing subgroup maps into the original global fixing subgroup.
This argument does not require Kbar→Lbar to be surjective. -/
theorem closureRestriction_continuous
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Continuous (closureRestrictionHom e) := by
  classical
  apply continuous_of_continuousAt_one (closureRestrictionHom e)
  change Filter.Tendsto (closureRestrictionHom e) (𝓝 1)
    (𝓝 (closureRestrictionHom e 1))
  rw [map_one]
  rw [Filter.tendsto_def]
  intro S hS
  obtain ⟨E,hE,hsub⟩ :=
    (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) S).mp hS
  letI : FiniteDimensional K E := hE
  let b := Module.finBasis K E
  let gen : Fin (Module.finrank K E) → AlgebraicClosure L :=
    fun i => e (b i : AlgebraicClosure K)
  let T : Set (AlgebraicClosure L) := Set.range gen
  letI : Fintype T := (Set.finite_range gen).fintype
  let F := IntermediateField.adjoin L T
  have hF : FiniteDimensional L F :=
    IntermediateField.finiteDimensional_adjoin
      (fun y _ => Algebra.IsIntegral.isIntegral y)
  apply (krullTopology_mem_nhds_one_iff L (AlgebraicClosure L) _).mpr
  refine ⟨F,hF,?_⟩
  intro σ hσ
  apply hsub
  change closureRestrictionHom e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let xE : E := ⟨x,hx⟩
  have hfix (i : Fin (Module.finrank K E)) :
      closureRestrictionHom e σ (b i : AlgebraicClosure K) =
        (b i : AlgebraicClosure K) := by
    apply e.injective
    change e (restrictClosureAutomorphism e σ (b i : AlgebraicClosure K)) =
      e (b i : AlgebraicClosure K)
    rw [← restrictClosureAutomorphism_commutes]
    have hy : gen i ∈ F :=
      IntermediateField.subset_adjoin L (Set.mem_range_self i)
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ (gen i) hy
  have hrepr : x = ∑ i : Fin (Module.finrank K E),
      algebraMap K (AlgebraicClosure K) (b.repr xE i) *
        (b i : AlgebraicClosure K) := by
    simpa [xE,Algebra.smul_def] using
      congrArg E.val (b.sum_repr xE).symm
  calc
    closureRestrictionHom e σ x =
        closureRestrictionHom e σ
          (∑ i : Fin (Module.finrank K E),
            algebraMap K (AlgebraicClosure K) (b.repr xE i) *
              (b i : AlgebraicClosure K)) := congrArg (closureRestrictionHom e σ) hrepr
    _ = ∑ i : Fin (Module.finrank K E),
        algebraMap K (AlgebraicClosure K) (b.repr xE i) *
          (b i : AlgebraicClosure K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul,AlgEquiv.commutes,hfix]
    _ = x := hrepr.symm

def continuousClosureRestriction
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K :=
  ⟨closureRestrictionHom e,closureRestriction_continuous e⟩


end
end BSDCohomology
