import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Actual elliptic two-torsion carrier and absolute-Galois point transport

For an elliptic Weierstrass curve W/K, work on the literal geometric point
group W(K̄), with K̄ = AlgebraicClosure K.

Define E[2] as the kernel of multiplication by two on that actual point
group. Every σ ∈ Gal(K̄/K) acts on W(K̄) through Mathlib's genuine
base-change point map, and this additive map preserves E[2].

This is the underlying algebraic content needed before constructing the
continuous Galois representation E[2] as a TopRep.

No cohomology/Kummer comparison is claimed in this module.
-/

namespace BSDCohomology

open WeierstrassCurve

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Actual geometric rational points on W over the chosen algebraic closure. -/
abbrev GeometricPoint : Type u :=
  (W⁄(AlgebraicClosure K)).toAffine.Point

/-- Actual elliptic two-torsion subgroup inside W(K̄). -/
abbrev EllipticTwoTorsion :
    AddSubgroup (GeometricPoint W) :=
  (nsmulAddMonoidHom (α := GeometricPoint W) 2).ker

/-- Characterization by literal doubling on the geometric point group. -/
theorem mem_ellipticTwoTorsion_iff
    (P : GeometricPoint W) :
    P ∈ EllipticTwoTorsion W ↔ 2 • P = 0 := by
  rfl

/-- An absolute-Galois automorphism acts on the actual geometric point group
by Mathlib's addition-preserving base-change point map. -/
noncomputable def galoisPointMap
    (σ : Field.absoluteGaloisGroup K) :
    GeometricPoint W →+ GeometricPoint W := by
  exact
    WeierstrassCurve.Affine.Point.map
      (W' := W.toAffine)
      σ.toAlgHom

/-- The Galois point map commutes with literal doubling. -/
theorem galoisPointMap_double
    (σ : Field.absoluteGaloisGroup K)
    (P : GeometricPoint W) :
    galoisPointMap W σ (2 • P) =
      2 • galoisPointMap W σ P := by
  exact map_nsmul (galoisPointMap W σ) P 2

/-- Every absolute-Galois automorphism preserves the actual E[2] subgroup. -/
theorem galoisPointMap_preserves_twoTorsion
    (σ : Field.absoluteGaloisGroup K)
    (P : EllipticTwoTorsion W) :
    galoisPointMap W σ P.1 ∈ EllipticTwoTorsion W := by
  rw [mem_ellipticTwoTorsion_iff]
  rw [← galoisPointMap_double W σ P.1]
  rw [P.2]
  exact map_zero (galoisPointMap W σ)

/-- The resulting additive endomorphism of the literal E[2] group. -/
noncomputable def galoisTwoTorsionMap
    (σ : Field.absoluteGaloisGroup K) :
    EllipticTwoTorsion W →+ EllipticTwoTorsion W where
  toFun P :=
    ⟨galoisPointMap W σ P.1,
      galoisPointMap_preserves_twoTorsion W σ P⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (galoisPointMap W σ)
  map_add' P Q := by
    apply Subtype.ext
    exact map_add (galoisPointMap W σ) P.1 Q.1

/-- Forgetting the subtype, the E[2] action is exactly the geometric point
base-change action, so no synthetic action has been substituted. -/
theorem galoisTwoTorsionMap_coe
    (σ : Field.absoluteGaloisGroup K)
    (P : EllipticTwoTorsion W) :
    (galoisTwoTorsionMap W σ P).1 =
      galoisPointMap W σ P.1 := rfl

/-- Identity Galois automorphism acts identically on geometric points. -/
theorem galoisPointMap_one
    (P : GeometricPoint W) :
    galoisPointMap W (1 : Field.absoluteGaloisGroup K) P = P := by
  simpa [galoisPointMap] using
    (WeierstrassCurve.Affine.Point.map_id
      (W' := W.toAffine) P)

/-- Composition of absolute-Galois automorphisms is transported by the
actual base-change point functor. -/
theorem galoisPointMap_mul
    (σ τ : Field.absoluteGaloisGroup K)
    (P : GeometricPoint W) :
    galoisPointMap W (σ * τ) P =
      galoisPointMap W σ (galoisPointMap W τ P) := by
  symm
  simpa [galoisPointMap, AlgEquiv.mul_apply] using
    (WeierstrassCurve.Affine.Point.map_map
      (W' := W.toAffine)
      τ.toAlgHom σ.toAlgHom P)

/-- The same identity law restricted to literal E[2]. -/
theorem galoisTwoTorsionMap_one :
    galoisTwoTorsionMap W (1 : Field.absoluteGaloisGroup K)
      =
    AddMonoidHom.id (EllipticTwoTorsion W) := by
  ext P
  apply Subtype.ext
  exact galoisPointMap_one W P.1

/-- The same composition law restricted to literal E[2]. -/
theorem galoisTwoTorsionMap_mul
    (σ τ : Field.absoluteGaloisGroup K) :
    galoisTwoTorsionMap W (σ * τ)
      =
    (galoisTwoTorsionMap W σ).comp
      (galoisTwoTorsionMap W τ) := by
  ext P
  apply Subtype.ext
  exact galoisPointMap_mul W σ τ P.1

/-- The actual absolute-Galois action on E[2], bundled as a monoid
homomorphism into additive endomorphisms. -/
noncomputable def ellipticTwoTorsionAction :
    Field.absoluteGaloisGroup K →*
      AddMonoid.End (EllipticTwoTorsion W) where
  toFun := galoisTwoTorsionMap W
  map_one' := galoisTwoTorsionMap_one W
  map_mul' := galoisTwoTorsionMap_mul W

/-!
NEXT BSD-C GATE

Prove identity/composition for galoisTwoTorsionMap, bundle the maps as a
continuous ℤ-linear representation of Field.absoluteGaloisGroup K, then
instantiate GenuineDegreeOneShaTwoTorsion with that E[2] TopRep.

After that still remain:
  * global Kummer connecting map E(K)/2E(K) → H¹(K,E[2]);
  * local Kummer maps;
  * x-T/cohomological Selmer comparison;
  * arithmetic defect ≃ cohomological Sha[2].
-/

end

end BSDCohomology
