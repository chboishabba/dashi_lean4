import Synthesis.MillenniumBSDClosureNormalRestrictionExact

/-!
Literal iterated base-change of the same elliptic curve, followed by the
existing continuous H1 naturality theorem. No selected square-class model.
All constructions use the structural K-algebra of L; the actual family
of number-field completions and the doubling-surjectivity source remain
separate inputs. Classical Kummer naturality, DASHI original-carrier weld.
-/
namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.OriginalH1
noncomputable section
universe u v

private def pointCurveEquiv {F : Type*} [Field F]
    (C D : WeierstrassCurve F) [C.IsElliptic] [D.IsElliptic]
    (h : C = D) : C.toAffine.Point ≃+ D.toAffine.Point := by
  subst D
  exact AddEquiv.refl _

private theorem pointCurveEquiv_zero {F : Type*} [Field F]
    (C D : WeierstrassCurve F) [C.IsElliptic] [D.IsElliptic]
    (h : C=D) : pointCurveEquiv C D h 0=0 :=
  map_zero _

private theorem pointCurveEquiv_some {F : Type*} [Field F]
    (C D : WeierstrassCurve F) [C.IsElliptic] [D.IsElliptic]
    (h : C=D) {x y : F} (hc : C.toAffine.Nonsingular x y)
    (hd : D.toAffine.Nonsingular x y) :
    pointCurveEquiv C D h (.some hc) = .some hd := by
  subst D
  rfl

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable [Algebra K L] [Algebra K (AlgebraicClosure L)]
variable [IsScalarTower K L (AlgebraicClosure L)]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- All five Weierstrass coefficients commute with structural base
change. This is a theorem of literal equality, not an arbitrary isogeny. -/
theorem iteratedCurveBaseChange :
    (W⁄(AlgebraicClosure L)) = ((W⁄L)⁄(AlgebraicClosure L)) := by
  symm
  change (W.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L)) =
    W.map (algebraMap K (AlgebraicClosure L))
  rw [WeierstrassCurve.map_map,← IsScalarTower.algebraMap_eq]

theorem localBaseChange_id : (W⁄L) = ((W⁄L)⁄L) := by
  symm
  change (W⁄L).map (algebraMap L L) = W⁄L
  simp

def iteratedLocalPointEquiv :
    LocalClosurePoint (L:=L) W ≃+ GeometricPoint (W⁄L) :=
  pointCurveEquiv _ _ (iteratedCurveBaseChange (L:=L) W)

def iteratedLocalBasePointEquiv :
    (W⁄L).toAffine.Point ≃+ BasePoint (W⁄L) :=
  pointCurveEquiv _ _ (localBaseChange_id (L:=L) W)

def completionPointMap :
    GeometricPoint W →+ GeometricPoint (W⁄L) :=
  (iteratedLocalPointEquiv (L:=L) W).toAddMonoidHom.comp
    (closureGeometricPointMap W (chooseClosureEmbedding (K:=K) (L:=L)))

def completionBasePointMap :
    BasePoint W →+ BasePoint (W⁄L) :=
  (iteratedLocalBasePointEquiv (L:=L) W).toAddMonoidHom.comp
    (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId K L))

/-- The literal coordinate map intertwines the local automorphism
after iterated base-change; both affine coordinates and zero retained. -/
theorem iteratedLocalPointEquiv_action
    (σ : Field.absoluteGaloisGroup L) (P : LocalClosurePoint (L:=L) W) :
    iteratedLocalPointEquiv (L:=L) W (localClosureAction W σ P) =
      galoisPointMap (W⁄L) σ (iteratedLocalPointEquiv (L:=L) W P) := by
  cases P with
  | zero =>
    simp [localClosureAction,galoisPointMap,iteratedLocalPointEquiv]
  | some x y h =>
    let C := W⁄(AlgebraicClosure L)
    let D := (W⁄L)⁄(AlgebraicClosure L)
    have hd : D.toAffine.Nonsingular x y :=
      iteratedCurveBaseChange (L:=L) W ▸ h
    have hcd : iteratedLocalPointEquiv (L:=L) W (.some h) = .some hd :=
      pointCurveEquiv_some C D _ h hd
    rw [hcd]
    simp only [localClosureAction,galoisPointMap,
      WeierstrassCurve.Affine.Point.map_some]
    apply pointCurveEquiv_some

theorem completionPointMap_equivariant
    (σ : Field.absoluteGaloisGroup L) (P : GeometricPoint W) :
    completionPointMap (L:=L) W
      (galoisPointMap W
        (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)) σ) P) =
    galoisPointMap (W⁄L) σ (completionPointMap (L:=L) W P) := by
  change iteratedLocalPointEquiv (L:=L) W
    (closureGeometricPointMap W _
      (galoisPointMap W (closureRestrictionHom
        (chooseClosureEmbedding (K:=K) (L:=L)) σ) P))=_
  rw [chosenClosurePointMap_equivariant W σ P]
  exact iteratedLocalPointEquiv_action W σ _

/-- The base-field and geometric-point squares commute on the original
rational point. This is not merely equality after passing to cohomology. -/
theorem completionPointMap_basePoint (P : BasePoint W) :
    completionPointMap (L:=L) W (basePointToGeometric W P) =
      basePointToGeometric (W⁄L) (completionBasePointMap (L:=L) W P) := by
  change iteratedLocalPointEquiv (L:=L) W
    (closureGeometricPointMap W (chooseClosureEmbedding (K:=K) (L:=L))
      (basePointToGeometric W P))=_
  rw [closureGeometricPointMap_basePoint]
  cases P with
  | zero =>
    simp [completionBasePointMap,basePointToGeometric,
      iteratedLocalPointEquiv,iteratedLocalBasePointEquiv]
  | some x y h =>
    let Pₗ := WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
      (Algebra.ofId K L) (.some h)
    have hp : (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) :=
      (W.toAffine.baseChange_nonsingular x y (Algebra.ofId K L).injective).mpr h
    have hₗ : ((W⁄L)⁄L).toAffine.Nonsingular
        (algebraMap K L x) (algebraMap K L y) :=
      localBaseChange_id (L:=L) W ▸ hp
    have hm : iteratedLocalBasePointEquiv (L:=L) W Pₗ = .some hₗ := by
      change pointCurveEquiv _ _ _ (WeierstrassCurve.Affine.Point.map
        (W' := W.toAffine) (Algebra.ofId K L) (.some h))=_
      rw [WeierstrassCurve.Affine.Point.map_some]
      exact pointCurveEquiv_some _ _ _ _ _
    change iteratedLocalPointEquiv (L:=L) W
        (WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
          (Algebra.ofId K (AlgebraicClosure L)) (.some h)) =
      basePointToGeometric (W⁄L) (iteratedLocalBasePointEquiv (L:=L) W Pₗ)
    rw [hm]
    simp only [basePointToGeometric,WeierstrassCurve.Affine.Point.map_some]
    have hxy (z : K) :
        algebraMap L (AlgebraicClosure L) (algebraMap K L z) =
          algebraMap K (AlgebraicClosure L) z :=
      (IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) z).symm
    simp only [Algebra.ofId_apply,hxy]
    apply pointCurveEquiv_some

section H1
open CategoryTheory
local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (GeometricPoint (W⁄L)) := ⊥
local instance : DiscreteTopology (GeometricPoint (W⁄L)) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion (W⁄L)) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion (W⁄L)) := discreteTopology_bot _

def actualCompletionTorsionRep :
    TopRep.res (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)))
      (ellipticTwoTorsionTopRep W) ⟶ ellipticTwoTorsionTopRep (W⁄L) :=
  transportedTorsionTopRep W (W⁄L) (completionPointMap (L:=L) W)
    _ (completionPointMap_equivariant (L:=L) W)

def actualCompletionH1 (x : EllipticTwoTorsionH1 W) :
    EllipticTwoTorsionH1 (W⁄L) :=
  ContinuousCohomology.map
    (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)))
    (actualCompletionTorsionRep (L:=L) W) 1 x

/-- Consume the actual cochain naturality and half-independence. The
local image is exactly the Kummer class of the actual base-changed point. -/
theorem actualCompletion_rationalKummer
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hsL : Function.Surjective (fun Q : GeometricPoint (W⁄L) => (2:ℕ) • Q))
    (P : BasePoint W) :
    actualCompletionH1 (L:=L) W (rationalKummerClass W hsK P) =
      rationalKummerClass (W⁄L) hsL (completionBasePointMap (L:=L) W P) := by
  let Q : GeometricHalfData W (basePointToGeometric W P) :=
    ⟨Classical.choose (hsK (basePointToGeometric W P)),
      Classical.choose_spec (hsK (basePointToGeometric W P))⟩
  let f := completionPointMap (L:=L) W
  let ρ := continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L))
  let he := completionPointMap_equivariant (L:=L) W
  let hP := basePointToGeometric_fixed W P
  let QL := transportOriginalHalf W (W⁄L) f Q
  have hn := originalKummerH1_localization W (W⁄L) f ρ he hP Q
  change ContinuousCohomology.map ρ (transportedTorsionTopRep W (W⁄L) f ρ he) 1
    (originalKummerH1Class W hP Q) = _
  rw [hn]
  have hb : f (basePointToGeometric W P) =
      basePointToGeometric (W⁄L) (completionBasePointMap (L:=L) W P) :=
    completionPointMap_basePoint W P
  have hchoice (P₁ P₂ : GeometricPoint (W⁄L))
      (h₁ : IsGaloisFixedPoint (W⁄L) P₁)
      (h₂ : IsGaloisFixedPoint (W⁄L) P₂)
      (Q₁ : GeometricHalfData (W⁄L) P₁)
      (Q₂ : GeometricHalfData (W⁄L) P₂)
      (h : P₁=P₂) :
      originalKummerH1Class (W⁄L) h₁ Q₁ =
        originalKummerH1Class (W⁄L) h₂ Q₂ := by
    subst P₂
    exact originalKummerH1_half_independent (W⁄L) h₁ Q₁ Q₂
  unfold rationalKummerClass
  exact hchoice _ _ _ _ _ _ hb

end H1
end
end BSDCohomology
