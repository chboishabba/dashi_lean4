import Synthesis.MillenniumBSDOriginalRationalKummerConnecting

/-! Original geometric-point Kummer naturality, at the actual cocycle
value. The compatible completion/closure embedding and the actual
continuous cohomology localization are still separate constructions. -/
namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.OriginalH1
noncomputable section
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable (W : WeierstrassCurve K) [W.IsElliptic]
variable (V : WeierstrassCurve L) [V.IsElliptic]

/-- Transport the ORIGINAL half along the actual geometric point map,
rather than choosing an unrelated local half. -/
def transportOriginalHalf (f : GeometricPoint W →+ GeometricPoint V)
    {P : GeometricPoint W} (Q : GeometricHalfData W P) :
    GeometricHalfData V (f P) :=
  ⟨f Q.half, by rw [← map_nsmul, Q.double_half]⟩

/-- This is the pointwise localization square on the original cocycle,
assuming the real completion-induced map intertwines Galois actions.
No finite square-class substitution and no H1 map assumed. -/
theorem originalKummerCocycleValue_transport
    (f : GeometricPoint W →+ GeometricPoint V)
    (ρ : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup K)
    (hEquiv : ∀ (σ : Field.absoluteGaloisGroup L) (Q : GeometricPoint W),
      f (galoisPointMap W (ρ σ) Q) = galoisPointMap V σ (f Q))
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) (σ : Field.absoluteGaloisGroup L) :
    f ((kummerCocycleValue W hP Q (ρ σ)).1) =
      (kummerCocycleValue V
        (fun τ => by rw [← hEquiv τ P, hP (ρ τ)])
        (transportOriginalHalf W V f Q) σ).1 := by
  change f (galoisPointMap W (ρ σ) Q.half-Q.half) =
    galoisPointMap V σ (f Q.half)-f Q.half
  rw [map_sub,hEquiv]

/-- Restrict the actual additive geometric point map to the genuine E[2]
carrier. No independent torsion map or extra choice is necessary. -/
def transportedTwoTorsion (f : GeometricPoint W →+ GeometricPoint V) :
    EllipticTwoTorsion W →+ EllipticTwoTorsion V where
  toFun P := ⟨f P.1, by rw [← map_nsmul,P.2,map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' P Q := Subtype.ext (map_add f P.1 Q.1)

section ContinuousLocalization
open CategoryTheory
local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (GeometricPoint V) := ⊥
local instance : DiscreteTopology (GeometricPoint V) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion V) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion V) := discreteTopology_bot _

variable (f : GeometricPoint W →+ GeometricPoint V)
variable (ρ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)
variable (hEquiv : ∀ (σ : Field.absoluteGaloisGroup L) (Q : GeometricPoint W),
  f (galoisPointMap W (ρ σ) Q) = galoisPointMap V σ (f Q))

/-- The literal restricted TopRep morphism, on the original torsion
representation and its already-established discrete topology. -/
def transportedTorsionTopRep :
    TopRep.res ρ (ellipticTwoTorsionTopRep W) ⟶ ellipticTwoTorsionTopRep V :=
  TopRep.ofHom ⟨{
    __ := (transportedTwoTorsion W V f).toIntLinearMap
    cont := continuous_of_discreteTopology
  }, by
    intro σ
    ext T
    apply Subtype.ext
    exact hEquiv σ T.1⟩

/-- Full original continuous H1 Kummer naturality, reusing the existing
actualClass_natural theorem rather than reimplementing cohomology.
A compatible completion closure embedding must still produce f,ρ,hEquiv. -/
theorem originalKummerH1_localization
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) :
    ContinuousCohomology.map ρ (transportedTorsionTopRep W V f ρ hEquiv) 1
      (originalKummerH1Class W hP Q) =
    originalKummerH1Class V
      (fun τ => by rw [← hEquiv τ P, hP (ρ τ)])
      (transportOriginalHalf W V f Q) := by
  let hPV : IsGaloisFixedPoint V (f P) :=
    fun τ => by rw [← hEquiv τ P, hP (ρ τ)]
  let QV := transportOriginalHalf W V f Q
  let X := ellipticTwoTorsionTopRep W
  let Y := ellipticTwoTorsionTopRep V
  let F := transportedTorsionTopRep W V f ρ hEquiv
  let c : C(Field.absoluteGaloisGroup K,X) :=
    ⟨kummerCocycleValue W hP Q, originalKummerCocycle_continuous W hP Q⟩
  let d : C(Field.absoluteGaloisGroup L,Y) :=
    ⟨kummerCocycleValue V hPV QV, originalKummerCocycle_continuous V hPV QV⟩
  have hc : Crossed X c := kummerCocycleValue_mul W hP Q
  have hd : Crossed Y d := kummerCocycleValue_mul V hPV QV
  change ContinuousCohomology.map ρ F 1 (actualClass X c hc) =
    actualClass Y d hd
  rw [actualClass_natural X Y ρ F c hc]
  have he : mappedCocycle X Y ρ F c = d := by
    apply ContinuousMap.ext
    intro σ
    apply Subtype.ext
    change f ((kummerCocycleValue W hP Q (ρ σ)).1) =
      (kummerCocycleValue V hPV QV σ).1
    exact originalKummerCocycleValue_transport W V f ρ hEquiv hP Q σ
  have hcongr (c₁ d₁ : C(Field.absoluteGaloisGroup L,Y))
      (hc₁ : Crossed Y c₁) (hd₁ : Crossed Y d₁) (h : c₁=d₁) :
      actualClass Y c₁ hc₁ = actualClass Y d₁ hd₁ := by
    subst d₁
    rfl
  exact hcongr _ _ _ _ he

end ContinuousLocalization

end
end BSDCohomology
