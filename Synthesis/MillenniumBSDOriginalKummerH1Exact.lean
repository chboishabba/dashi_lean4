import Synthesis.MillenniumBSDOriginalHomogeneousH1Exact
import BSDCohomology.EllipticKummerTopRepMapsExact

/-! Original degree-one Kummer maps. The representative exactness is
transported into the actual continuous cohomology class maps. Geometric
doubling surjectivity is explicit, and is already supplied for the
selected CM curve by the existing source owner. -/

namespace BSDCohomology
open WeierstrassCurve CategoryTheory DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _

abbrev pointRep := geometricPointTopRep W
abbrev torsionRep := ellipticTwoTorsionTopRep W
abbrev idGal := ContinuousMonoidHom.id (Field.absoluteGaloisGroup K)

def originalInclusionH1 : EllipticTwoTorsionH1 W ⟶ EllipticPointH1 W :=
  ContinuousCohomology.map idGal (twoTorsionInclusionTopRep W) 1

def originalDoublingH1 : EllipticPointH1 W ⟶ EllipticPointH1 W :=
  ContinuousCohomology.map idGal (geometricDoublingTopRep W) 1

/-- Exactness at the actual torsion H1, with the original fixed-point
Kummer values. This is not yet rational-point descent or localization. -/
theorem originalInclusionH1_zero_iff_kummer (x : EllipticTwoTorsionH1 W) :
    originalInclusionH1 W x = 0 ↔
      ∃ P : GeometricPoint W, ∃ hP : IsGaloisFixedPoint W P,
        ∃ Q : GeometricHalfData W P, x = originalKummerH1Class W hP Q := by
  obtain ⟨c,hc,hx⟩ := actualClass_surjective (torsionRep W) x
  let d := mappedCocycle (torsionRep W) (pointRep W) idGal
    (twoTorsionInclusionTopRep W) c
  have hd := mappedCocycle_crossed (torsionRep W) (pointRep W) idGal
    (twoTorsionInclusionTopRep W) c hc
  have hmap : originalInclusionH1 W x = actualClass (pointRep W) d hd := by
    rw [← hx]
    exact actualClass_natural (torsionRep W) (pointRep W) idGal
      (twoTorsionInclusionTopRep W) c hc
  rw [hmap,actualClass_zero_iff_coboundary]
  change (∃ Q : GeometricPoint W, ∀ σ, (c σ).1 = kummerDifference W Q σ) ↔ _
  rw [torsion_coboundary_iff_kummer W c]
  constructor
  · rintro ⟨P,hP,Q,hQ⟩
    refine ⟨P,hP,Q,?_⟩
    rw [← hx]
    unfold originalKummerH1Class
    have he : c = ⟨kummerCocycleValue W hP Q,
        originalKummerCocycle_continuous W hP Q⟩ := ContinuousMap.ext hQ
    subst c
    rfl
  · rintro ⟨P,hP,Q,hQ⟩
    have he : actualClass (torsionRep W) c hc =
        originalKummerH1Class W hP Q := hx.trans hQ
    unfold originalKummerH1Class at he
    obtain ⟨T,hT⟩ := (actualClass_eq_iff_coboundary (torsionRep W)
      c ⟨kummerCocycleValue W hP Q,originalKummerCocycle_continuous W hP Q⟩
      hc (kummerCocycleValue_mul W hP Q)).mp he
    -- Changing the chosen half by the literal torsion point realizes
    -- the signed coboundary; the rational target stays fixed.
    let Q' : GeometricHalfData W P := ⟨Q.half+T.1,by
      rw [nsmul_add,Q.double_eq,T.2,add_zero]⟩
    refine ⟨P,hP,Q',fun σ => ?_⟩
    apply Subtype.ext
    have hval := congrArg Subtype.val (hT σ)
    change (c σ).1-kummerDifference W Q.half σ =
      galoisPointMap W σ T.1-T.1 at hval
    change (c σ).1=kummerDifference W (Q.half+T.1) σ
    unfold kummerDifference at *
    rw [map_add]
    abel_nf at hval ⊢
    exact sub_eq_iff_eq_add.mp hval

/-- Exactness at the actual point H1: if doubling kills the class, the
reverse lift is obtained by subtracting a genuine geometric half
coboundary. The remaining hypothesis is geometric doubling onto. -/
theorem originalDoublingH1_zero_iff_inclusion
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (x : EllipticPointH1 W) :
    originalDoublingH1 W x = 0 ↔
      ∃ y : EllipticTwoTorsionH1 W, originalInclusionH1 W y = x := by
  constructor
  · intro hz
    obtain ⟨c,hc,hx⟩ := actualClass_surjective (pointRep W) x
    rw [← hx, originalDoublingH1, actualClass_natural] at hz
    obtain ⟨P,hP⟩ := (actualClass_zero_iff_coboundary _ _ _).mp hz
    change ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ at hP
    obtain ⟨Q,hQ⟩ := hs P
    let d : C(Field.absoluteGaloisGroup K,torsionRep W) :=
      ⟨liftDoubleCoboundary W c P Q hQ hP,
        liftDoubleCoboundary_continuous W c c.continuous P Q hQ hP⟩
    have hd : Crossed (torsionRep W) d :=
      liftDouble_crossed W c hc P Q hQ hP
    refine ⟨actualClass (torsionRep W) d hd,?_⟩
    rw [originalInclusionH1,actualClass_natural,← hx]
    symm
    apply (actualClass_eq_iff_coboundary _ _ _ _ _).mpr
    refine ⟨Q,fun σ => ?_⟩
    change c σ-(c σ-kummerDifference W Q σ)=kummerDifference W Q σ
    abel
  · rintro ⟨y,hy⟩
    obtain ⟨d,hd,hdy⟩ := actualClass_surjective (torsionRep W) y
    rw [← hy,← hdy,originalInclusionH1,actualClass_natural,
      originalDoublingH1,actualClass_natural]
    apply (actualClass_zero_iff_coboundary _ _ _).mpr
    refine ⟨0,fun σ => ?_⟩
    change (2 : ℕ) • (d σ).1 = galoisPointMap W σ 0-0
    rw [(d σ).2,map_zero,sub_zero]

end
end BSDCohomology
