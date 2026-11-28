import BSDCohomology.EllipticFixedPointDescentExact
import Synthesis.MillenniumBSDOriginalKummerH1Exact
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The original fixed-point descent and degree-one Kummer class give the
connecting map on the base-field point group. The cohomological API still
requires the compatible isolated Mathlib build; no new H1 object. -/
namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _

theorem originalKummerH1_half_independent
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q R : GeometricHalfData W P) :
    originalKummerH1Class W hP Q = originalKummerH1Class W hP R := by
  unfold originalKummerH1Class
  apply (actualClass_eq_iff_coboundary _ _ _ _ _).mpr
  refine ⟨halfDifferenceTwoTorsion W R Q,fun σ => ?_⟩
  apply Subtype.ext
  change (galoisPointMap W σ Q.half-Q.half)-
    (galoisPointMap W σ R.half-R.half) =
      galoisPointMap W σ (Q.half-R.half)-(Q.half-R.half)
  rw [map_sub]
  abel

theorem originalKummerH1_zero_iff_fixed_half
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) :
    originalKummerH1Class W hP Q = 0 ↔
      ∃ R : GeometricHalfData W P, IsGaloisFixedPoint W R.half := by
  constructor
  · intro hz
    unfold originalKummerH1Class at hz
    obtain ⟨T,hT⟩ := (actualClass_zero_iff_coboundary _ _ _).mp hz
    let R : GeometricHalfData W P := ⟨Q.half-T.1,by
      rw [nsmul_sub,Q.double_half,T.2,sub_zero]⟩
    refine ⟨R,fun σ => ?_⟩
    have ht := congrArg Subtype.val (hT σ)
    change galoisPointMap W σ Q.half-Q.half =
      galoisPointMap W σ T.1-T.1 at ht
    change galoisPointMap W σ (Q.half-T.1)=Q.half-T.1
    rw [map_sub]
    calc
      galoisPointMap W σ Q.half - galoisPointMap W σ T.1 =
        (galoisPointMap W σ Q.half-Q.half) + Q.half -
          galoisPointMap W σ T.1 := by abel
      _ = Q.half-T.1 := by rw [ht]; abel
  · rintro ⟨R,hR⟩
    rw [originalKummerH1_half_independent W hP Q R]
    unfold originalKummerH1Class
    apply (actualClass_zero_iff_coboundary _ _ _).mpr
    refine ⟨0,fun σ => ?_⟩
    apply Subtype.ext
    change galoisPointMap W σ R.half-R.half =
      galoisPointMap W σ 0-0
    rw [hR σ,sub_self,map_zero,sub_zero]

/-- Choose a geometric half using the existing geometric doubling theorem. -/
def rationalKummerClass
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (P : BasePoint W) : EllipticTwoTorsionH1 W :=
  originalKummerH1Class W (basePointToGeometric_fixed W P)
    ⟨Classical.choose (hs (basePointToGeometric W P)),
      Classical.choose_spec (hs (basePointToGeometric W P))⟩

theorem rationalKummerClass_zero_iff_double
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (P : BasePoint W) :
    rationalKummerClass W hs P = 0 ↔ ∃ R : BasePoint W, (2 : ℕ) • R=P := by
  unfold rationalKummerClass
  rw [originalKummerH1_zero_iff_fixed_half]
  constructor
  · rintro ⟨Q,hQ⟩
    obtain ⟨R,hR⟩ := (geometricFixed_iff_basePoint W Q.half).mp hQ
    refine ⟨R,basePointToGeometric_injective W ?_⟩
    rw [map_nsmul,hR,Q.double_half]
  · rintro ⟨R,hR⟩
    refine ⟨⟨basePointToGeometric W R,?_⟩,basePointToGeometric_fixed W R⟩
    rw [← map_nsmul,hR]

theorem originalInclusionH1_zero_iff_rationalKummer
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (x : EllipticTwoTorsionH1 W) :
    originalInclusionH1 W x = 0 ↔
      ∃ P : BasePoint W, rationalKummerClass W hs P=x := by
  rw [originalInclusionH1_zero_iff_kummer]
  constructor
  · rintro ⟨P,hP,Q,hQ⟩
    obtain ⟨R,hR⟩ := (geometricFixed_iff_basePoint W P).mp hP
    subst P
    refine ⟨R,?_⟩
    rw [hQ]
    unfold rationalKummerClass
    exact originalKummerH1_half_independent W _ _ Q
  · rintro ⟨P,hP⟩
    exact ⟨basePointToGeometric W P,basePointToGeometric_fixed W P,
      ⟨Classical.choose (hs (basePointToGeometric W P)),
        Classical.choose_spec (hs (basePointToGeometric W P))⟩,hP.symm⟩


/-- The original Kummer map is additive without choosing an additive
section of geometric doubling. Half-choice independence is essential. -/
theorem rationalKummerClass_add
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (P R : BasePoint W) :
    rationalKummerClass W hs (P+R) =
      rationalKummerClass W hs P+rationalKummerClass W hs R := by
  let Q₁ : GeometricHalfData W (basePointToGeometric W P) :=
    ⟨Classical.choose (hs (basePointToGeometric W P)),
      Classical.choose_spec (hs (basePointToGeometric W P))⟩
  let Q₂ : GeometricHalfData W (basePointToGeometric W R) :=
    ⟨Classical.choose (hs (basePointToGeometric W R)),
      Classical.choose_spec (hs (basePointToGeometric W R))⟩
  let Q : GeometricHalfData W (basePointToGeometric W (P+R)) :=
    ⟨Q₁.half+Q₂.half,by rw [nsmul_add,Q₁.double_half,Q₂.double_half,map_add]⟩
  have he : rationalKummerClass W hs (P+R) =
      originalKummerH1Class W (basePointToGeometric_fixed W (P+R)) Q := by
    unfold rationalKummerClass
    exact originalKummerH1_half_independent W _ _ Q
  rw [he]
  let c₁ : C(Field.absoluteGaloisGroup K,torsionRep W) :=
    ⟨kummerCocycleValue W (basePointToGeometric_fixed W P) Q₁,
      originalKummerCocycle_continuous W _ Q₁⟩
  let c₂ : C(Field.absoluteGaloisGroup K,torsionRep W) :=
    ⟨kummerCocycleValue W (basePointToGeometric_fixed W R) Q₂,
      originalKummerCocycle_continuous W _ Q₂⟩
  have hc₁ : Crossed (torsionRep W) c₁ := kummerCocycleValue_mul W _ Q₁
  have hc₂ : Crossed (torsionRep W) c₂ := kummerCocycleValue_mul W _ Q₂
  change actualClass (torsionRep W)
    ⟨kummerCocycleValue W (basePointToGeometric_fixed W (P+R)) Q,
     originalKummerCocycle_continuous W _ Q⟩
    (kummerCocycleValue_mul W _ Q) =
      actualClass (torsionRep W) c₁ hc₁+actualClass (torsionRep W) c₂ hc₂
  rw [← actualClass_add (torsionRep W) c₁ c₂ hc₁ hc₂]
  have hco : (⟨kummerCocycleValue W (basePointToGeometric_fixed W (P+R)) Q,
     originalKummerCocycle_continuous W _ Q⟩ :
       C(Field.absoluteGaloisGroup K,torsionRep W)) = c₁+c₂ := by
    ext σ
    apply Subtype.ext
    change galoisPointMap W σ (Q₁.half+Q₂.half)-(Q₁.half+Q₂.half) =
      (galoisPointMap W σ Q₁.half-Q₁.half)+(galoisPointMap W σ Q₂.half-Q₂.half)
    rw [map_add]
    abel
  -- The crossed-law proof is a Prop, so dependent substitution does
  -- not impose a separate proof-identity obligation.
  have hcongr (c d : C(Field.absoluteGaloisGroup K,torsionRep W))
      (hc : Crossed (torsionRep W) c) (hd : Crossed (torsionRep W) d)
      (h : c=d) : actualClass (torsionRep W) c hc =
        actualClass (torsionRep W) d hd := by
    subst d
    rfl
  exact hcongr _ _ _ _ hco

def rationalKummerHom
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q)) :
    BasePoint W →+ EllipticTwoTorsionH1 W where
  toFun := rationalKummerClass W hs
  map_zero' := (rationalKummerClass_zero_iff_double W hs 0).mpr ⟨0,by simp⟩
  map_add' := rationalKummerClass_add W hs

abbrev rationalDoubles : AddSubgroup (BasePoint W) :=
  (nsmulAddMonoidHom (α := BasePoint W) 2).range

theorem rationalKummerHom_ker
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q)) :
    (rationalKummerHom W hs).ker = rationalDoubles W := by
  ext P
  exact rationalKummerClass_zero_iff_double W hs P

/-- Literal E(K)/2E(K) map into the ORIGINAL H1, with the actual
first isomorphism theorem, not a finite cardinality comparison. -/
def rationalKummerQuotientHom
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q)) :
    (BasePoint W ⧸ rationalDoubles W) →+ EllipticTwoTorsionH1 W :=
  QuotientAddGroup.lift (rationalDoubles W) (rationalKummerHom W hs)
    (by rw [rationalKummerHom_ker])

theorem rationalKummerQuotient_injective
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q)) :
    Function.Injective (rationalKummerQuotientHom W hs) := by
  intro a b
  refine Quotient.inductionOn₂' a b ?_
  intro P R h
  change rationalKummerHom W hs P = rationalKummerHom W hs R at h
  apply Quotient.sound'
  rw [QuotientAddGroup.leftRel_apply,← rationalKummerHom_ker W hs]
  change rationalKummerHom W hs (-P+R)=0
  rw [map_add,map_neg,h,neg_add_cancel]


end
end BSDCohomology
