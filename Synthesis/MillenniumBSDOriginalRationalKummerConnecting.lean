import BSDCohomology.EllipticFixedPointDescentExact
import Synthesis.MillenniumBSDOriginalKummerH1Exact

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

end
end BSDCohomology
