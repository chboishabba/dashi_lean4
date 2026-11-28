import BSDCohomology.EllipticKummerCocycleAlgebraExact
import Mathlib.FieldTheory.Galois.Infinite

/-!
Rational fixed-point descent in characteristic zero on the original
geometric elliptic group. This uses the pinned Mathlib infinite Galois
fixed-field theorem, independently of continuous cohomology.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

abbrev BasePoint := (W⁄K).toAffine.Point

def basePointToGeometric : BasePoint W →+ GeometricPoint W :=
  WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
    (Algebra.ofId K (AlgebraicClosure K))

theorem basePointToGeometric_injective :
    Function.Injective (basePointToGeometric W) :=
  WeierstrassCurve.Affine.Point.map_injective (W' := W.toAffine)
    (Algebra.ofId K (AlgebraicClosure K))

theorem basePointToGeometric_fixed (P : BasePoint W) :
    IsGaloisFixedPoint W (basePointToGeometric W P) := by
  intro σ
  cases P with
  | zero => rfl
  | some x y h =>
    simp [basePointToGeometric, galoisPointMap,
      WeierstrassCurve.Affine.Point.map_some, AlgEquiv.commutes]

/-- Every fixed geometric point descends, including the zero point.
For an affine point, use the actual coordinate equalities extracted
from the point equality, then reflect nonsingularity along base change. -/
theorem geometricFixed_iff_basePoint (P : GeometricPoint W) :
    IsGaloisFixedPoint W P ↔ ∃ Q : BasePoint W, basePointToGeometric W Q = P := by
  constructor
  · intro hP
    cases P with
    | zero => exact ⟨0,rfl⟩
    | some x y h =>
      have hx : ∀ σ : Field.absoluteGaloisGroup K, σ x = x := by
        intro σ
        have he := hP σ
        simp only [galoisPointMap, WeierstrassCurve.Affine.Point.map_some,
          WeierstrassCurve.Affine.Point.some.injEq] at he
        exact he.1
      have hy : ∀ σ : Field.absoluteGaloisGroup K, σ y = y := by
        intro σ
        have he := hP σ
        simp only [galoisPointMap, WeierstrassCurve.Affine.Point.map_some,
          WeierstrassCurve.Affine.Point.some.injEq] at he
        exact he.2
      obtain ⟨a,ha⟩ :=
        (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) x).mpr hx
      obtain ⟨b,hb⟩ :=
        (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) y).mpr hy
      let f := Algebra.ofId K (AlgebraicClosure K)
      have hab : (W⁄K).toAffine.Nonsingular a b :=
        (W.toAffine.baseChange_nonsingular a b f.injective).mp
          (by simpa [f,ha,hb] using h)
      refine ⟨WeierstrassCurve.Affine.Point.some hab,?_⟩
      simp [basePointToGeometric, WeierstrassCurve.Affine.Point.map_some,ha,hb]
  · rintro ⟨Q,rfl⟩
    exact basePointToGeometric_fixed W Q

def fixedPointSubgroup : AddSubgroup (GeometricPoint W) where
  carrier := {P | IsGaloisFixedPoint W P}
  zero_mem' := fun σ => map_zero (galoisPointMap W σ)
  add_mem' := by
    intro P Q hP hQ σ
    rw [map_add,hP σ,hQ σ]
  neg_mem' := by
    intro P hP σ
    rw [map_neg,hP σ]

def basePointToFixed : BasePoint W →+ fixedPointSubgroup W where
  toFun P := ⟨basePointToGeometric W P,basePointToGeometric_fixed W P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

def basePointEquivFixed : BasePoint W ≃+ fixedPointSubgroup W :=
  AddEquiv.ofBijective (basePointToFixed W) ⟨by
    intro P Q h
    exact basePointToGeometric_injective W (congrArg Subtype.val h),by
    intro P
    obtain ⟨Q,hQ⟩ := (geometricFixed_iff_basePoint W P.1).mp P.2
    exact ⟨Q,Subtype.ext hQ⟩⟩

@[simp] theorem basePointEquivFixed_val (P : BasePoint W) :
    (basePointEquivFixed W P).1 = basePointToGeometric W P := rfl

end
end BSDCohomology
