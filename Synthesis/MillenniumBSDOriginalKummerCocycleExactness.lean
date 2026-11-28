import BSDCohomology.EllipticKummerCocycleAlgebraExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
import Synthesis.MillenniumBSDCMGeometricKummerContinuousH1Exact
import Mathlib.Tactic

/-! Degree-one Kummer exactness on the original geometric point action.
Use the existing point carrier and Kummer differences, not a replacement
H1 object. The two exactness assertions below hold at representatives.
The comparison with the general Mathlib homogeneous-cochain quotient,
completion maps, and the analytic rank theorem remain separate. -/

namespace BSDCohomology

open WeierstrassCurve
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The actual crossed-cocycle equation for the existing point action. -/
def IsPointCrossed (c : Field.absoluteGaloisGroup K → GeometricPoint W) : Prop :=
  ∀ σ τ, c (σ * τ) = c σ + galoisPointMap W σ (c τ)

theorem kummerDifference_crossed (Q : GeometricPoint W) :
    IsPointCrossed W (kummerDifference W Q) := by
  intro σ τ
  unfold kummerDifference
  rw [galoisPointMap_mul, map_sub]
  abel

theorem kummerDifference_double (Q : GeometricPoint W)
    (σ : Field.absoluteGaloisGroup K) :
    (2 : ℕ) • kummerDifference W Q σ =
      kummerDifference W ((2 : ℕ) • Q) σ := by
  unfold kummerDifference
  rw [nsmul_sub, galoisPointMap_double]

/-- For nontrivial E[2] action, the two choices need not agree pointwise:
their difference is precisely the actual two-torsion coboundary. -/
theorem half_change_is_coboundary
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q₁ Q₂ : GeometricHalfData W P) (σ : Field.absoluteGaloisGroup K) :
    (kummerCocycleValue W hP Q₂ σ).1 -
      (kummerCocycleValue W hP Q₁ σ).1 =
        kummerDifference W (halfDifferenceTwoTorsion W Q₁ Q₂).1 σ := by
  simp only [kummerCocycleValue_coe]
  change (galoisPointMap W σ Q₂.half - Q₂.half) -
    (galoisPointMap W σ Q₁.half - Q₁.half) =
      galoisPointMap W σ (Q₂.half-Q₁.half) - (Q₂.half-Q₁.half)
  rw [map_sub]
  abel

/-- If a literal E[2]-valued cocycle is an Ebar-coboundary,
the double of its coboundary witness is genuinely Galois-fixed. -/
theorem fixed_double_of_torsion_coboundary
    (c : Field.absoluteGaloisGroup K → EllipticTwoTorsion W)
    (Q : GeometricPoint W)
    (h : ∀ σ, (c σ).1 = kummerDifference W Q σ) :
    IsGaloisFixedPoint W ((2 : ℕ) • Q) := by
  intro σ
  have ht := (mem_ellipticTwoTorsion_iff W (c σ).1).mp (c σ).2
  rw [h σ, kummerDifference_double] at ht
  exact sub_eq_zero.mp ht

/-- Literal kernel of H1 inclusion at cocycle representatives:
E[2]-valued coboundaries in Ebar are exactly geometric Kummer values. -/
theorem torsion_coboundary_iff_kummer
    (c : Field.absoluteGaloisGroup K → EllipticTwoTorsion W) :
    (∃ Q : GeometricPoint W, ∀ σ, (c σ).1 = kummerDifference W Q σ) ↔
      ∃ P : GeometricPoint W, ∃ hP : IsGaloisFixedPoint W P,
        ∃ Q : GeometricHalfData W P, ∀ σ, c σ = kummerCocycleValue W hP Q σ := by
  constructor
  · rintro ⟨Q,hQ⟩
    let P := (2 : ℕ) • Q
    have hP : IsGaloisFixedPoint W P :=
      fixed_double_of_torsion_coboundary W c Q hQ
    refine ⟨P,hP,⟨Q,rfl⟩,fun σ => ?_⟩
    apply Subtype.ext
    exact hQ σ
  · rintro ⟨P,hP,Q,hQ⟩
    exact ⟨Q.half,fun σ => congrArg Subtype.val (hQ σ)⟩

/-- Remove the actual half-coboundary from a cocycle whose double is
a coboundary. This is the reverse solve for the H1[2] lift. -/
def removeHalfCoboundary
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (Q : GeometricPoint W) (σ : Field.absoluteGaloisGroup K) :
    GeometricPoint W :=
  c σ - kummerDifference W Q σ

theorem removeHalf_crossed
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c) (Q : GeometricPoint W) :
    IsPointCrossed W (removeHalfCoboundary W c Q) := by
  intro σ τ
  unfold removeHalfCoboundary
  rw [hc σ τ, kummerDifference_crossed W Q σ τ, map_sub]
  abel

theorem removeHalf_is_torsion
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ : Field.absoluteGaloisGroup K) :
    removeHalfCoboundary W c Q σ ∈ EllipticTwoTorsion W := by
  rw [mem_ellipticTwoTorsion_iff]
  unfold removeHalfCoboundary
  rw [nsmul_sub, h σ, kummerDifference_double, hQ, sub_self]

/-- The lifted function lives in the existing literal E[2] subgroup. -/
def liftDoubleCoboundary
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ : Field.absoluteGaloisGroup K) : EllipticTwoTorsion W :=
  ⟨removeHalfCoboundary W c Q σ,removeHalf_is_torsion W c P Q hQ h σ⟩

theorem liftDouble_crossed
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ τ : Field.absoluteGaloisGroup K) :
    liftDoubleCoboundary W c P Q hQ h (σ*τ) =
      liftDoubleCoboundary W c P Q hQ h σ +
      galoisTwoTorsionMap W σ (liftDoubleCoboundary W c P Q hQ h τ) := by
  apply Subtype.ext
  exact removeHalf_crossed W c hc Q σ τ

/-- Exactness at the point-cohomology two-kernel, on representatives,
using the actual geometric surjectivity hypothesis. -/
theorem double_coboundary_iff_torsion_lift
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c) :
    (∃ P : GeometricPoint W, ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ) ↔
      ∃ d : Field.absoluteGaloisGroup K → EllipticTwoTorsion W,
        (∀ σ τ, d (σ*τ) = d σ + galoisTwoTorsionMap W σ (d τ)) ∧
        ∃ Q : GeometricPoint W, ∀ σ, c σ = (d σ).1 + kummerDifference W Q σ := by
  constructor
  · rintro ⟨P,h⟩
    obtain ⟨Q,hQ⟩ := hs P
    refine ⟨liftDoubleCoboundary W c P Q hQ h,
      liftDouble_crossed W c hc P Q hQ h,Q,fun σ => ?_⟩
    change c σ = c σ - kummerDifference W Q σ + kummerDifference W Q σ
    abel
  · rintro ⟨d,hd,Q,hQ⟩
    refine ⟨(2 : ℕ) • Q,fun σ => ?_⟩
    rw [hQ σ,nsmul_add,(mem_ellipticTwoTorsion_iff W (d σ).1).mp (d σ).2,
      zero_add,kummerDifference_double]

end
end BSDCohomology

namespace Synthesis.Millennium.BSD
open BSDCohomology
noncomputable section

/-- Instantiate the reverse lift on the existing actual selected curve.
No divisibility premise remains on this curve. -/
theorem cmOriginalDoubleCoboundary_iff_torsion_lift
    (c : Field.absoluteGaloisGroup ℚ → GeometricPoint cmWeierstrass)
    (hc : IsPointCrossed cmWeierstrass c) :
    (∃ P : GeometricPoint cmWeierstrass,
      ∀ σ, (2 : ℕ) • c σ = kummerDifference cmWeierstrass P σ) ↔
      ∃ d : Field.absoluteGaloisGroup ℚ → EllipticTwoTorsion cmWeierstrass,
        (∀ σ τ, d (σ*τ) = d σ + galoisTwoTorsionMap cmWeierstrass σ (d τ)) ∧
        ∃ Q : GeometricPoint cmWeierstrass,
          ∀ σ, c σ = (d σ).1 + kummerDifference cmWeierstrass Q σ :=
  double_coboundary_iff_torsion_lift cmWeierstrass
    cmSelectedGeometricDoubling_onto c hc

end
end Synthesis.Millennium.BSD
