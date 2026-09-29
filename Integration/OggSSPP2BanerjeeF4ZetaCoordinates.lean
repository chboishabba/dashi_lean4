import Mathlib
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

/-!
# An actual F4 zeta coordinate for Banerjee's special fibre

This is NOT the characteristic-zero Eisenstein scalar zeta.  We select an
actual element zeta of F4 distinct from 0 and 1 and prove:

* zeta^3 = 1;
* zeta^2 + zeta + 1 = 0;
* zeta^2 + zeta = 1, by characteristic two;
* its square is the other Frobenius-conjugate root;
* y=zeta and y=zeta^2 solve y^2+y=1;
* [zeta:zeta^2:0] does NOT lie on the projective cubic, whereas [0:1:0] does.

The projective triple is distinct from the ternary ROOT LABEL carrier
{0,zeta,zeta^2} and from the six nonzero-x affine points it indexes.
-/

namespace Integration.OggSSPP2BanerjeeF4ZetaCoordinates

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

theorem f4_cardinality :
    Fintype.card B.F4 = 4 := by
  simpa [B.F4] using GaloisField.card 2 2 (by decide)

theorem exists_nontrivial_f4_element :
    ∃ z : B.F4, z ≠ 0 ∧ z ≠ 1 := by
  classical
  by_contra h
  have cover : (Finset.univ : Finset B.F4) ⊆ ({0, 1} : Finset B.F4) := by
    intro z hz
    by_cases hzero : z = 0
    · simp [hzero]
    · have hone : z = 1 := by
        by_contra hnot
        exact h ⟨z, hzero, hnot⟩
      simp [hone]
  have hc : Fintype.card B.F4 ≤ 2 := by
    have bound := Finset.card_le_card cover
    simpa using bound
  omega

noncomputable def zeta : B.F4 :=
  Classical.choose exists_nontrivial_f4_element

theorem zeta_ne_zero : zeta ≠ 0 :=
  (Classical.choose_spec exists_nontrivial_f4_element).1

theorem zeta_ne_one : zeta ≠ 1 :=
  (Classical.choose_spec exists_nontrivial_f4_element).2

theorem nonzero_f4_cube_is_one (a : B.F4) (ha : a ≠ 0) :
    a ^ 3 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  simpa [f4_cardinality] using h

theorem zeta_cube_is_one : zeta ^ 3 = 1 :=
  nonzero_f4_cube_is_one zeta zeta_ne_zero

theorem zeta_quadratic :
    zeta ^ 2 + zeta + 1 = 0 := by
  have factor :
      (zeta - 1) * (zeta ^ 2 + zeta + 1) = 0 := by
    calc
      _ = zeta ^ 3 - 1 := by ring
      _ = 0 := by rw [zeta_cube_is_one]; ring
  exact (mul_eq_zero.mp factor).resolve_left (sub_ne_zero.mpr zeta_ne_one)

theorem zeta_trace_one :
    zeta ^ 2 + zeta = 1 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination zeta_quadratic - htwo

theorem zeta_fourth_is_zeta :
    zeta ^ 4 = zeta := by
  have h := FiniteField.pow_card zeta
  simpa [f4_cardinality] using h

theorem zeta_squared_quadratic :
    (zeta ^ 2) ^ 2 + zeta ^ 2 + 1 = 0 := by
  calc
    _ = zeta ^ 4 + zeta ^ 2 + 1 := by ring
    _ = zeta + zeta ^ 2 + 1 := by rw [zeta_fourth_is_zeta]
    _ = 0 := by simpa [add_comm, add_left_comm, add_assoc] using zeta_quadratic

theorem zeta_squared_trace_one :
    (zeta ^ 2) ^ 2 + zeta ^ 2 = 1 := by
  calc
    _ = zeta ^ 4 + zeta ^ 2 := by ring
    _ = zeta + zeta ^ 2 := by rw [zeta_fourth_is_zeta]
    _ = 1 := by simpa [add_comm] using zeta_trace_one

/-- The degree-three root polynomial has roots 0, zeta, and zeta^2. -/
def ternaryRootPolynomial (t : B.F4) : B.F4 :=
  t * (t ^ 2 + t + 1)

theorem zero_is_ternary_root :
    ternaryRootPolynomial 0 = 0 := by
  simp [ternaryRootPolynomial]

theorem zeta_is_ternary_root :
    ternaryRootPolynomial zeta = 0 := by
  simp [ternaryRootPolynomial, zeta_quadratic]

theorem zeta_squared_is_ternary_root :
    ternaryRootPolynomial (zeta ^ 2) = 0 := by
  simp [ternaryRootPolynomial, zeta_squared_quadratic]

/-- The characteristic-two quadratic splits at precisely zeta and zeta². -/
theorem quadratic_factors (t : B.F4) :
    (t - zeta) * (t - zeta ^ 2) = t ^ 2 + t + 1 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  calc
    _ = t ^ 2 - (zeta + zeta ^ 2) * t + zeta ^ 3 := by ring
    _ = t ^ 2 - t + 1 := by
      rw [show zeta + zeta ^ 2 = (1 : B.F4) from by
        simpa [add_comm] using zeta_trace_one, zeta_cube_is_one]
    _ = t ^ 2 + t + 1 := by linear_combination -(t * htwo)

/-- All three roots, and no others, of t(t²+t+1) over F4. -/
theorem ternary_root_iff (t : B.F4) :
    ternaryRootPolynomial t = 0 ↔
      t = 0 ∨ t = zeta ∨ t = zeta ^ 2 := by
  constructor
  · intro h
    have hf : t * ((t - zeta) * (t - zeta ^ 2)) = 0 := by
      simpa [ternaryRootPolynomial, quadratic_factors] using h
    rcases mul_eq_zero.mp hf with hzero | hrest
    · exact Or.inl hzero
    rcases mul_eq_zero.mp hrest with hz | hz2
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
    · exact Or.inr (Or.inr (sub_eq_zero.mp hz2))
  · rintro (rfl | rfl | rfl)
    · exact zero_is_ternary_root
    · exact zeta_is_ternary_root
    · exact zeta_squared_is_ternary_root

/-- Frobenius exchanges the two nonzero phase roots. -/
theorem zeta_frobenius_conjugate :
    (zeta ^ 2) ^ 2 = zeta := by
  calc
    _ = zeta ^ 4 := by ring
    _ = zeta := zeta_fourth_is_zeta

theorem one_is_not_ternary_root :
    ternaryRootPolynomial 1 ≠ 0 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  simp [ternaryRootPolynomial, show (3 : B.F4) = 1 by
    linear_combination htwo]

/-- Equation of the special-fibre homogeneous cubic at a coordinate triple. -/
def specialHomogeneousCubic (X Y Z : B.F4) : B.F4 :=
  Y ^ 2 * Z + Y * Z ^ 2 - X ^ 3

theorem valid_infinity :
    specialHomogeneousCubic 0 1 0 = 0 := by
  simp [specialHomogeneousCubic]

theorem zeta_zetaSquared_zero_is_not_infinity :
    specialHomogeneousCubic zeta (zeta ^ 2) 0 ≠ 0 := by
  simp [specialHomogeneousCubic, zeta_cube_is_one]

/-- Every cube-one coordinate is 1, zeta, or zeta². -/
theorem cube_one_iff (x : B.F4) :
    x ^ 3 = 1 ↔ x = 1 ∨ x = zeta ∨ x = zeta ^ 2 := by
  constructor
  · intro h
    have hf : (x - 1) * ((x - zeta) * (x - zeta ^ 2)) = 0 := by
      calc
        _ = (x - 1) * (x ^ 2 + x + 1) := by rw [quadratic_factors]
        _ = x ^ 3 - 1 := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp hf with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    rcases mul_eq_zero.mp h2 with hz | hz2
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
    · exact Or.inr (Or.inr (sub_eq_zero.mp hz2))
  · rintro (rfl | rfl | rfl)
    · ring
    · exact zeta_cube_is_one
    · calc
        _ = zeta ^ 6 := by ring
        _ = (zeta ^ 3) ^ 2 := by ring
        _ = 1 := by rw [zeta_cube_is_one]; ring

/-- The characteristic-two zero-trace values are exactly zero and one. -/
theorem trace_zero_iff (y : B.F4) :
    y ^ 2 + y = 0 ↔ y = 0 ∨ y = 1 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hfactor : y * (y - 1) = y ^ 2 + y := by
    linear_combination -(y * htwo)
  constructor
  · intro h
    have hf : y * (y - 1) = 0 := by rw [hfactor, h]
    rcases mul_eq_zero.mp hf with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl)
    · simp
    · simpa using htwo

/-- The characteristic-two unit-trace values are zeta and zeta². -/
theorem trace_one_iff (y : B.F4) :
    y ^ 2 + y = 1 ↔ y = zeta ∨ y = zeta ^ 2 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  constructor
  · intro h
    have hz : y ^ 2 + y + 1 = 0 := by
      linear_combination h + htwo
    have hf : (y - zeta) * (y - zeta ^ 2) = 0 := by
      rw [quadratic_factors]
      exact hz
    rcases mul_eq_zero.mp hf with hz1 | hz2
    · exact Or.inl (sub_eq_zero.mp hz1)
    · exact Or.inr (sub_eq_zero.mp hz2)
  · rintro (rfl | rfl)
    · exact zeta_trace_one
    · exact zeta_squared_trace_one

/--
Exhaustive affine-coordinate classification for Banerjee's special F4 curve.
This determines two points over x=0, and two over each of 1,zeta,zeta².
-/
theorem affine_curve_coordinate_iff (x y : B.F4) :
    y ^ 2 + y = x ^ 3 ↔
      (x = 0 ∧ (y = 0 ∨ y = 1)) ∨
      ((x = 1 ∨ x = zeta ∨ x = zeta ^ 2) ∧
        (y = zeta ∨ y = zeta ^ 2)) := by
  constructor
  · intro h
    by_cases hx : x = 0
    · left
      refine ⟨hx, (trace_zero_iff y).mp ?_⟩
      simpa [hx] using h
    · right
      have hx3 : x ^ 3 = 1 := nonzero_f4_cube_is_one x hx
      exact ⟨(cube_one_iff x).mp hx3,
        (trace_one_iff y).mp (h.trans hx3)⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, hy⟩)
    · simpa using (trace_zero_iff y).mpr hy
    · have hx3 := (cube_one_iff x).mpr hx
      have hy1 := (trace_one_iff y).mpr hy
      exact hy1.trans hx3.symm

structure Boundary where
  actualNontrivialF4ZetaSelected : Bool
  cubicRootAndQuadraticRelation : Bool
  bothConjugateRootsSolveYTraceOne : Bool
  threeRootPolynomialOwned : Bool
  exhaustiveThreeRootClassificationOwned : Bool
  falseProjectiveInfinityTripleRejected : Bool
  exhaustiveAffineCoordinateClassificationLeanOwned : Bool
  fullCurvePointEnumerationLeanProved : Bool
  gamma0FourMarkedSourceRealized : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualNontrivialF4ZetaSelected := true
  cubicRootAndQuadraticRelation := true
  bothConjugateRootsSolveYTraceOne := true
  threeRootPolynomialOwned := true
  exhaustiveThreeRootClassificationOwned := true
  falseProjectiveInfinityTripleRejected := true
  exhaustiveAffineCoordinateClassificationLeanOwned := true
  fullCurvePointEnumerationLeanProved := false
  gamma0FourMarkedSourceRealized := false

end Integration.OggSSPP2BanerjeeF4ZetaCoordinates
