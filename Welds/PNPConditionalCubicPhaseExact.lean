import Welds.PNPQuadraticMobiusExact

/-!
F3 conditional phase elimination on the original character carrier.
A cubic interaction is reduced by selecting an actual coordinate, not
by treating dependent phase labels as independent. No claim that the
number of selected coordinates is uniformly bounded.
-/
namespace PNPQuadraticPhase
open scoped BigOperators

theorem linear_axis {R : Type*} [CommRing R]
    (chi : ZMod 3 → R) (hchi : ∀ x y,chi (x+y)=chi x*chi y)
    (hzero : ∑ x : ZMod 3,chi x=0)
    (b c : ZMod 3) (hb : b≠0) :
    (∑ x : ZMod 3,chi (b*x+c))=0 := by
  let e : ZMod 3 ≃ ZMod 3 :=
    {toFun := fun x => b*x
     invFun := fun x => b⁻¹*x
     left_inv := fun x => by rw [← mul_assoc,inv_mul_cancel₀ hb,one_mul]
     right_inv := fun x => by rw [← mul_assoc,mul_inv_cancel₀ hb,one_mul]}
  calc
    _ = ∑ x : ZMod 3,chi c*chi (b*x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← hchi,add_comm]
    _ = chi c*∑ x : ZMod 3,chi (b*x) := by rw [Finset.mul_sum]
    _ = 0 := by
      have he := Equiv.sum_comp e chi
      change (∑ x : ZMod 3,chi (b*x))=(∑ x : ZMod 3,chi x) at he
      rw [he,hzero,mul_zero]

/-- Every conditional axis, including vanishing quadratic coefficient,
has an exact signed elimination law. The constant branch is not
confused with the linear-zero character branch. -/
theorem gauss_axis_total {R : Type*} [CommRing R]
    (chi : ZMod 3 → R) (hchi : ∀ x y,chi (x+y)=chi x*chi y)
    (hzero : ∑ x : ZMod 3,chi x=0)
    (a b c : ZMod 3) :
    (∑ x : ZMod 3,chi (a*x^2+b*x+c)) =
      if a=0 then (if b=0 then 3*chi c else 0)
      else chi (c-a*b^2)*∑ x : ZMod 3,chi (a*x^2) := by
  by_cases ha : a=0
  · subst a
    by_cases hb : b=0
    · subst b
      simp
    · simpa [hb] using linear_axis chi hchi hzero b c hb
  · rw [if_neg ha]
    exact gauss_axis chi hchi a b c ha

/-- Fubini on a selected coordinate of a dependent cubic source.
The remaining coefficients may be nonlinear functions of the retained
coordinates. This is exact; no universal affordable cost is inferred. -/
theorem conditional_phase_axis {R Y : Type*} [CommRing R] [Fintype Y]
    (chi : ZMod 3 → R) (hchi : ∀ x y,chi (x+y)=chi x*chi y)
    (hzero : ∑ x : ZMod 3,chi x=0)
    (a b c : Y → ZMod 3) :
    (∑ p : Y × ZMod 3,chi (a p.1*p.2^2+b p.1*p.2+c p.1)) =
      ∑ y : Y,if a y=0 then (if b y=0 then 3*chi (c y) else 0)
        else chi (c y-a y*(b y)^2)*∑ x : ZMod 3,chi (a y*x^2) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  exact gauss_axis_total chi hchi hzero (a y) (b y) (c y)

end PNPQuadraticPhase
