import Welds.PNPConditionalCubicPhaseExact

/-!
Product factorization after the actual affine pullback, on disjoint
coordinate carriers. A quadratic bridge between two cubic supports
must be kept in the same component. This theorem requires the literal
separation equality; it does not infer it from CNF block labels.
-/
namespace PNPQuadraticPhase
open scoped BigOperators

theorem independent_phase_product {R A B : Type*} [CommRing R]
    [Fintype A] [Fintype B] (chi : ZMod 3 → R)
    (hchi : ∀ x y,chi (x+y)=chi x*chi y)
    (p : A → ZMod 3) (q : B → ZMod 3) :
    (∑ x : A × B,chi (p x.1+q x.2)) =
      (∑ a : A,chi (p a))*(∑ b : B,chi (q b)) := by
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact hchi _ _

theorem independent_phase_chart {R X A B : Type*} [CommRing R]
    [Fintype X] [Fintype A] [Fintype B]
    (chi : ZMod 3 → R) (hchi : ∀ x y,chi (x+y)=chi x*chi y)
    (e : X ≃ A × B) (P : X → ZMod 3)
    (p : A → ZMod 3) (q : B → ZMod 3)
    (hsep : ∀ x,P x=p (e x).1+q (e x).2) :
    (∑ x : X,chi (P x))=
      (∑ a : A,chi (p a))*(∑ b : B,chi (q b)) := by
  have he := Equiv.sum_comp e (fun z : A × B=>chi (p z.1+q z.2))
  simp only [hsep]
  rw [he]
  exact independent_phase_product chi hchi p q

/-- Independent copies of xyz over F3. Each has character sum 15
when chi is the usual nontrivial cubic character. A product of
independent copies is not a joint exponential branching requirement. -/
theorem independent_xyz_axis {R : Type*} [CommRing R]
    (chi : ZMod 3 → R) (h1 : chi 0=1)
    (hzero : ∑ x : ZMod 3,chi x=0) :
    (∑ p : (ZMod 3 × ZMod 3) × ZMod 3,chi (p.1.1*p.1.2*p.2))=15 := by
  have haxis (a : ZMod 3) :
      (∑ x : ZMod 3,chi (a*x))=if a=0 then (3:R) else 0 := by
    by_cases ha : a=0
    · simp [ha,h1]
    · let e : ZMod 3 ≃ ZMod 3 :=
        {toFun := fun x=>a*x
         invFun := fun x=>a⁻¹*x
         left_inv := fun x=>by rw [← mul_assoc,inv_mul_cancel₀ ha,one_mul]
         right_inv := fun x=>by rw [← mul_assoc,mul_inv_cancel₀ ha,one_mul]}
      have he := Equiv.sum_comp e chi
      change (∑ x : ZMod 3,chi (a*x))=(∑ x : ZMod 3,chi x) at he
      rw [he,hzero,if_neg ha]
  rw [Fintype.sum_prod_type]
  simp_rw [haxis]
  have hcount : ((Finset.univ : Finset (ZMod 3 × ZMod 3)).filter
      (fun z=>z.1*z.2=0)).card=5 := by decide
  rw [← Finset.sum_filter]
  simp [hcount]
  ring

end PNPQuadraticPhase
