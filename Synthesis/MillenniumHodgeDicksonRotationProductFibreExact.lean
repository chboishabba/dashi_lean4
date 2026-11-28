import Synthesis.MillenniumHodgeDicksonGenericSignedFibreExact

/-! Punctured rotation chart of the original Dickson polynomial.
The product address is retained; this is a geometric fibre calculation,
not an algebraic-cycle construction or a cohomological pushforward. -/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

def dickson7Field (X a : F) :=
  X^7-7*a*X^5+14*a^2*X^3-7*a^3*X

theorem dickson7Field_laurent (a v : F) (hv : v ≠ 0) :
    dickson7Field (v+a/v) a = v^7+(a/v)^7 := by
  unfold dickson7Field
  field_simp [hv] <;> ring

def RotationFibre (y : Address → F) (η : F) :=
  {v : Address → F // (∀ i,v i^7=y i) ∧ (∏ i,v i)=η}

def RotationDeck (F : Type*) [Field F] :=
  {e : Address → F // (∀ i,e i^7=1) ∧ (∏ i,e i)=1}

theorem rotationFibre_nonzero {y : Address → F} {η : F}
    (v : RotationFibre y η) (hη : η ≠ 0) (i : Address) : v.1 i ≠ 0 := by
  intro h
  apply hη
  rw [← v.2.2,← Finset.prod_erase_mul (s:=Finset.univ) (f:=v.1)
    (Finset.mem_univ i),h,mul_zero]

theorem rotationFibre_inhabited [IsAlgClosed F] (y : Address → F) (η : F)
    (hη : η ≠ 0) (hprod : η^7=∏ i,y i) :
    Nonempty (RotationFibre y η) := by
  classical
  choose v hv using fun i : Address =>
    IsAlgClosed.exists_pow_nat_eq (y i) (by decide : 0<7)
  let p : F := ∏ i,v i
  have hp7 : p^7=η^7 := by
    rw [hprod]
    dsimp [p]
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _=>hv i
  have hp : p≠0 := by
    intro h
    rw [h,zero_pow (by decide : 7≠0)] at hp7
    exact hη (pow_eq_zero hp7.symm)
  let ε : F := η/p
  have hε : ε^7=1 := by
    dsimp [ε]
    rw [div_pow,hp7,div_self (pow_ne_zero _ hη)]
  let e : Address → F := fun i=>if i=5 then ε else 1
  have he : ∏ i,e i = ε := by simp [e,Fin.prod_univ_succ]
  refine ⟨⟨fun i=>e i*v i,?_,?_⟩⟩
  · intro i
    rw [mul_pow,hv]
    have hi : e i^7=1 := by by_cases h : i=5 <;> simp [e,h,hε]
    rw [hi,one_mul]
  · rw [Finset.prod_mul_distrib,he]
    change η/p*p=η
    exact div_mul_cancel₀ _ hp

def rotationDeckEquiv {y : Address → F} {η : F}
    (v : RotationFibre y η) (hη : η≠0) : RotationDeck F ≃ RotationFibre y η where
  toFun e := ⟨fun i=>e.1 i*v.1 i,by
    constructor
    · intro i
      rw [mul_pow,e.2.1 i,v.2.1 i,one_mul]
    · rw [Finset.prod_mul_distrib,e.2.2,v.2.2,one_mul]⟩
  invFun x := ⟨fun i=>x.1 i/v.1 i,by
    constructor
    · intro i
      rw [div_pow,x.2.1 i,← v.2.1 i,div_self (pow_ne_zero _ (rotationFibre_nonzero v hη i))]
    · rw [Finset.prod_div_distrib,x.2.2,v.2.2,div_self hη]⟩
  left_inv e := Subtype.ext (funext fun i=>mul_div_cancel_right₀ _ (rotationFibre_nonzero v hη i))
  right_inv x := Subtype.ext (funext fun i=>div_mul_cancel₀ _ (rotationFibre_nonzero v hη i))

/-- Both product-address constraints are simultaneously realized on
the punctured chart, and the six actual Dickson surface equations hold. -/
theorem coupled_chart_inhabited [IsAlgClosed F] (a y : Address → F) (η δ : F)
    (hy : ∀ i,y i≠0) (hη : η≠0) (hδ : δ≠0)
    (hrot : η^7=∏ i,y i) (hsign : δ^2=∏ i,deltaField (a i) (y i)) :
    ∃ v : RotationFibre y η, ∃ s : ActualRootFibre a y δ,
      ∀ i, dickson7Field (v.1 i+a i/v.1 i) (a i)=Q0Field (a i) (s.1 i) := by
  obtain ⟨v⟩ := rotationFibre_inhabited y η hη hrot
  obtain ⟨s⟩ := actualRootFibre_inhabited a y δ hy hδ hsign
  refine ⟨v,s,fun i=>?_⟩
  rw [dickson7Field_laurent _ _ (rotationFibre_nonzero v hη i),
    div_pow,v.2.1 i,s.2.1 i]

end
end DASHI.Hodge.DicksonCoupled
