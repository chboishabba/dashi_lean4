import Synthesis.MillenniumHodgeDicksonSignedDerivativeIncidenceExact
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
The actual Q0 incidence over an algebraically closed extension.
Over the punctured signed discriminant cover, the six root fibres
are inhabited and all points differ by an even deck-sign vector.
This is the generic geometric fibre (not a diagonal rational example).
No Chow pushforward or primitive-class nonvanishing is inferred.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

def Q0Field (a s : F) := -3*a^3-3*a^2*s-a^2+3*a*s+3*a-2*s^2+s+3

def deltaField (a y : F) :=
  (-3*a^2+3*a+1)^2+8*(-3*a^3-a^2+3*a+3-y-a^7/y)

def dField (a s : F) := -3*a^2+3*a+1-4*s

def inverseField (a d : F) := (-3*a^2+3*a+1-d)/4

theorem Q0Field_rat (a s : ℚ) : Q0Field a s = Q0 a s := by
  unfold Q0Field Q0
  ring

theorem deltaField_rat (a y : ℚ) : deltaField a y = Q0Discriminant a y := rfl

theorem dField_inverse (a d : F) : dField a (inverseField a d)=d := by
  unfold dField inverseField
  ring

theorem inverseField_d (a s : F) : inverseField a (dField a s)=s := by
  unfold dField inverseField
  ring

theorem actual_field_residual (a y s : F) :
    dField a s ^ 2-deltaField a y = -8*(Q0Field a s-y-a^7/y) := by
  unfold dField deltaField Q0Field
  ring

def SignedFibre (D : Address → F) (δ : F) :=
  {d : Address → F // (∀ i,d i^2=D i) ∧ (∏ i,d i)=δ}

def ActualRootFibre (a y : Address → F) (δ : F) :=
  {s : Address → F // (∀ i,Q0Field (a i) (s i)=y i+(a i)^7/y i) ∧
    (∏ i,dField (a i) (s i))=δ}

theorem field_root_iff (a y s : F) :
    Q0Field a s = y+a^7/y ↔ dField a s^2=deltaField a y := by
  have he := actual_field_residual a y s
  constructor
  · intro h
    linear_combination he - 8*h
  · intro h
    linear_combination (1/8 : F)*h - (1/8 : F)*he

def actualRootFibreEquiv (a y : Address → F) (δ : F) :
    ActualRootFibre a y δ ≃ SignedFibre (fun i => deltaField (a i) (y i)) δ where
  toFun s := ⟨fun i=>dField (a i) (s.1 i),
    fun i=>(field_root_iff _ _ _).mp (s.2.1 i),s.2.2⟩
  invFun d := ⟨fun i=>inverseField (a i) (d.1 i),by
    constructor
    · intro i
      apply (field_root_iff _ _ _).mpr
      rw [dField_inverse]
      exact d.2.1 i
    · simpa only [dField_inverse] using d.2.2⟩
  left_inv s := Subtype.ext (funext fun i=>inverseField_d _ _)
  right_inv d := Subtype.ext (funext fun i=>dField_inverse _ _)

theorem signedFibre_nonzero {D : Address → F} {δ : F}
    (d : SignedFibre D δ) (hδ : δ≠0) (i : Address) : d.1 i≠0 := by
  intro h
  apply hδ
  rw [← d.2.2,← Finset.prod_erase_mul (s:=Finset.univ) (f:=d.1) (Finset.mem_univ i),h,mul_zero]

/-- On the actual punctured double cover, choose roots in the
algebraically closed field and correct ONE sign to match δ. -/
theorem signedFibre_inhabited [IsAlgClosed F] (D : Address → F) (δ : F)
    (hδ : δ≠0) (hprod : δ^2=∏ i,D i) : Nonempty (SignedFibre D δ) := by
  classical
  choose d hd using fun i : Address => IsAlgClosed.exists_pow_nat_eq (D i) (by decide : 0<2)
  let p : F := ∏ i,d i
  have hp2 : p^2=δ^2 := by
    rw [hprod]
    dsimp [p]
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _=>hd i
  have hp : p≠0 := by
    intro h
    rw [h,zero_pow (by decide : 2≠0)] at hp2
    exact hδ (pow_eq_zero hp2.symm)
  let ε : F := δ/p
  have hε : ε^2=1 := by
    dsimp [ε]
    rw [div_pow,hp2,div_self (pow_ne_zero _ hδ)]
  let e : Address → F := fun i=>if i=5 then ε else 1
  have he : ∏ i,e i = ε := by
    simp [e,Fin.prod_univ_succ]
  refine ⟨⟨fun i=>e i*d i,?_,?_⟩⟩
  · intro i
    rw [mul_pow,hd]
    have hi : e i^2=1 := by
      by_cases h : i=5 <;> simp [e,h,hε]
    rw [hi,one_mul]
  · rw [Finset.prod_mul_distrib,he]
    change δ/p*p=δ
    exact div_mul_cancel₀ _ hp

/-- Exact free/transitive deck action: every other signed lift uniquely
has coordinate ratios of square one with product one. -/
def EvenDeck (F : Type*) [Field F] :=
  {e : Address → F // (∀ i,e i^2=1) ∧ (∏ i,e i)=1}

def signedFibreDeckEquiv {D : Address → F} {δ : F}
    (d : SignedFibre D δ) (hδ : δ≠0) : EvenDeck F ≃ SignedFibre D δ where
  toFun e := ⟨fun i=>e.1 i*d.1 i,by
    constructor
    · intro i
      rw [mul_pow,e.2.1 i,d.2.1 i,one_mul]
    · rw [Finset.prod_mul_distrib,e.2.2,d.2.2,one_mul]⟩
  invFun x := ⟨fun i=>x.1 i/d.1 i,by
    constructor
    · intro i
      rw [div_pow,x.2.1 i,← d.2.1 i,div_self (pow_ne_zero _ (signedFibre_nonzero d hδ i))]
    · rw [Finset.prod_div_distrib,x.2.2,d.2.2,div_self hδ]⟩
  left_inv e := Subtype.ext (funext fun i=>mul_div_cancel_right₀ _ (signedFibre_nonzero d hδ i))
  right_inv x := Subtype.ext (funext fun i=>div_mul_cancel₀ _ (signedFibre_nonzero d hδ i))

theorem actualRootFibre_inhabited [IsAlgClosed F] (a y : Address → F) (δ : F)
    (_hy : ∀ i,y i≠0) (hδ : δ≠0)
    (hprod : δ^2=∏ i,deltaField (a i) (y i)) :
    Nonempty (ActualRootFibre a y δ) := by
  obtain ⟨d⟩ := signedFibre_inhabited _ δ hδ hprod
  exact ⟨(actualRootFibreEquiv a y δ).symm d⟩

end
end DASHI.Hodge.DicksonCoupled
