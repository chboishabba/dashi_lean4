import Synthesis.MillenniumHodgeDicksonRotationProductFibreExact
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! On the actual punctured generic Dickson chart, the projection to
surface x-coordinates is injective on the fixed seventh-power address
away from y²=a⁷. The quadratic derivative-to-s map is already BIDI.
This pays a generic projection multiplicity cut; it does not assert
properness, irreducibility or primitive Chow-class nonvanishing. -/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

theorem fold_collision (a v w : F) (hv : v≠0) (hw : w≠0)
    (h : v+a/v=w+a/w) : v=w ∨ v*w=a := by
  have he : (v-w)*(v*w-a)=0 := by
    field_simp [hv,hw] at h
    linear_combination h
  exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp

theorem fold_seventh_injective (a y v w : F)
    (hy : y≠0) (hbranch : y^2≠a^7)
    (hv : v^7=y) (hw : w^7=y)
    (h : v+a/v=w+a/w) : v=w := by
  have hv0 : v≠0 := by intro hz; apply hy; rw [← hv,hz]; norm_num
  have hw0 : w≠0 := by intro hz; apply hy; rw [← hw,hz]; norm_num
  rcases fold_collision a v w hv0 hw0 h with he|he
  · exact he
  · apply False.elim
    apply hbranch
    have hp := congrArg (fun z : F=>z^7) he
    rw [mul_pow,hv,hw] at hp
    simpa [pow_two] using hp

def coupledProjection (a y : Address → F) (η δ : F)
    (p : RotationFibre y η × ActualRootFibre a y δ) :
    Address → F × F :=
  fun i=>(p.1.1 i+a i/p.1.1 i,p.2.1 i)

theorem coupledProjection_injective (a y : Address → F) (η δ : F)
    (hy : ∀ i,y i≠0) (hb : ∀ i,(y i)^2≠(a i)^7) :
    Function.Injective (coupledProjection a y η δ) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    exact fold_seventh_injective (a i) (y i) (p.1.1 i) (q.1.1 i)
      (hy i) (hb i) (p.1.2.1 i) (q.1.2.1 i)
      (congrArg Prod.fst (congrFun h i))
  · apply Subtype.ext
    funext i
    exact congrArg Prod.snd (congrFun h i)

def coupledSurfaceFibreEquiv (a y : Address → F) (η δ : F)
    (hy : ∀ i,y i≠0) (hb : ∀ i,(y i)^2≠(a i)^7) :
    (RotationFibre y η × ActualRootFibre a y δ) ≃
      Set.range (coupledProjection a y η δ) :=
  Equiv.ofInjective _ (coupledProjection_injective a y η δ hy hb)

/-- Five independent root-of-unity coordinates and a uniquely determined
sixth. This is the actual product-one deck fibre, not a loose sixfold
Cartesian product. -/
def ProductOneDeck (F : Type*) [Field F] (n : ℕ) :=
  {e : Address → F // (∀ i,e i^n=1) ∧ (∏ i,e i)=1}

def rootProd (n : ℕ) (f : Fin 5 → {e : F // e^n=1}) : F := ∏ i,(f i).1

theorem rootProd_pow (n : ℕ) (f : Fin 5 → {e : F // e^n=1}) :
    (rootProd n f)^n=1 := by
  unfold rootProd
  rw [← Finset.prod_pow]
  simp only [Subtype.property,Finset.prod_const_one]

def fiveDeckEquiv (n : ℕ) (hn : n≠0) :
    (Fin 5 → {e : F // e^n=1}) ≃ ProductOneDeck F n where
  toFun f := ⟨Fin.lastCases (rootProd n f)⁻¹ (fun i=>(f i).1),by
    have hprod := rootProd_pow n f
    have hz : rootProd n f≠0 := by
      intro h; rw [h,zero_pow hn] at hprod; exact zero_ne_one hprod
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simp [inv_pow,hprod]
      · simpa using (f j).2
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
      exact mul_inv_cancel₀ hz⟩
  invFun e i := ⟨e.1 i.castSucc,e.2.1 _⟩
  left_inv f := by funext i; apply Subtype.ext; simp
  right_inv e := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j=>by simp) i
    have he := e.2.2
    rw [Fin.prod_univ_castSucc] at he
    have hz : (∏ j : Fin 5,e.1 j.castSucc)≠0 := by
      intro h; rw [h,zero_mul] at he; exact zero_ne_one he
    simp only [Fin.lastCases_last,rootProd]
    exact (inv_eq_of_mul_eq_one_left he).symm

end
end DASHI.Hodge.DicksonCoupled
