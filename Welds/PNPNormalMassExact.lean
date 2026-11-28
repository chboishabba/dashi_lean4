import Welds.PNPBooleanSeparatorExact
import Welds.PNPSeparatorMarginalsExact
import Welds.PNPLinearConsumerCutExact

namespace PNPNormalMass
open scoped BigOperators

abbrev F := ZMod 2

section Glue
variable {M : Type*} [AddCommGroup M] [Module F M]
variable (U V : Submodule F M)

-- Local observations are linear functionals on the actual source
-- normal spaces, not ambient assignments. Equality on the intersection
-- is exactly the well-definedness condition for their sum.
def Agree (l : U →ₗ[F] F) (r : V →ₗ[F] F) : Prop :=
  ∀ x (hu : x ∈ U) (hv : x ∈ V), l ⟨x,hu⟩ = r ⟨x,hv⟩

theorem split_exists (x : U ⊔ V) :
    ∃ p : U × V, (p.1 : M)+(p.2 : M)=x.val := by
  obtain ⟨u,hu,v,hv,h⟩ := Submodule.mem_sup.mp x.property
  exact ⟨(⟨u,hu⟩,⟨v,hv⟩),h⟩

theorem split_value_eq (l : U →ₗ[F] F) (r : V →ₗ[F] F)
    (h : Agree U V l r) (u u' : U) (v v' : V)
    (e : (u : M)+(v : M)=(u' : M)+(v' : M)) :
    l u+r v=l u'+r v' := by
  have ed : (u : M)-(u' : M)=(v' : M)-(v : M) := by
    calc
      (u : M)-(u' : M) = ((u : M)+(v : M))-((u' : M)+(v : M)) := by abel
      _ = ((u' : M)+(v' : M))-((u' : M)+(v : M)) := by rw [e]
      _ = (v' : M)-(v : M) := by abel
  have hu : (u : M)-(u' : M) ∈ U := U.sub_mem u.property u'.property
  have hv : (u : M)-(u' : M) ∈ V := ed.symm ▸ V.sub_mem v'.property v.property
  have hl : (⟨(u : M)-(u' : M),hu⟩ : U)=u-u' := rfl
  have hr : (⟨(u : M)-(u' : M),hv⟩ : V)=v'-v :=
    Subtype.ext ed
  have q := h ((u : M)-(u' : M)) hu hv
  rw [hl,hr,map_sub,map_sub] at q
  calc
    l u+r v = (l u-l u')+(l u'+r v) := by abel
    _ = (r v'-r v)+(l u'+r v) := by rw [q]
    _ = l u'+r v' := by abel

noncomputable def chooseSplit (x : U ⊔ V) : U × V :=
  Classical.choose (split_exists U V x)

theorem chooseSplit_spec (x : U ⊔ V) :
    ((chooseSplit U V x).1 : M)+((chooseSplit U V x).2 : M)=x.val :=
  Classical.choose_spec (split_exists U V x)

noncomputable def gluedValue (l : U →ₗ[F] F) (r : V →ₗ[F] F)
    (x : U ⊔ V) : F :=
  l (chooseSplit U V x).1 + r (chooseSplit U V x).2

theorem gluedValue_on (l : U →ₗ[F] F) (r : V →ₗ[F] F)
    (h : Agree U V l r) (x : U ⊔ V) (u : U) (v : V)
    (e : (u : M)+(v : M)=x.val) :
    gluedValue U V l r x=l u+r v :=
  split_value_eq U V l r h _ _ _ _ ((chooseSplit_spec U V x).trans e.symm)

noncomputable def glue (l : U →ₗ[F] F) (r : V →ₗ[F] F)
    (h : Agree U V l r) : (U ⊔ V) →ₗ[F] F where
  toFun := gluedValue U V l r
  map_add' x y := by
    let p := chooseSplit U V x
    let q := chooseSplit U V y
    have hp : (p.1 : M)+(p.2 : M)=x.val := chooseSplit_spec U V x
    have hq : (q.1 : M)+(q.2 : M)=y.val := chooseSplit_spec U V y
    have he : ((p.1+q.1 : U) : M)+((p.2+q.2 : V) : M)=(x+y).val := by
      change ((p.1 : M)+(q.1 : M))+((p.2 : M)+(q.2 : M))=x.val+y.val
      rw [← hp,← hq]
      abel
    change gluedValue U V l r (x+y)=gluedValue U V l r x+gluedValue U V l r y
    rw [gluedValue_on U V l r h _ _ _ he]
    change l (p.1+q.1)+r (p.2+q.2)=(l p.1+r p.2)+(l q.1+r q.2)
    rw [map_add,map_add]
    abel
  map_smul' a x := by
    let p := chooseSplit U V x
    have hp : (p.1 : M)+(p.2 : M)=x.val := chooseSplit_spec U V x
    have he : ((a • p.1 : U) : M)+((a • p.2 : V) : M)=(a • x).val := by
      change a • (p.1 : M)+a • (p.2 : M)=a • x.val
      rw [← smul_add,hp]
    change gluedValue U V l r (a • x)=a • gluedValue U V l r x
    rw [gluedValue_on U V l r h _ _ _ he]
    change l (a • p.1)+r (a • p.2)=a • (l p.1+r p.2)
    rw [map_smul,map_smul,smul_add]

def leftIn (x : U) : U ⊔ V := ⟨x.val,le_sup_left x.property⟩
def rightIn (x : V) : U ⊔ V := ⟨x.val,le_sup_right x.property⟩

theorem glue_left (l : U →ₗ[F] F) (r : V →ₗ[F] F) (h : Agree U V l r) (x : U) :
    glue U V l r h (leftIn U V x)=l x := by
  change gluedValue U V l r (leftIn U V x)=l x
  rw [gluedValue_on U V l r h _ x 0 (by simp [leftIn])]
  simp

theorem glue_right (l : U →ₗ[F] F) (r : V →ₗ[F] F) (h : Agree U V l r) (x : V) :
    glue U V l r h (rightIn U V x)=r x := by
  change gluedValue U V l r (rightIn U V x)=r x
  rw [gluedValue_on U V l r h _ 0 x (by simp [rightIn])]
  simp

theorem glue_unique (l : U →ₗ[F] F) (r : V →ₗ[F] F)
    (h : Agree U V l r) (g : (U ⊔ V) →ₗ[F] F)
    (hl : ∀ x, g (leftIn U V x)=l x)
    (hr : ∀ x, g (rightIn U V x)=r x) : g=glue U V l r h := by
  ext x
  obtain ⟨⟨u,v⟩,e⟩ := split_exists U V x
  have hx : leftIn U V u+rightIn U V v=x := Subtype.ext e
  calc
    g x = l u+r v := by rw [← hx,map_add,hl,hr]
    _ = glue U V l r h x := (gluedValue_on U V l r h x u v e).symm

theorem glue_iff (l : U →ₗ[F] F) (r : V →ₗ[F] F) :
    Agree U V l r ↔ ∃! g : (U ⊔ V) →ₗ[F] F,
      (∀ x, g (leftIn U V x)=l x) ∧ (∀ x, g (rightIn U V x)=r x) := by
  constructor
  · intro h
    exact ⟨glue U V l r h,⟨glue_left U V l r h,glue_right U V l r h⟩,
      fun g hg => glue_unique U V l r h g hg.1 hg.2⟩
  · rintro ⟨g,⟨hl,hr⟩,_⟩ x hu hv
    have e : leftIn U V ⟨x,hu⟩=rightIn U V ⟨x,hv⟩ := rfl
    rw [← hl,← hr,e]

-- Parent boundary information is determined by the two child
-- boundaries. This is the actual condition that allows one retained
-- representative to determine the parent's label, even though its
-- mass counts many distinct private normal restrictions.
theorem parent_boundary_le (W : Submodule F M) :
    ((U ⊔ V) ⊓ W) ≤ (U ⊓ (V ⊔ W)) ⊔ (V ⊓ (U ⊔ W)) := by
  intro x hx
  obtain ⟨u,hu,v,hv,e⟩ := Submodule.mem_sup.mp hx.1
  have hu' : u∈V⊔W := by
    have he : u=x-v := by rw [← e]; abel
    rw [he]
    exact (V⊔W).sub_mem (le_sup_right hx.2) (le_sup_left hv)
  have hv' : v∈U⊔W := by
    have he : v=x-u := by rw [← e]; abel
    rw [he]
    exact (U⊔W).sub_mem (le_sup_right hx.2) (le_sup_left hu)
  exact Submodule.mem_sup.mpr ⟨u,⟨hu,hu'⟩,v,⟨hv,hv'⟩,e⟩

theorem sibling_overlap_left (W : Submodule F M) :
    U⊓V ≤ U⊓(V⊔W) := by
  intro x hx
  exact ⟨hx.1,le_sup_left hx.2⟩

theorem sibling_overlap_right (W : Submodule F M) :
    U⊓V ≤ V⊓(U⊔W) := by
  intro x hx
  exact ⟨hx.2,le_sup_left hx.1⟩

end Glue

-- Original affine observation fibres all have the same kernel mass.
-- No multiplicity is introduced by choosing different representatives.
def translateFibre {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (L : M →ₗ[F] N) (x : M) :
    {y : M // L y=L x} ≃ L.ker where
  toFun y := ⟨y.val-x,LinearMap.mem_ker.mpr (by rw [map_sub,y.property,sub_self])⟩
  invFun z := ⟨z.val+x,by rw [map_add,LinearMap.mem_ker.mp z.property,zero_add]⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

theorem fibre_card {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (L : M →ₗ[F] N) (x : M)
    [Fintype {y : M // L y=L x}] [Fintype L.ker] :
    Fintype.card {y : M // L y=L x}=Fintype.card L.ker :=
  Fintype.card_congr (translateFibre L x)

-- A checked kernel basis supplies the factor 2^k on the actual GF2
-- carrier. The explicit pivot chart determines k=d-rank at runtime.
theorem kernel_basis_card {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (L : M →ₗ[F] N) (x : M) (k : Nat)
    (basis : L.ker ≃ (Fin k → F))
    [Fintype {y : M // L y=L x}] [Fintype L.ker] :
    Fintype.card {y : M // L y=L x}=2^k := by
  rw [fibre_card L x,Fintype.card_congr basis]
  simp [F,Fintype.card_fun]

end PNPNormalMass
