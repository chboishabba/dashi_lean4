import RequestProject.CategoryOfOntologies

/-!
# Group theory: the symmetries of an ontology, and the symmetries of a pullback

*Wikidata: group theory (Q874429), group (Q83478), subgroup (Q466109),
automorphism group (Q60790315), group action (Q288465), pullback (Q1397439).*

`RequestProject.MathResonance` shows that the strict endomorphisms of an ontology
form a monoid (`Ontology.endoSubmonoid`).  This file takes the units of that
picture: the **automorphism group** `Aut X` of an ontology, in the category
`Ont` of `RequestProject.CategoryOfOntologies`, acting on its items — a renaming
of the items that preserves every `subclass of` and `instance of` statement, in
both directions.

The pullback is where the group theory happens.  Two ontologies aligned over a
third have a fibre product, and a symmetry of the fibre product can be assembled
from a *compatible triple* of symmetries: an automorphism `α` of `X`, one `β` of
`Y` and one `γ` of the reference `Z`, such that both squares commute.  Those
triples form a subgroup `Ontology.autOverSubgroup` of `Aut X × Aut Y × Aut Z` —
the fibre product of the automorphism groups over `Aut Z` — and

* `Ontology.pbAut` is a **group homomorphism** from it to `Aut (pbOnt F G)`;
* `Ontology.pbAut_fst`, `Ontology.pbAut_snd` say the two projections of the
  pullback are **equivariant** for the resulting actions;
* `Ontology.pbAutMulAction` is the induced action on the matched pairs, and
  `Ontology.pbAut_smul_apply` computes it: a compatible triple moves a matched
  pair componentwise.

`Ontology.autPerm` records that an automorphism of an ontology is in particular a
permutation of its items, as a group homomorphism `Aut X →* Equiv.Perm X.carrier`,
and `Ontology.autMulAction` is the action of `Aut X` on the items.
-/

open CategoryTheory

namespace Wikidata
namespace Ontology

universe u

variable {X Y Z : Ont.{u}}

/-! ## The automorphism group of an ontology -/

/-- The permutation of items underlying an automorphism of an ontology. -/
def autToPerm (α : Aut X) : Equiv.Perm X.carrier where
  toFun := α.hom.map
  invFun := α.inv.map
  left_inv a := congrFun (congrArg Morphism.map α.hom_inv_id) a
  right_inv a := congrFun (congrArg Morphism.map α.inv_hom_id) a

@[simp] theorem autToPerm_apply (α : Aut X) (a : X.carrier) : autToPerm α a = α.hom.map a := rfl

/-- **An automorphism of an ontology is a permutation of its items**, and this is
a group homomorphism. -/
def autPerm : Aut X →* Equiv.Perm X.carrier where
  toFun := autToPerm
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem autPerm_apply (α : Aut X) (a : X.carrier) : autPerm α a = α.hom.map a := rfl

/-- The automorphism group of an ontology acts on its items. -/
instance autMulAction : MulAction (Aut X) X.carrier :=
  MulAction.compHom _ autPerm

@[simp] theorem aut_smul_apply (α : Aut X) (a : X.carrier) : α • a = α.hom.map a := rfl

/-- Automorphisms preserve and reflect the derived class hierarchy. -/
theorem aut_subclassOf (α : Aut X) {a b : X.carrier} :
    X.str.SubclassOf (α • a) (α • b) ↔ X.str.SubclassOf a b := by
  constructor
  · intro h
    have h0 : X.str.SubclassOf (α.hom.map a) (α.hom.map b) := h
    have h' := α.inv.subclassOf h0
    rwa [show α.inv.map (α.hom.map a) = a from congrFun (congrArg Morphism.map α.hom_inv_id) a,
      show α.inv.map (α.hom.map b) = b from congrFun (congrArg Morphism.map α.hom_inv_id) b] at h'
  · exact fun h => α.hom.subclassOf h

/-! ## Compatible triples of symmetries -/

/-- **The fibre product of the automorphism groups.** Triples `(α, β, γ)` of
automorphisms of `X`, `Y` and the reference `Z` making both squares of the
cospan `X ⟶ Z ⟵ Y` commute. -/
def autOverSubgroup (F : X ⟶ Z) (G : Y ⟶ Z) : Subgroup (Aut X × Aut Y × Aut Z) where
  carrier := {t | t.1.hom ≫ F = F ≫ t.2.2.hom ∧ t.2.1.hom ≫ G = G ≫ t.2.2.hom}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show (𝟙 X) ≫ F = F ≫ (𝟙 Z); simp
    · show (𝟙 Y) ≫ G = G ≫ (𝟙 Z); simp
  mul_mem' := by
    rintro ⟨α₁, β₁, γ₁⟩ ⟨α₂, β₂, γ₂⟩ ⟨hα₁, hβ₁⟩ ⟨hα₂, hβ₂⟩
    refine ⟨?_, ?_⟩
    · show (α₂.hom ≫ α₁.hom) ≫ F = F ≫ (γ₂.hom ≫ γ₁.hom)
      rw [Category.assoc, hα₁, ← Category.assoc, hα₂, Category.assoc]
    · show (β₂.hom ≫ β₁.hom) ≫ G = G ≫ (γ₂.hom ≫ γ₁.hom)
      rw [Category.assoc, hβ₁, ← Category.assoc, hβ₂, Category.assoc]
  inv_mem' := by
    rintro ⟨α, β, γ⟩ ⟨hα, hβ⟩
    refine ⟨?_, ?_⟩
    · show α.inv ≫ F = F ≫ γ.inv
      rw [← Category.comp_id (α.inv ≫ F), ← γ.hom_inv_id, ← Category.assoc, Category.assoc α.inv,
        ← hα, ← Category.assoc, α.inv_hom_id, Category.id_comp]
    · show β.inv ≫ G = G ≫ γ.inv
      rw [← Category.comp_id (β.inv ≫ G), ← γ.hom_inv_id, ← Category.assoc, Category.assoc β.inv,
        ← hβ, ← Category.assoc, β.inv_hom_id, Category.id_comp]

variable {F : X ⟶ Z} {G : Y ⟶ Z}

theorem autOver_fst_map (t : autOverSubgroup F G) (a : X.carrier) :
    F.map (t.1.1.hom.map a) = t.1.2.2.hom.map (F.map a) :=
  congrFun (congrArg Morphism.map t.2.1) a

theorem autOver_snd_map (t : autOverSubgroup F G) (b : Y.carrier) :
    G.map (t.1.2.1.hom.map b) = t.1.2.2.hom.map (G.map b) :=
  congrFun (congrArg Morphism.map t.2.2) b

/-- The strict endomorphism of the fibre product induced by a compatible
triple: it moves a matched pair componentwise. -/
def pbAutMap (t : Aut X × Aut Y × Aut Z) (ht : t ∈ autOverSubgroup F G) :
    pbOnt F G ⟶ pbOnt F G :=
  pullback.lift F G (pbFst F G ≫ t.1.hom) (pbSnd F G ≫ t.2.1.hom) (by
    intro p
    have h₁ : F.map (t.1.hom.map p.1.1) = t.2.2.hom.map (F.map p.1.1) :=
      congrFun (congrArg Morphism.map ht.1) p.1.1
    have h₂ : G.map (t.2.1.hom.map p.1.2) = t.2.2.hom.map (G.map p.1.2) :=
      congrFun (congrArg Morphism.map ht.2) p.1.2
    show F.map (t.1.hom.map p.1.1) = G.map (t.2.1.hom.map p.1.2)
    rw [h₁, h₂, p.2])

@[simp] theorem pbAutMap_map_val (t : Aut X × Aut Y × Aut Z) (ht : t ∈ autOverSubgroup F G)
    (p : (pbOnt F G).carrier) :
    ((pbAutMap t ht).map p).1 = (t.1.hom.map p.1.1, t.2.1.hom.map p.1.2) := rfl

/-- **A compatible triple of symmetries is a symmetry of the pullback**, and this
assignment is a group homomorphism. -/
def pbAut (F : X ⟶ Z) (G : Y ⟶ Z) : autOverSubgroup F G →* Aut (pbOnt F G) where
  toFun t :=
    { hom := pbAutMap t.1 t.2
      inv := pbAutMap t⁻¹.1 t⁻¹.2
      hom_inv_id := by
        refine Morphism.ext' (funext fun p => Subtype.ext (Prod.ext ?_ ?_))
        · exact congrFun (congrArg Morphism.map t.1.1.hom_inv_id) p.1.1
        · exact congrFun (congrArg Morphism.map t.1.2.1.hom_inv_id) p.1.2
      inv_hom_id := by
        refine Morphism.ext' (funext fun p => Subtype.ext (Prod.ext ?_ ?_))
        · exact congrFun (congrArg Morphism.map t.1.1.inv_hom_id) p.1.1
        · exact congrFun (congrArg Morphism.map t.1.2.1.inv_hom_id) p.1.2 }
  map_one' := by
    refine Aut.ext ?_
    exact Morphism.ext' (funext fun p => Subtype.ext (Prod.ext rfl rfl))
  map_mul' s t := by
    refine Aut.ext ?_
    exact Morphism.ext' (funext fun p => Subtype.ext (Prod.ext rfl rfl))

@[simp] theorem pbAut_hom_map (t : autOverSubgroup F G) (p : (pbOnt F G).carrier) :
    ((pbAut F G t).hom.map p).1 = (t.1.1.hom.map p.1.1, t.1.2.1.hom.map p.1.2) := rfl

/-- **The first projection is equivariant**: projecting a moved matched pair is
moving the projection. -/
theorem pbAut_fst (t : autOverSubgroup F G) :
    (pbAut F G t).hom ≫ pbFst F G = pbFst F G ≫ t.1.1.hom := rfl

/-- **The second projection is equivariant.** -/
theorem pbAut_snd (t : autOverSubgroup F G) :
    (pbAut F G t).hom ≫ pbSnd F G = pbSnd F G ≫ t.1.2.1.hom := rfl

/-- The compatible triples act on the matched pairs of the pullback. -/
instance pbAutMulAction : MulAction (autOverSubgroup F G) (pbOnt F G).carrier :=
  MulAction.compHom _ ((autPerm (X := pbOnt F G)).comp (pbAut F G))

@[simp] theorem pbAut_smul_apply (t : autOverSubgroup F G) (p : (pbOnt F G).carrier) :
    (t • p).1 = (t.1.1.hom.map p.1.1, t.1.2.1.hom.map p.1.2) := rfl

/-- Projection is equivariant, pointwise. -/
theorem pbFst_smul (t : autOverSubgroup F G) (p : (pbOnt F G).carrier) :
    (pbFst F G).map (t • p) = t.1.1 • (pbFst F G).map p := rfl

theorem pbSnd_smul (t : autOverSubgroup F G) (p : (pbOnt F G).carrier) :
    (pbSnd F G).map (t • p) = t.1.2.1 • (pbSnd F G).map p := rfl

end Ontology
end Wikidata
