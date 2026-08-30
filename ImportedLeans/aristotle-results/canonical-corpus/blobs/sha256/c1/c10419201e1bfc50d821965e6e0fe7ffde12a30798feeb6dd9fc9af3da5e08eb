import RequestProject.OntologyLimits

/-!
# Colimits: the disjoint union of two ontologies

`RequestProject.CategoryOfOntologies` builds the *fibre product* of two
ontologies and `RequestProject.OntologyLimits` settles which other limits `Ont`
has.  This file does the dual, for the newly downloaded notions *coproduct*
(`Q692689`) and *colimit* (`Q111204834`): two ontologies can be placed side by
side, and the result is their coproduct in `Ont`.

* `Ontology.sumOnt X Y` — the **disjoint union** of two ontologies: the items are
  the items of `X` and the items of `Y`, each keeps its own `subclass of` and
  `instance of` statements and its own metaclass level, and no statement crosses
  from one side to the other.  That the metaclass discipline survives is
  immediate; that the class hierarchy stays acyclic needs
  `Ontology.reflTransGen_sumP279_inl` — a chain of `subclass of` steps starting
  on one side never leaves it.
* `Ontology.isColimit_sumCofan` — the two inclusions make it a **coproduct**, so
  `Ontology.hasBinaryCoproduct_ont` and `Ontology.instHasBinaryCoproductsOnt`:
  `Ont` has all binary coproducts.  Together with
  `Ontology.isInitial_emptyOnt` (the empty ontology is initial) this says `Ont`
  has all finite coproducts, in contrast with the terminal object it does *not*
  have.
* `Ontology.forgetOnt_faithful` — the forgetful functor to sets is **faithful**
  (`Q12175350`), so `Ont` is a *concrete category* (`Q1575634`): an ontology is a
  set of items with structure, and a morphism is a map of items with properties,
  never extra data.  `Ontology.forgetOnt_sumOnt` records that the forgetful
  functor takes the disjoint union of ontologies to the disjoint union of their
  item sets, so the coproduct is computed on underlying sets.
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u

/-! ### The disjoint union of two ontologies -/

variable (X Y : Ont.{u})

/-- `subclass of` on the disjoint union: the statements of each side, and
nothing across. -/
def sumP279 : X.carrier ⊕ Y.carrier → X.carrier ⊕ Y.carrier → Prop
  | .inl a, .inl b => X.str.P279 a b
  | .inr a, .inr b => Y.str.P279 a b
  | _, _ => False

/-- `instance of` on the disjoint union: the statements of each side, and
nothing across. -/
def sumP31 : X.carrier ⊕ Y.carrier → X.carrier ⊕ Y.carrier → Prop
  | .inl a, .inl c => X.str.P31 a c
  | .inr a, .inr c => Y.str.P31 a c
  | _, _ => False

variable {X Y}

/-- A chain of `subclass of` steps that starts on the left stays on the left,
and is a chain of the left ontology. -/
theorem reflTransGen_sumP279_inl {a : X.carrier} {c : X.carrier ⊕ Y.carrier}
    (h : Relation.ReflTransGen (sumP279 X Y) (.inl a) c) :
    ∃ b, c = .inl b ∧ Relation.ReflTransGen X.str.P279 a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | tail _ hstep ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      rename_i d _
      cases d with
      | inl d => exact ⟨d, rfl, hb.tail hstep⟩
      | inr d => exact absurd hstep (by simp [sumP279])

/-- The same on the right. -/
theorem reflTransGen_sumP279_inr {a : Y.carrier} {c : X.carrier ⊕ Y.carrier}
    (h : Relation.ReflTransGen (sumP279 X Y) (.inr a) c) :
    ∃ b, c = .inr b ∧ Relation.ReflTransGen Y.str.P279 a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | tail _ hstep ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      rename_i d _
      cases d with
      | inl d => exact absurd hstep (by simp [sumP279])
      | inr d => exact ⟨d, rfl, hb.tail hstep⟩

variable (X Y)

/-- **The disjoint union of two ontologies** as an ontology structure. -/
def sumStr : Ontology (X.carrier ⊕ Y.carrier) where
  P279 := sumP279 X Y
  P31 := sumP31 X Y
  level := Sum.elim X.str.level Y.str.level
  level_P31 := by
    rintro (a | a) (c | c) h
    · exact X.str.level_P31 h
    · exact absurd h (by simp [sumP31])
    · exact absurd h (by simp [sumP31])
    · exact Y.str.level_P31 h
  level_P279 := by
    rintro (a | a) (b | b) h
    · exact X.str.level_P279 h
    · exact absurd h (by simp [sumP279])
    · exact absurd h (by simp [sumP279])
    · exact Y.str.level_P279 h
  P279_isClass := by
    rintro (a | a) (b | b) h
    · exact X.str.P279_isClass h
    · exact absurd h (by simp [sumP279])
    · exact absurd h (by simp [sumP279])
    · exact Y.str.P279_isClass h
  P279_antisymm := by
    rintro (a | a) b hab hba
    · obtain ⟨b', rfl, hab'⟩ := reflTransGen_sumP279_inl hab
      obtain ⟨a', ha', hba'⟩ := reflTransGen_sumP279_inl hba
      cases ha'
      exact congrArg _ (X.str.P279_antisymm hab' hba')
    · obtain ⟨b', rfl, hab'⟩ := reflTransGen_sumP279_inr hab
      obtain ⟨a', ha', hba'⟩ := reflTransGen_sumP279_inr hba
      cases ha'
      exact congrArg _ (Y.str.P279_antisymm hab' hba')

/-- The disjoint union as an object of `Ont`. -/
def sumOnt : Ont.{u} := ⟨X.carrier ⊕ Y.carrier, sumStr X Y⟩

@[simp] theorem sumOnt_carrier : (sumOnt X Y).carrier = (X.carrier ⊕ Y.carrier) := rfl

/-- The inclusion of the left summand. -/
def sumInl : X ⟶ sumOnt X Y where
  map := Sum.inl
  map_P279 h := h
  map_P31 h := h

/-- The inclusion of the right summand. -/
def sumInr : Y ⟶ sumOnt X Y where
  map := Sum.inr
  map_P279 h := h
  map_P31 h := h

@[simp] theorem sumInl_map (a : X.carrier) : (sumInl X Y).map a = Sum.inl a := rfl
@[simp] theorem sumInr_map (b : Y.carrier) : (sumInr X Y).map b = Sum.inr b := rfl

variable {X Y}

/-- The morphism out of the disjoint union determined by a morphism on each
summand. -/
def sumDesc {Z : Ont.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : sumOnt X Y ⟶ Z where
  map := Sum.elim f.map g.map
  map_P279 := by
    rintro (a | a) (b | b) h
    · exact f.map_P279 h
    · exact absurd h (by simp [sumOnt, sumStr, sumP279])
    · exact absurd h (by simp [sumOnt, sumStr, sumP279])
    · exact g.map_P279 h
  map_P31 := by
    rintro (a | a) (c | c) h
    · exact f.map_P31 h
    · exact absurd h (by simp [sumOnt, sumStr, sumP31])
    · exact absurd h (by simp [sumOnt, sumStr, sumP31])
    · exact g.map_P31 h

@[simp] theorem sumDesc_map {Z : Ont.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (sumDesc f g).map = Sum.elim f.map g.map := rfl

/-! ### The disjoint union is the coproduct -/

variable (X Y)

/-- The two inclusions, as a cocone under the pair `X`, `Y`. -/
def sumCofan : BinaryCofan X Y := BinaryCofan.mk (sumInl X Y) (sumInr X Y)

@[simp] theorem sumCofan_pt : (sumCofan X Y).pt = sumOnt X Y := rfl

/-- **The disjoint union of two ontologies is their coproduct in `Ont`.** -/
def isColimit_sumCofan : IsColimit (sumCofan X Y) :=
  BinaryCofan.IsColimit.mk _ (fun f g => sumDesc f g)
    (fun _ _ => Morphism.ext' rfl) (fun _ _ => Morphism.ext' rfl)
    (fun f g m hf hg => Morphism.ext' (by
      funext p
      cases p with
      | inl a => exact congrFun (congrArg Morphism.map hf) a
      | inr b => exact congrFun (congrArg Morphism.map hg) b))

/-- So any two ontologies have a coproduct … -/
instance hasBinaryCoproduct_ont : HasBinaryCoproduct X Y :=
  ⟨⟨⟨_, isColimit_sumCofan X Y⟩⟩⟩

/-- … and `Ont` has all binary coproducts.  With the initial object of
`Ontology.isInitial_emptyOnt`, that is all finite coproducts — while `Ont` has
no terminal object at all (`Ontology.no_isTerminal`). -/
instance instHasBinaryCoproductsOnt : HasBinaryCoproducts Ont.{u} :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-! ### `Ont` is a concrete category -/

/-- **The forgetful functor is faithful**: a strict morphism of ontologies is
determined by its underlying map on items, so an ontology morphism carries no
data beyond a function.  This is what makes `Ont` a *concrete category*. -/
instance forgetOnt_faithful : forgetOnt.{u}.Faithful where
  map_injective h := Morphism.ext' h

/-- Spelled out: two morphisms with the same underlying map are equal. -/
theorem eq_of_forget_eq {X Y : Ont.{u}} {F G : X ⟶ Y}
    (h : forgetOnt.map F = forgetOnt.map G) : F = G :=
  forgetOnt.map_injective h

/-- The underlying set of a disjoint union of ontologies is the disjoint union
of the underlying sets, and the inclusions are the set-theoretic ones. -/
theorem forgetOnt_sumOnt (X Y : Ont.{u}) :
    forgetOnt.obj (sumOnt X Y) = (X.carrier ⊕ Y.carrier) ∧
      forgetOnt.map (sumInl X Y) = Sum.inl ∧ forgetOnt.map (sumInr X Y) = Sum.inr :=
  ⟨rfl, rfl, rfl⟩

end Ontology
end Wikidata
