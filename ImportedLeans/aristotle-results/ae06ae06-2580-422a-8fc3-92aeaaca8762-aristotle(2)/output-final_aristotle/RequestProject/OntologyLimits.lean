import RequestProject.CategoryOfOntologies

/-!
# Which limits the category of ontologies has

`RequestProject.CategoryOfOntologies` shows that `Ont` has all pullbacks.  This
file asks the other questions a reader of that file will ask next, and answers
them with the three small ontologies that decide them:

* `Ontology.ptOnt` — one item, no statements: morphisms out of it are exactly the
  items of the target, which is what makes monomorphisms detectable;
* `Ontology.emptyOnt` — no items at all;
* `Ontology.stepOnt` — two items, one an `instance of` the other.

The results:

* `Ontology.mono_iff_injective` — a strict morphism is a monomorphism exactly
  when its underlying map is injective (and `epi_of_surjective` for the easy
  half of the dual);
* `Ontology.isInitial_emptyOnt` — the empty ontology is an initial object, so
  `Ont` has an initial object;
* `Ontology.no_isTerminal` — **`Ont` has no terminal object**: a terminal
  ontology would have to have exactly one item, and an item cannot be an
  `instance of` itself because a class sits one metaclass level above its
  instances.  So `Ont` has all pullbacks but is *not* finitely complete, and in
  particular it is not the category of models of a limit theory.
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u

/-! ### Three small ontologies -/

/-- The **one-item ontology**: a single item and no statements at all. -/
def ptStr : Ontology PUnit.{u + 1} where
  P279 _ _ := False
  P31 _ _ := False
  level _ := 0
  level_P31 h := h.elim
  level_P279 h := h.elim
  P279_isClass h := h.elim
  P279_antisymm _ _ := rfl

/-- The one-item ontology as an object of `Ont`. -/
def ptOnt : Ont.{u} := ⟨PUnit, ptStr⟩

/-- A morphism out of the one-item ontology is just an item of the target. -/
def ptHom (X : Ont.{u}) (a : X.carrier) : ptOnt.{u} ⟶ X where
  map _ := a
  map_P279 h := h.elim
  map_P31 h := h.elim

@[simp] theorem ptHom_map (X : Ont.{u}) (a : X.carrier) (u : PUnit) :
    (ptHom X a).map u = a := rfl

/-- The **empty ontology**: no items, hence no statements. -/
def emptyStr : Ontology PEmpty.{u + 1} where
  P279 _ _ := False
  P31 _ _ := False
  level _ := 0
  level_P31 h := h.elim
  level_P279 h := h.elim
  P279_isClass h := h.elim
  P279_antisymm := fun {a} _ _ _ => a.elim

/-- The empty ontology as an object of `Ont`. -/
def emptyOnt : Ont.{u} := ⟨PEmpty, emptyStr⟩

/-- The **two-item ontology** `false : true`: one item is an `instance of` the
other, so the two sit at different metaclass levels. -/
def stepStr : Ontology (ULift.{u} Bool) where
  P279 _ _ := False
  P31 a c := a = ⟨false⟩ ∧ c = ⟨true⟩
  level b := if b.down then 1 else 0
  level_P31 := by rintro a c ⟨rfl, rfl⟩; rfl
  level_P279 h := h.elim
  P279_isClass h := h.elim
  P279_antisymm h _ := by
    induction h with
    | refl => rfl
    | tail _ h _ => exact h.elim

/-- The two-item ontology as an object of `Ont`. -/
def stepOnt : Ont.{u} := ⟨ULift Bool, stepStr⟩

/-- In the two-item ontology, `false` is an instance of `true`. -/
theorem stepOnt_P31 : stepOnt.{u}.str.P31 ⟨false⟩ ⟨true⟩ := ⟨rfl, rfl⟩

/-! ### Monomorphisms and epimorphisms -/

/-- A morphism with injective underlying map is a monomorphism. -/
theorem mono_of_injective {X Y : Ont.{u}} (f : X ⟶ Y) (hf : Function.Injective f.map) :
    Mono f := by
  refine ⟨fun {W} g h hgh => Morphism.ext' (funext fun w => hf ?_)⟩
  exact congrFun (congrArg Morphism.map hgh) w

/-- A monomorphism has injective underlying map: the one-item ontology sees the
two items apart. -/
theorem injective_of_mono {X Y : Ont.{u}} (f : X ⟶ Y) [Mono f] : Function.Injective f.map := by
  intro a b hab
  have h : ptHom X a ≫ f = ptHom X b ≫ f := Morphism.ext' (funext fun _ => hab)
  have := (cancel_mono f).1 h
  exact congrFun (congrArg Morphism.map this) PUnit.unit

/-- **A strict morphism of ontologies is a monomorphism exactly when it is
injective on items.** -/
theorem mono_iff_injective {X Y : Ont.{u}} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.map :=
  ⟨fun _ => injective_of_mono f, mono_of_injective f⟩

/-- A morphism with surjective underlying map is an epimorphism. -/
theorem epi_of_surjective {X Y : Ont.{u}} (f : X ⟶ Y) (hf : Function.Surjective f.map) :
    Epi f := by
  refine ⟨fun {W} g h hgh => Morphism.ext' (funext fun y => ?_)⟩
  obtain ⟨x, rfl⟩ := hf y
  exact congrFun (congrArg Morphism.map hgh) x

/-! ### The initial object -/

/-- **The empty ontology is an initial object of `Ont`.** -/
def isInitial_emptyOnt : IsInitial emptyOnt.{u} :=
  IsInitial.ofUniqueHom
    (fun _ => { map := fun a => a.elim, map_P279 := fun {a} _ => a.elim,
                map_P31 := fun {a} _ => a.elim })
    (fun _ _ => Morphism.ext' (funext fun a => a.elim))

/-- So `Ont` has an initial object. -/
theorem hasInitial_ont : HasInitial Ont.{u} := isInitial_emptyOnt.hasInitial

/-! ### There is no terminal object -/

/-- A terminal ontology has at most one item: the two items of a discrete
two-item ontology would give two different morphisms into it. -/
theorem subsingleton_of_isTerminal {T : Ont.{u}} (hT : IsTerminal T) :
    Subsingleton T.carrier := by
  refine ⟨fun s t => ?_⟩
  have hs : ptHom T s = hT.from ptOnt := hT.hom_ext _ _
  have ht : ptHom T t = hT.from ptOnt := hT.hom_ext _ _
  have : ptHom T s = ptHom T t := hs.trans ht.symm
  exact congrFun (congrArg Morphism.map this) PUnit.unit

/-- **The category of ontologies has no terminal object.**  A terminal ontology
would have a single item `t`, and the morphism out of the two-item ontology
`false : true` would make `t` an `instance of` itself — impossible, since a
class sits exactly one metaclass level above its instances. -/
theorem no_isTerminal (T : Ont.{u}) (hT : IsTerminal T) : False := by
  have hsub : Subsingleton T.carrier := subsingleton_of_isTerminal hT
  set f : stepOnt.{u} ⟶ T := hT.from stepOnt with hf
  have h31 : T.str.P31 (f.map ⟨false⟩) (f.map ⟨true⟩) := f.map_P31 stepOnt_P31
  have hlevel : T.str.level (f.map ⟨true⟩) = T.str.level (f.map ⟨false⟩) + 1 :=
    T.str.level_P31 h31
  have : f.map ⟨true⟩ = f.map ⟨false⟩ := hsub.allEq _ _
  rw [this] at hlevel
  omega

/-- Spelled out: no object of `Ont` is terminal, so `Ont` — which has all
pullbacks — is not finitely complete. -/
theorem not_hasTerminal : ¬ HasTerminal Ont.{u} := by
  intro h
  exact no_isTerminal (⊤_ Ont.{u}) terminalIsTerminal

end Ontology
end Wikidata
