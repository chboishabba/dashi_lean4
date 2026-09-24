import RequestProject.Alignment
import RequestProject.Concepts

/-!
# Reduction, pullback, retraction and Frobenius reciprocity for ontologies

This file adds the categorical apparatus that the meta-level layer of the
development needs, phrased for the abstract `Wikidata.Ontology` model of
*Wikidata:WikiProject Ontology*.

Four constructions, each the ontological reading of a standard notion:

* **Reduction** (`Ontology.comap`, `Ontology.restrict`). An ontology can be read
  through an injective renaming of its identifiers, or restricted to a
  sub-vocabulary. The result is again an ontology and the renaming is an
  alignment, so a reduct never invents `subclass of` or `instance of` facts.

* **Pullback** (`Ontology.pullback`). Two ontologies mapped into a common
  reference ontology have a fibre product: the ontology of *matched pairs*, the
  items of the two that the alignments identify. It comes with two projections,
  a commuting square, and the universal property (`Ontology.pullback.lift`,
  `Ontology.pullback.lift_unique`) — this is exactly the operation that "aligns
  two ontologies over a third".

* **Retraction** (`Ontology.Retract`). A section–retraction pair: an ontology
  embedded in a larger one together with a map back that undoes the embedding.
  The point is `Retract.subclassOf_iff` and `Retract.instanceOf_iff`: a retract
  is a *conservative* extension, the big ontology derives no new facts about the
  embedded items. The composite `section ∘ retraction` is an idempotent
  endomorphism, and idempotents that split this way are precisely retracts.

* **Frobenius reciprocity** (`Ontology.Alignment.push`, `Alignment.pull`).
  Class extensions (the sets of instances) can be pushed forward and pulled back
  along an alignment; pushforward is left adjoint to pullback
  (`Alignment.push_subset_iff`) and the projection formula
  `Alignment.projection_formula` — `f_*(A ⊓ f^*B) = f_*A ⊓ B` — holds. For a
  retract the pullback of an extension is exact (`Retract.preimage_extension`).

Morphisms come in two strengths. `Ontology.Alignment` (from
`RequestProject.Alignment`) is the *lax* notion used for ontology matching: an
asserted statement may be matched by a *derived* fact. `Ontology.Morphism`,
defined here, is the strict notion, sending direct statements to direct
statements; strict morphisms are what the pullback is a limit of.
-/

namespace Wikidata
namespace Ontology

variable {I J K L : Type*}

/-! ## Strict morphisms -/

/-- A **strict morphism** of ontologies: a map of identifiers sending direct
`subclass of` and `instance of` statements to direct statements. Every strict
morphism is in particular an alignment (`Morphism.toAlignment`). -/
structure Morphism (O₁ : Ontology I) (O₂ : Ontology J) where
  /-- The underlying map on identifiers. -/
  map : I → J
  /-- Direct `subclass of` statements are sent to direct `subclass of` statements. -/
  map_P279 : ∀ {a b}, O₁.P279 a b → O₂.P279 (map a) (map b)
  /-- Direct `instance of` statements are sent to direct `instance of` statements. -/
  map_P31 : ∀ {a c}, O₁.P31 a c → O₂.P31 (map a) (map c)

namespace Morphism

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}

/-- A strict morphism is an alignment. -/
def toAlignment (F : Morphism O₁ O₂) : Alignment O₁ O₂ where
  map := F.map
  map_P279 h := subclassOf_of_P279 (F.map_P279 h)
  map_P31 h := instanceOf_of_P31 (F.map_P31 h)

@[simp] theorem toAlignment_map (F : Morphism O₁ O₂) : F.toAlignment.map = F.map := rfl

/-- The identity morphism. -/
def id (O : Ontology I) : Morphism O O where
  map := _root_.id
  map_P279 h := h
  map_P31 h := h

@[simp] theorem id_map (O : Ontology I) : (Morphism.id O).map = _root_.id := rfl

/-- Composition of strict morphisms. -/
def comp (F : Morphism O₁ O₂) (G : Morphism O₂ O₃) : Morphism O₁ O₃ where
  map := G.map ∘ F.map
  map_P279 h := G.map_P279 (F.map_P279 h)
  map_P31 h := G.map_P31 (F.map_P31 h)

@[simp] theorem comp_map (F : Morphism O₁ O₂) (G : Morphism O₂ O₃) :
    (F.comp G).map = G.map ∘ F.map := rfl

/-- The derived class hierarchy transfers along a strict morphism. -/
theorem subclassOf (F : Morphism O₁ O₂) {a b : I} (h : O₁.SubclassOf a b) :
    O₂.SubclassOf (F.map a) (F.map b) := F.toAlignment.subclassOf h

/-- The derived instance relation transfers along a strict morphism. -/
theorem instanceOf (F : Morphism O₁ O₂) {a c : I} (h : O₁.InstanceOf a c) :
    O₂.InstanceOf (F.map a) (F.map c) := F.toAlignment.instanceOf h

end Morphism

/-! ## Reduction: reading an ontology through an injective renaming -/

theorem reflTransGen_comap {O : Ontology J} {f : I → J} {a b : I}
    (h : Relation.ReflTransGen (fun x y => O.P279 (f x) (f y)) a b) :
    Relation.ReflTransGen O.P279 (f a) (f b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc

/-- **Reduction.** The ontology obtained by reading `O` through the injective
renaming `f`: the statements are exactly the statements of `O` between renamed
items. -/
def comap (O : Ontology J) (f : I → J) (hf : Function.Injective f) : Ontology I where
  P279 a b := O.P279 (f a) (f b)
  P31 a c := O.P31 (f a) (f c)
  level a := O.level (f a)
  level_P31 h := O.level_P31 h
  level_P279 h := O.level_P279 h
  P279_isClass h := O.P279_isClass h
  P279_antisymm hab hba :=
    hf (O.P279_antisymm (reflTransGen_comap hab) (reflTransGen_comap hba))

@[simp] theorem comap_level (O : Ontology J) (f : I → J) (hf : Function.Injective f) (a : I) :
    (O.comap f hf).level a = O.level (f a) := rfl

/-- The renaming underlying a reduction is a strict morphism into the original
ontology. -/
def comapMorphism (O : Ontology J) (f : I → J) (hf : Function.Injective f) :
    Morphism (O.comap f hf) O where
  map := f
  map_P279 h := h
  map_P31 h := h

@[simp] theorem comapMorphism_map (O : Ontology J) (f : I → J) (hf : Function.Injective f) :
    (O.comapMorphism f hf).map = f := rfl

/-- A reduction invents nothing: a derived `subclass of` fact of the reduct is a
derived fact of the original ontology. -/
theorem comap_subclassOf {O : Ontology J} {f : I → J} {hf : Function.Injective f} {a b : I}
    (h : (O.comap f hf).SubclassOf a b) : O.SubclassOf (f a) (f b) :=
  (O.comapMorphism f hf).subclassOf h

/-- A reduction invents nothing: a derived `instance of` fact of the reduct is a
derived fact of the original ontology. -/
theorem comap_instanceOf {O : Ontology J} {f : I → J} {hf : Function.Injective f} {a c : I}
    (h : (O.comap f hf).InstanceOf a c) : O.InstanceOf (f a) (f c) :=
  (O.comapMorphism f hf).instanceOf h

/-- The **sub-ontology** carried by a sub-vocabulary `S`: the reduct of `O` along
the inclusion of `S`.  (`Ontology.restrict`, in `RequestProject.Provenance`, is
the other kind of reduct: it keeps all items but only selected statements.) -/
def subVocabulary (O : Ontology I) (S : Set I) : Ontology S :=
  O.comap Subtype.val Subtype.val_injective

@[simp] theorem subVocabulary_level (O : Ontology I) (S : Set I) (a : S) :
    (O.subVocabulary S).level a = O.level a.1 := rfl

/-- The inclusion of a sub-vocabulary is a strict morphism. -/
def subVocabularyMorphism (O : Ontology I) (S : Set I) : Morphism (O.subVocabulary S) O :=
  O.comapMorphism Subtype.val Subtype.val_injective

@[simp] theorem subVocabularyMorphism_map (O : Ontology I) (S : Set I) :
    (O.subVocabularyMorphism S).map = Subtype.val := rfl

/-! ## Pullback: the fibre product of two ontologies over a third -/

/-- The carrier of the pullback: pairs of items that the two alignments identify
in the reference ontology. -/
def PullbackCarrier {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}
    (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) : Type _ :=
  {p : I × J // F.map p.1 = G.map p.2}

instance {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}
    (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    CoeOut (PullbackCarrier F G) (I × J) := ⟨Subtype.val⟩

theorem reflTransGen_fst {R : I → I → Prop} {S : J → J → Prop} {p q : I × J}
    (h : Relation.ReflTransGen (fun u v : I × J => R u.1 v.1 ∧ S u.2 v.2) p q) :
    Relation.ReflTransGen R p.1 q.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.1

theorem reflTransGen_snd {R : I → I → Prop} {S : J → J → Prop} {p q : I × J}
    (h : Relation.ReflTransGen (fun u v : I × J => R u.1 v.1 ∧ S u.2 v.2) p q) :
    Relation.ReflTransGen S p.2 q.2 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.2

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K} {O₀ : Ontology L}

/-- **Pullback.** The fibre product of `F : O₁ ⟶ O₃` and `G : O₂ ⟶ O₃`: its items
are the matched pairs, and a statement holds of a pair exactly when it holds of
both components. -/
def pullback (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) : Ontology (PullbackCarrier F G) where
  P279 p q := O₁.P279 p.1.1 q.1.1 ∧ O₂.P279 p.1.2 q.1.2
  P31 p q := O₁.P31 p.1.1 q.1.1 ∧ O₂.P31 p.1.2 q.1.2
  level p := O₁.level p.1.1
  level_P31 h := O₁.level_P31 h.1
  level_P279 h := O₁.level_P279 h.1
  P279_isClass h := O₁.P279_isClass h.1
  P279_antisymm := by
    intro a b hab hba
    have h1 : a.1.1 = b.1.1 :=
      O₁.P279_antisymm (reflTransGen_fst (R := O₁.P279) (S := O₂.P279)
          (p := a.1) (q := b.1) (by
            refine Relation.ReflTransGen.lift (fun x : PullbackCarrier F G => x.1) ?_ hab
            intro x y hxy; exact hxy))
        (reflTransGen_fst (R := O₁.P279) (S := O₂.P279) (p := b.1) (q := a.1) (by
            refine Relation.ReflTransGen.lift (fun x : PullbackCarrier F G => x.1) ?_ hba
            intro x y hxy; exact hxy))
    have h2 : a.1.2 = b.1.2 :=
      O₂.P279_antisymm (reflTransGen_snd (R := O₁.P279) (S := O₂.P279)
          (p := a.1) (q := b.1) (by
            refine Relation.ReflTransGen.lift (fun x : PullbackCarrier F G => x.1) ?_ hab
            intro x y hxy; exact hxy))
        (reflTransGen_snd (R := O₁.P279) (S := O₂.P279) (p := b.1) (q := a.1) (by
            refine Relation.ReflTransGen.lift (fun x : PullbackCarrier F G => x.1) ?_ hba
            intro x y hxy; exact hxy))
    exact Subtype.ext (Prod.ext h1 h2)

namespace pullback

variable (F : Morphism O₁ O₃) (G : Morphism O₂ O₃)

/-- The first projection of the pullback. -/
def fst : Morphism (pullback F G) O₁ where
  map p := p.1.1
  map_P279 h := h.1
  map_P31 h := h.1

/-- The second projection of the pullback. -/
def snd : Morphism (pullback F G) O₂ where
  map p := p.1.2
  map_P279 h := h.2
  map_P31 h := h.2

@[simp] theorem fst_map (p : PullbackCarrier F G) : (fst F G).map p = p.1.1 := rfl
@[simp] theorem snd_map (p : PullbackCarrier F G) : (snd F G).map p = p.1.2 := rfl

/-- **The pullback square commutes.** -/
theorem comm : ((fst F G).comp F).map = ((snd F G).comp G).map := by
  funext p; exact p.2

/-- **The universal property, existence.** A pair of strict morphisms out of `O₀`
that agree in the reference ontology factors through the pullback. -/
def lift (A : Morphism O₀ O₁) (B : Morphism O₀ O₂)
    (h : ∀ x, F.map (A.map x) = G.map (B.map x)) : Morphism O₀ (pullback F G) where
  map x := ⟨(A.map x, B.map x), h x⟩
  map_P279 hab := ⟨A.map_P279 hab, B.map_P279 hab⟩
  map_P31 hac := ⟨A.map_P31 hac, B.map_P31 hac⟩

@[simp] theorem lift_fst (A : Morphism O₀ O₁) (B : Morphism O₀ O₂)
    (h : ∀ x, F.map (A.map x) = G.map (B.map x)) :
    ((lift F G A B h).comp (fst F G)).map = A.map := rfl

@[simp] theorem lift_snd (A : Morphism O₀ O₁) (B : Morphism O₀ O₂)
    (h : ∀ x, F.map (A.map x) = G.map (B.map x)) :
    ((lift F G A B h).comp (snd F G)).map = B.map := rfl

/-- **The universal property, uniqueness.** Any strict morphism into the pullback
is determined by its two components. -/
theorem lift_unique (M N : Morphism O₀ (pullback F G))
    (h1 : (M.comp (fst F G)).map = (N.comp (fst F G)).map)
    (h2 : (M.comp (snd F G)).map = (N.comp (snd F G)).map) : M.map = N.map := by
  funext x
  exact Subtype.ext (Prod.ext (congrFun h1 x) (congrFun h2 x))

end pullback

/-! ## Retraction -/

/-- A **retract** of `O₂` onto `O₁`: an embedding `sec` together with a map `ret`
back that undoes it. -/
structure Retract (O₁ : Ontology I) (O₂ : Ontology J) where
  /-- The embedding of the small ontology into the big one. -/
  sec : Morphism O₁ O₂
  /-- The map back. -/
  ret : Morphism O₂ O₁
  /-- The embedding is undone by the retraction. -/
  ret_sec : ∀ a, ret.map (sec.map a) = a

namespace Retract

variable {O₁ : Ontology I} {O₂ : Ontology J} (R : Retract O₁ O₂)

/-- The embedding of a retract is injective. -/
theorem sec_injective : Function.Injective R.sec.map := by
  intro a b hab
  have := congrArg R.ret.map hab
  rwa [R.ret_sec, R.ret_sec] at this

/-- **A retract is a conservative extension for the class hierarchy**: the big
ontology derives a `subclass of` fact between embedded items only if the small
one already does. -/
theorem subclassOf_iff {a b : I} :
    O₂.SubclassOf (R.sec.map a) (R.sec.map b) ↔ O₁.SubclassOf a b := by
  constructor
  · intro h
    have := R.ret.subclassOf h
    rwa [R.ret_sec, R.ret_sec] at this
  · exact fun h => R.sec.subclassOf h

/-- **A retract is a conservative extension for the instance relation.** -/
theorem instanceOf_iff {a c : I} :
    O₂.InstanceOf (R.sec.map a) (R.sec.map c) ↔ O₁.InstanceOf a c := by
  constructor
  · intro h
    have := R.ret.instanceOf h
    rwa [R.ret_sec, R.ret_sec] at this
  · exact fun h => R.sec.instanceOf h

/-- Classhood is reflected by a retract. -/
theorem hasInstance_iff {c : I} : O₂.HasInstance (R.sec.map c) ↔ O₁.HasInstance c := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨R.ret.map x, by simpa [R.ret_sec] using R.ret.instanceOf hx⟩
  · rintro ⟨a, ha⟩
    exact ⟨R.sec.map a, R.sec.instanceOf ha⟩

/-- Metaclasshood is reflected by a retract. -/
theorem isMetaclass_iff {c : I} : O₂.IsMetaclass (R.sec.map c) ↔ O₁.IsMetaclass c := by
  constructor
  · rintro ⟨x, hx, hxi⟩
    refine ⟨R.ret.map x, ?_, ?_⟩
    · simpa [R.ret_sec] using R.ret.instanceOf hx
    · obtain ⟨y, hy⟩ := hxi
      exact ⟨R.ret.map y, R.ret.instanceOf hy⟩
  · exact fun h => R.sec.toAlignment.isMetaclass h

/-- The composite `sec ∘ ret` is an **idempotent** endomorphism of the big
ontology. -/
def idem : Morphism O₂ O₂ := R.ret.comp R.sec

@[simp] theorem idem_map (x : J) : R.idem.map x = R.sec.map (R.ret.map x) := rfl

theorem idem_idempotent (x : J) : R.idem.map (R.idem.map x) = R.idem.map x := by
  simp [idem_map, R.ret_sec]

/-- The fixed points of the idempotent are exactly the embedded items. -/
theorem idem_fixed_iff (x : J) : R.idem.map x = x ↔ ∃ a, R.sec.map a = x := by
  constructor
  · intro h; exact ⟨R.ret.map x, h⟩
  · rintro ⟨a, rfl⟩; simp [idem_map, R.ret_sec]

end Retract

/-! ## Frobenius reciprocity for class extensions -/

namespace Alignment

variable {O₁ : Ontology I} {O₂ : Ontology J}

/-- Pushforward of a set of items along an alignment. -/
def push (F : Alignment O₁ O₂) (A : Set I) : Set J := F.map '' A

/-- Pullback of a set of items along an alignment. -/
def pull (F : Alignment O₁ O₂) (B : Set J) : Set I := F.map ⁻¹' B

/-- **Pushforward is left adjoint to pullback.** -/
theorem push_subset_iff (F : Alignment O₁ O₂) (A : Set I) (B : Set J) :
    F.push A ⊆ B ↔ A ⊆ F.pull B := Set.image_subset_iff

theorem subset_pull_push (F : Alignment O₁ O₂) (A : Set I) : A ⊆ F.pull (F.push A) :=
  Set.subset_preimage_image _ _

theorem push_pull_subset (F : Alignment O₁ O₂) (B : Set J) : F.push (F.pull B) ⊆ B :=
  Set.image_preimage_subset _ _

/-- **The projection formula (Frobenius reciprocity)**: `f_*(A ⊓ f^*B) = f_*A ⊓ B`. -/
theorem projection_formula (F : Alignment O₁ O₂) (A : Set I) (B : Set J) :
    F.push (A ∩ F.pull B) = F.push A ∩ B := Set.image_inter_preimage _ _ _

/-- Pushforward and pullback are monotone. -/
theorem push_mono (F : Alignment O₁ O₂) {A A' : Set I} (h : A ⊆ A') : F.push A ⊆ F.push A' :=
  Set.image_mono h

theorem pull_mono (F : Alignment O₁ O₂) {B B' : Set J} (h : B ⊆ B') : F.pull B ⊆ F.pull B' :=
  fun _ hx => h hx

/-- **Alignments respect extensions**: instances of a class are sent to instances
of the aligned class. -/
theorem push_extension_subset (F : Alignment O₁ O₂) (c : I) :
    F.push (O₁.extension c) ⊆ O₂.extension (F.map c) := by
  rintro _ ⟨a, ha, rfl⟩
  exact F.instanceOf ha

theorem extension_subset_pull_extension (F : Alignment O₁ O₂) (c : I) :
    O₁.extension c ⊆ F.pull (O₂.extension (F.map c)) :=
  (F.push_subset_iff _ _).1 (F.push_extension_subset c)

end Alignment

/-- **For a retract the pullback of an extension is exact**: pulling the extension
of an embedded class back along the embedding returns the extension itself, so no
instances are gained by passing to the larger ontology. -/
theorem Retract.preimage_extension {O₁ : Ontology I} {O₂ : Ontology J} (R : Retract O₁ O₂) (c : I) :
    R.sec.toAlignment.pull (O₂.extension (R.sec.map c)) = O₁.extension c := by
  ext a
  simpa [Alignment.pull, Ontology.extension] using R.instanceOf_iff (a := a) (c := c)

end Ontology
end Wikidata
