import RequestProject.CategoryOfOntologies

/-!
# Homotopy type theory: the pullback as a homotopy fibre product

*Wikidata: homotopy type theory (Q5891840), identity type (Q110720714),
fibration (Q493941), bijection (Q180907), pullback (Q1397439).*

Homotopy type theory reads the identity type `a = b` as a **path** and a family
`fun b => {a // f a = b}` as the **fibres** of a map.  In those terms the fibre
product of two ontologies is not a subset of a product, it is the type of
*triples*

  `(x, y, p)`  with `x` an item of `X`, `y` an item of `Y` and `p : F x = G y`

— a path in the reference ontology witnessing that the two alignments identify
`x` and `y`.  That is `Ontology.pullbackEquivSigma`, and everything else in the
file follows from it:

* `Ontology.fibPbFstEquiv` — **base change of fibrations**: the fibre of the
  first projection over an item `x` is the fibre of `G` over `F x`, so the fibre
  product really does fibre the second ontology over the first;
* `Ontology.pbFstEquivOfBijective` — **base change of an equivalence is an
  equivalence**: if `G` is bijective on items then so is the projection
  `pbFst`, and the fibre product is (equivalent to) `X` itself;
* `Ontology.pullbackCongrEquiv` — **homotopy invariance**: pointwise equal
  alignments have equivalent fibre products;
* `Ontology.pullbackPasteEquiv` — **the pasting lemma**: pulling back twice in
  a row is pulling back along the composite, and
  `Ontology.isPullback_paste` is the same statement in the categorical language
  of `RequestProject.CategoryOfOntologies`;
* `Ontology.pullbackSwapEquiv` — the fibre product is symmetric in its two
  arguments.

A caveat on the reading: Lean's identity types satisfy uniqueness of identity
proofs, so what is formalised here is the `h`-set fragment of the homotopy
interpretation — paths compose and invert, but there are no non-trivial higher
paths, and univalence is not available.
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u

variable {X Y Z W : Ont.{u}}

/-! ## Fibres -/

/-- **The fibre of a map over a point** — the homotopy fibre, the type of items
sent to `b` together with the path witnessing it. -/
def Fib {A B : Type*} (f : A → B) (b : B) : Type _ := {a : A // f a = b}

@[simp] theorem mem_fib {A B : Type*} {f : A → B} {b : B} (x : Fib f b) : f x.1 = b := x.2

/-- A map is injective exactly when its fibres are subsingletons, and surjective
exactly when they are inhabited. -/
theorem bijective_iff_fib_unique {A B : Type*} (f : A → B) :
    Function.Bijective f ↔ ∀ b, Nonempty (Fib f b) ∧ ∀ x y : Fib f b, x = y := by
  constructor
  · rintro ⟨hinj, hsurj⟩ b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨⟨⟨a, ha⟩⟩, fun x y => Subtype.ext (hinj (x.2.trans y.2.symm))⟩
  · intro h
    constructor
    · intro a a' haa'
      have := (h (f a)).2 ⟨a, rfl⟩ ⟨a', haa'.symm⟩
      exact congrArg Subtype.val this
    · intro b
      obtain ⟨⟨a, ha⟩⟩ := (h b).1
      exact ⟨a, ha⟩

/-! ## The fibre product as a type of triples -/

/-- **The fibre product is the type of matched triples**: an item of `X`, an item
of `Y`, and a path between their images in the reference ontology. -/
def pullbackEquivSigma (F : X ⟶ Z) (G : Y ⟶ Z) :
    (pbOnt F G).carrier ≃ Σ x : X.carrier, {y : Y.carrier // F.map x = G.map y} where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun t := ⟨(t.1, t.2.1), t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Base change of fibrations.** The fibre of the first projection over an item
`x` of `X` is the fibre of `G` over the image of `x`. -/
def fibPbFstEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (x : X.carrier) :
    Fib (pbFst F G).map x ≃ Fib G.map (F.map x) where
  toFun q := ⟨q.1.1.2, q.1.2.symm.trans (congrArg F.map q.2)⟩
  invFun r := ⟨⟨(x, r.1), r.2.symm⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨a, b⟩, hab⟩, hq⟩ := q
    cases hq
    rfl
  right_inv _ := rfl

/-- Symmetrically, the fibre of the second projection over an item `y` of `Y` is
the fibre of `F` over the image of `y`. -/
def fibPbSndEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (y : Y.carrier) :
    Fib (pbSnd F G).map y ≃ Fib F.map (G.map y) where
  toFun q := ⟨q.1.1.1, q.1.2.trans (congrArg G.map q.2)⟩
  invFun r := ⟨⟨(r.1, y), r.2⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨a, b⟩, hab⟩, hq⟩ := q
    cases hq
    rfl
  right_inv _ := rfl

/-- **Base change of an equivalence is an equivalence.** If the second alignment
is bijective on items, the fibre product is just the first ontology. -/
noncomputable def pbFstEquivOfBijective (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : Function.Bijective G.map) : (pbOnt F G).carrier ≃ X.carrier := by
  refine Equiv.ofBijective (pbFst F G).map ⟨?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
    have ha : a = a' := h
    subst ha
    have : G.map b = G.map b' := by rw [← hab, hab']
    have hb : b = b' := hG.1 this
    subst hb
    rfl
  · exact pbFst_surjective_of_surjective F G hG.2

/-! ## Homotopy invariance -/

/-- **Homotopy invariance of the fibre product.** Two alignments that agree
pointwise on items have equivalent fibre products. -/
def pullbackCongrEquiv {F F' : X ⟶ Z} {G G' : Y ⟶ Z} (hF : ∀ x, F.map x = F'.map x)
    (hG : ∀ y, G.map y = G'.map y) : (pbOnt F G).carrier ≃ (pbOnt F' G').carrier where
  toFun p := ⟨p.1, by rw [← hF, ← hG]; exact p.2⟩
  invFun q := ⟨q.1, by rw [hF, hG]; exact q.2⟩
  left_inv p := rfl
  right_inv q := rfl

/-! ## Pasting -/

/-- **The pasting lemma, as an equivalence of types.** Pulling `H : W ⟶ Y` back
along the second projection of the fibre product of `F` and `G` is the same as
pulling back along the composite `H ≫ G`. -/
def pullbackPasteEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (H : W ⟶ Y) :
    (pbOnt (pbSnd F G) H).carrier ≃ (pbOnt F (H ≫ G)).carrier where
  toFun q := ⟨(q.1.1.1.1, q.1.2), by
    have h₁ : F.map q.1.1.1.1 = G.map q.1.1.1.2 := q.1.1.2
    have h₂ : q.1.1.1.2 = H.map q.1.2 := q.2
    rw [h₁, h₂]; rfl⟩
  invFun r := ⟨(⟨(r.1.1, H.map r.1.2), r.2⟩, r.1.2), rfl⟩
  left_inv q := Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl q.2.symm)) rfl)
  right_inv _ := rfl

/-- The pasting lemma in categorical form: the outer rectangle of two pullback
squares is a pullback square. -/
theorem isPullback_paste (F : X ⟶ Z) (G : Y ⟶ Z) (H : W ⟶ Y) :
    IsPullback (pbFst (pbSnd F G) H ≫ pbFst F G) (pbSnd (pbSnd F G) H) F (H ≫ G) :=
  IsPullback.paste_horiz (isPullback_pbOnt (pbSnd F G) H) (isPullback_pbOnt F G)

/-! ## Symmetry -/

/-- The fibre product is symmetric: swapping the two alignments swaps the two
components of a matched pair. -/
def pullbackSwapEquiv (F : X ⟶ Z) (G : Y ⟶ Z) :
    (pbOnt F G).carrier ≃ (pbOnt G F).carrier where
  toFun p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  invFun q := ⟨(q.1.2, q.1.1), q.2.symm⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, hab⟩ := p
    rfl
  right_inv q := by
    obtain ⟨⟨b, a⟩, hba⟩ := q
    rfl

/-! ## Transport -/

/-- **Transport along a path of items.** A statement about an item can be moved
along an identification of items — the `subst` rule of type theory, applied to
the `subclass of` relation. -/
theorem subclassOf_transport {O : Ontology X.carrier} {a a' b : X.carrier} (p : a = a')
    (h : O.SubclassOf a b) : O.SubclassOf a' b := p ▸ h

/-- Paths in the reference ontology compose: the matched pairs of a fibre product
are closed under composing the witnessing identifications. -/
theorem pullback_path_trans (F : X ⟶ Z) (G : Y ⟶ Z) (p : (pbOnt F G).carrier)
    {z : Z.carrier} (q : G.map p.1.2 = z) : F.map p.1.1 = z := p.2.trans q

end Ontology
end Wikidata
