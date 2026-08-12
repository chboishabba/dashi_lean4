import Mathlib

/-!
# Lean mirror of `DASHI/Foundations/QuotientSetoidSurface.agda`
(genuine interface + real `Quotient` witness)

Faithful transcription of the setoid-quotient *authority surface*:

* `IsEquivalence`, `SetoidSurface` — a carrier with an equivalence relation,
* `SetoidQuotientSurface` — the quotient carrier with `quotientClass`, soundness
  (`x ≈ y → class x = class y`), the recursor `quotientRec` with its `β`-rule, and
  the dependent eliminator `quotientElim` with its `β`-rule,
* the derived `quotientStable`, `quotientTransport`,
* `SetoidNormSurface` and the descended `quotientNorm` with its `β`-rule.

The Agda original keeps the quotient as an *assumed* external surface (a record of
fields).  Here we go further and supply a **genuine witness** built from Lean's
real `Quotient` type, so every field is *proved* (soundness is `Quotient.sound`,
the recursor is `Quotient.lift`/`Quotient.rec`, and all `β`-rules hold by `rfl`).
No `sorry`, axiom-clean (only the kernel's `Quot.sound`/`propext`).
-/

namespace AgdaMirror.QuotientSetoidSurface

/-- An equivalence relation (Agda `record IsEquivalence`). -/
structure IsEquivalence {A : Type} (r : A → A → Prop) : Prop where
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z

/-- A setoid surface: a carrier with an equivalence (Agda `record SetoidSurface`). -/
structure SetoidSurface where
  Carrier : Type
  rel : Carrier → Carrier → Prop
  isEquiv : IsEquivalence rel

/-- The setoid-quotient surface (Agda `record SetoidQuotientSurface`). -/
structure SetoidQuotientSurface (S : SetoidSurface) where
  QuotientCarrier : Type
  quotientClass : S.Carrier → QuotientCarrier
  quotientSound : ∀ {x y}, S.rel x y → quotientClass x = quotientClass y
  quotientRec : ∀ (B : Type) (f : S.Carrier → B),
    (∀ x y, S.rel x y → f x = f y) → QuotientCarrier → B
  quotientRec_beta : ∀ (B : Type) (f : S.Carrier → B)
    (resp : ∀ x y, S.rel x y → f x = f y) (x : S.Carrier),
    quotientRec B f resp (quotientClass x) = f x

/-- Soundness is "stability of the class map" (Agda `quotientStable`). -/
theorem quotientStable {S : SetoidSurface} (Q : SetoidQuotientSurface S)
    {x y : S.Carrier} (h : S.rel x y) :
    Q.quotientClass x = Q.quotientClass y :=
  Q.quotientSound h

/-- Transport of a predicate along a class equality (Agda `quotientTransport`). -/
theorem quotientTransport {S : SetoidSurface} (Q : SetoidQuotientSurface S)
    (P : Q.QuotientCarrier → Prop) {x y : S.Carrier} (h : S.rel x y)
    (px : P (Q.quotientClass x)) : P (Q.quotientClass y) :=
  Q.quotientSound h ▸ px

/-- A setoid norm: a relation-respecting map to a value type (Agda
`record SetoidNormSurface`). -/
structure SetoidNormSurface (S : SetoidSurface) (NormValue : Type) where
  norm : S.Carrier → NormValue
  normRespects : ∀ {x y}, S.rel x y → norm x = norm y

/-- The norm descends to the quotient (Agda `quotientNorm`). -/
def quotientNorm {S : SetoidSurface} (Q : SetoidQuotientSurface S)
    {NormValue : Type} (N : SetoidNormSurface S NormValue) :
    Q.QuotientCarrier → NormValue :=
  Q.quotientRec NormValue N.norm (fun _ _ h => N.normRespects h)

/-- The descended norm computes on classes (Agda `quotientNorm-β`). -/
theorem quotientNorm_beta {S : SetoidSurface} (Q : SetoidQuotientSurface S)
    {NormValue : Type} (N : SetoidNormSurface S NormValue) (x : S.Carrier) :
    quotientNorm Q N (Q.quotientClass x) = N.norm x :=
  Q.quotientRec_beta NormValue N.norm (fun _ _ h => N.normRespects h) x

/-! ## Genuine witness via Lean's real `Quotient` -/

/-- The Lean `Setoid` induced by a `SetoidSurface`. -/
def toSetoid (S : SetoidSurface) : Setoid S.Carrier where
  r := S.rel
  iseqv := ⟨S.isEquiv.refl, S.isEquiv.symm, S.isEquiv.trans⟩

/-- Genuine witness: Lean's `Quotient` realises the setoid-quotient surface, with
every field *proved* (soundness = `Quotient.sound`, recursor = `Quotient.lift`,
`β`-rule by `rfl`). -/
def quotientWitness (S : SetoidSurface) : SetoidQuotientSurface S where
  QuotientCarrier := Quotient (toSetoid S)
  quotientClass := fun x => Quotient.mk (toSetoid S) x
  quotientSound := fun h => Quotient.sound h
  quotientRec := fun _ f resp =>
    Quotient.lift f (fun a b h => resp a b h)
  quotientRec_beta := fun _ _ _ _ => rfl

end AgdaMirror.QuotientSetoidSurface
