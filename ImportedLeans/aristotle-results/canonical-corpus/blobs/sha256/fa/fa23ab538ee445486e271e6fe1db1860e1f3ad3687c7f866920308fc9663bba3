import Cuisine.HyperfabricGuard
import Synthesis.ToneCore

/-!
# A referent for `spiral`

The hyperfabric guard imported by the cuisine record enumerates eight semantic
surfaces, one of which is named `spiral`.  `Cuisine.SurfaceInterpretation`
matches seven of them with implementation types; `spiral` was recorded as having
no referent anywhere in the corpus.

That was wrong, and this file corrects it.  `Agda/DASHI/Cognition/
KlueverFormConstantProjection.agda` defines a four-element type `KlueverForm`
whose constructors are `latticeGrating`, `tunnelFunnel`, **`spiral`** and
`radialCobweb`, together with a dependent family `KlueverGeometryHint` assigning
each form exactly one coarse geometry hint.  That is a genuine implementation
carrier, and `spiral` is one of its four values.

Proved here:

* `card_klueverForm` — the carrier has four elements;
* `hint_unique`, `hintSigmaEquiv` — the geometry-hint family is a singleton over
  each form, so hints and forms are the same four-element object.  The Agda
  comment calls the hints "many to one and incomplete"; on this data they are in
  fact one to one and total, which is the stronger (and checkable) statement;
* `spiralHint_unique` — `spiral`'s hint, `angularPhaseHint`, is its only one.

And the honest limitation:

* `no_injective_klueverForm_to_trit` — four elements do not inject into three,
  so the form-constant carrier does **not** join the ternary spine.  `spiral`
  now has a referent; it is not a ternary one.  Its actual geometry — the
  logarithmic spirals of the retino-cortical log-polar map — lives in the
  separate real-analytic development under
  `Lean/DASHI/Klüver’s Form Constants_aristotle/`, which is a continuous
  geometry and not a finite carrier at all.

Boundary: `KlueverForm` is a four-element set.  Nothing here asserts anything
about perception, cortex, or phenomenology; the Agda module's own guard fields
forbid exactly such promotions.
-/

namespace Cuisine.SpiralCarrier

open AgdaMirror.Base369 (TriTruth)

/-- Mirror of `KlueverForm`: the four classic form-constant families. -/
inductive KlueverForm
  | latticeGrating | tunnelFunnel | spiral | radialCobweb
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `VisualCarrierVariable`. -/
inductive VisualCarrierVariable
  | retinalExcitation | corticalExcitation | lateralInhibition | orientationMapBias
  | retinotopicCoordinate | logPolarCoordinate | endogenousNoise
  | externalInputAttenuation
  deriving DecidableEq, Fintype, Repr

open KlueverForm

/-- Mirror of the dependent family `KlueverGeometryHint`. -/
inductive KlueverGeometryHint : KlueverForm → Type
  | gridOrTilingHint : KlueverGeometryHint latticeGrating
  | funnelDepthHint : KlueverGeometryHint tunnelFunnel
  | angularPhaseHint : KlueverGeometryHint spiral
  | radialSpokeHint : KlueverGeometryHint radialCobweb

theorem card_klueverForm : Fintype.card KlueverForm = 4 := rfl

theorem card_visualCarrierVariable : Fintype.card VisualCarrierVariable = 8 := rfl

/-- **Each form has exactly one hint.** -/
theorem hint_unique {f : KlueverForm} (h h' : KlueverGeometryHint f) : h = h' := by
  cases f <;> cases h <;> cases h' <;> rfl

/-- Every form has a hint. -/
def hintOf : (f : KlueverForm) → KlueverGeometryHint f
  | latticeGrating => .gridOrTilingHint
  | tunnelFunnel => .funnelDepthHint
  | spiral => .angularPhaseHint
  | radialCobweb => .radialSpokeHint

/-- **Hints and forms are the same four-element object.**  The total space of
the hint family projects isomorphically onto the forms. -/
def hintSigmaEquiv : (Σ f : KlueverForm, KlueverGeometryHint f) ≃ KlueverForm where
  toFun := Sigma.fst
  invFun f := ⟨f, hintOf f⟩
  left_inv := by rintro ⟨f, h⟩; cases f <;> cases h <;> rfl
  right_inv _ := rfl

/-- `spiral`'s hint is the angular-phase hint, and it is the only one. -/
theorem spiralHint_unique (h : KlueverGeometryHint spiral) :
    h = KlueverGeometryHint.angularPhaseHint := hint_unique _ _

/-- **Honest limitation.**  The form-constant carrier has four elements, so it
does not inject into the ternary tone carrier: giving `spiral` a referent does
not attach it to the `369` spine. -/
theorem no_injective_klueverForm_to_trit :
    ¬ ∃ f : KlueverForm → TriTruth, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle : Fintype.card KlueverForm ≤ Fintype.card TriTruth :=
    Fintype.card_le_of_injective f hf
  rw [card_klueverForm] at hle
  exact absurd hle (by decide)

end Cuisine.SpiralCarrier
