import Mathlib

/-!
# Cuisine layer 1: the surface ledger and what it does (and does not) prove

Lean mirror of `DASHI.Culture.Cuisine.CuisineFormalismBundle` (the
`CuisineSurface` / `SurfaceDistinction` / `CuisineNonCollapse` block) and of the
`SurfaceKind` enumeration of `DASHI.Culture.Cuisine.CuisineDataFlowCore`.

The Agda `SurfaceDistinction` is an inductive family with six constructors and
*no* proof that the related surfaces are actually different: syntactically one
could add a constructor `SurfaceDistinction s s` and the record
`CuisineNonCollapse` would still be inhabited while asserting nothing.

New content proved here:

* `SurfaceDistinction.ne` — every inhabitant of the supplied family does relate
  two genuinely distinct surfaces, so the ledger is sound;
* `SurfaceDistinction.irrefl` — no surface is distinguished from itself;
* `SurfaceDistinction.asymm_example` — the family is *directed*: it is a ledger
  of asserted separations, not a symmetric apartness relation;
* `surfaceDistinction_incomplete` — the ledger is genuinely partial: distinct
  surfaces exist that it does not separate.  The last point is the honest limit
  of what the Agda bundle establishes.
-/

namespace Cuisine.Surfaces

/-- The ten cuisine surfaces of the Agda bundle. -/
inductive CuisineSurface
  | sensorySurface | safetySurface | popularitySurface | canonSurface
  | nutritionSurface | identitySurface | provenanceSurface | flavourSurface
  | historicalSurface | universalReadingSurface
  deriving DecidableEq, Fintype, Repr

open CuisineSurface

/-- The six asserted separations of the Agda `SurfaceDistinction` family,
transcribed constructor for constructor. -/
inductive SurfaceDistinction : CuisineSurface → CuisineSurface → Prop
  | sensorySafetyDistinct : SurfaceDistinction sensorySurface safetySurface
  | popularityCanonDistinct : SurfaceDistinction popularitySurface canonSurface
  | nutritionIdentityDistinct : SurfaceDistinction nutritionSurface identitySurface
  | provenanceFlavourDistinct : SurfaceDistinction provenanceSurface flavourSurface
  | historicalReceiptDistinct : SurfaceDistinction historicalSurface canonSurface
  | observerUniversalDistinct : SurfaceDistinction sensorySurface universalReadingSurface

/-- Boolean transcription of the six recorded separations, used to make the
ledger decidable. -/
def recorded : CuisineSurface → CuisineSurface → Bool
  | sensorySurface, safetySurface => true
  | popularitySurface, canonSurface => true
  | nutritionSurface, identitySurface => true
  | provenanceSurface, flavourSurface => true
  | historicalSurface, canonSurface => true
  | sensorySurface, universalReadingSurface => true
  | _, _ => false

theorem surfaceDistinction_iff (a b : CuisineSurface) :
    SurfaceDistinction a b ↔ recorded a b = true := by
  constructor
  · rintro h; cases h <;> rfl
  · intro h
    cases a <;> cases b <;> first | exact absurd h (by decide) | constructor

instance (a b : CuisineSurface) : Decidable (SurfaceDistinction a b) :=
  decidable_of_iff _ (surfaceDistinction_iff a b).symm

namespace SurfaceDistinction

/-- **Soundness of the ledger.**  Every asserted separation really is a
separation of two different surfaces. -/
theorem ne {a b : CuisineSurface} (h : SurfaceDistinction a b) : a ≠ b := by
  cases h <;> decide

/-- No surface is separated from itself. -/
theorem irrefl (a : CuisineSurface) : ¬ SurfaceDistinction a a := fun h => h.ne rfl

/-- The ledger is directed, not symmetric: the reverse of a recorded separation
is not itself recorded. -/
theorem asymm_example : ¬ SurfaceDistinction safetySurface sensorySurface := by
  rintro ⟨⟩

end SurfaceDistinction

/-- The Agda record `CuisineNonCollapse`: a bundle of the six separations. -/
structure CuisineNonCollapse where
  sensoryIsNotSafety : SurfaceDistinction sensorySurface safetySurface
  popularityIsNotCanon : SurfaceDistinction popularitySurface canonSurface
  nutritionIsNotIdentity : SurfaceDistinction nutritionSurface identitySurface
  provenanceIsNotFlavour : SurfaceDistinction provenanceSurface flavourSurface
  historicalClaimNeedsReceipt : SurfaceDistinction historicalSurface canonSurface
  observerReadingIsNotUniversal : SurfaceDistinction sensorySurface universalReadingSurface

/-- The canonical inhabitant, mirroring `canonicalCuisineNonCollapse`. -/
def canonicalCuisineNonCollapse : CuisineNonCollapse where
  sensoryIsNotSafety := .sensorySafetyDistinct
  popularityIsNotCanon := .popularityCanonDistinct
  nutritionIsNotIdentity := .nutritionIdentityDistinct
  provenanceIsNotFlavour := .provenanceFlavourDistinct
  historicalClaimNeedsReceipt := .historicalReceiptDistinct
  observerReadingIsNotUniversal := .observerUniversalDistinct

/-- **Honest limit of the bundle.**  `CuisineNonCollapse` records six
separations, but the surface carrier has `10 * 9 / 2 = 45` unordered pairs of
distinct surfaces; the ledger does not separate, for instance, nutrition from
flavour.  So the bundle is a list of audited claims, not a proof that all ten
surfaces are pairwise independent. -/
theorem surfaceDistinction_incomplete :
    nutritionSurface ≠ flavourSurface ∧
      ¬ SurfaceDistinction nutritionSurface flavourSurface ∧
      ¬ SurfaceDistinction flavourSurface nutritionSurface :=
  ⟨by decide, by rintro ⟨⟩, by rintro ⟨⟩⟩

/-- The number of ordered pairs the ledger actually records. -/
theorem card_recorded_pairs :
    (Finset.univ.filter
      (fun p : CuisineSurface × CuisineSurface => SurfaceDistinction p.1 p.2)).card = 6 := by
  decide

/-! ## The data-flow surface kinds

`DASHI.Culture.Cuisine.CuisineDataFlowCore` carries a *second*, eleven-element
surface enumeration `SurfaceKind`.  It overlaps the bundle's `CuisineSurface` in
name only for four constructors, and the two carriers are not in bijection. -/

inductive SurfaceKind
  | identitySurface | techniqueSurface | recipeRouteSurface | lineageSurface
  | nutritionSurface | provenanceSurface | qualitativeSurface | movementSurface
  | safetySurface | authoritySurface | variantSurface
  deriving DecidableEq, Fintype, Repr

/-- The two surface carriers of the cuisine lane have different cardinalities,
so there is no bijection between them; any identification of "surfaces" across
the two modules would have to be a partial map chosen by hand. -/
theorem no_surface_bijection : ¬ Nonempty (CuisineSurface ≃ SurfaceKind) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  have h1 : Fintype.card CuisineSurface = 10 := by decide
  have h2 : Fintype.card SurfaceKind = 11 := by decide
  rw [h1, h2] at h
  exact absurd h (by decide)

end Cuisine.Surfaces
