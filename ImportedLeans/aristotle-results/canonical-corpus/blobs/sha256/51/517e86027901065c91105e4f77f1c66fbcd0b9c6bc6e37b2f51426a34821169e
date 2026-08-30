import Cuisine.UmamiTransport

/-!
# The `3 · 5 = 15` shape of the base, the `3 ^ 9 = 19683` sheet, and the
moonshine numerals

The corpus repeatedly writes the Monster/moonshine numerals against the
ternary depth-nine count `3 ^ 9 = 19683`:

* `Agda/DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda` states
  `196884 = 10 · 3^9 + 54` and `196883 = 10 · 3^9 + 53`;
* `Agda/DASHI/Biology/MonsterStructuredBulkCarrierExact.agda` states
  `196883 = 3^11 + 3^9 + 53`;
* `Agda/DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda` carries the bulk
  count `196830 = 10 · 3^9`.

This file makes the corresponding statements about the *hyperfabric* of
`Synthesis.Hyperfabric` — sections of the ternary fibre over the fifteen
supersingular primes — and puts the cuisine transport of
`Cuisine.UmamiTransport` on the same line.

Content:

* `card_supported` — for any set `s` of base points, the sections vanishing
  outside `s` number `3 ^ |s|`.  At `|s| = 9` this is `19683`
  (`card_supported_nine`), and `3 ^ 15 = 3 ^ 9 · 3 ^ 6` splits the full fabric
  into a depth-nine sheet and its complement (`card_fabric_split`).
* `sspToneTaste` — the base has the shape `3 · 5`: a chosen bijection
  `SSP ≃ TriTruth × TasteDimension` onto tone-indexed cuisine taste dimensions.
  *This is a choice*, as it is for any two fifteen-element sets; the content is
  the factorisation shape, and it is used only to index sheets by tastes.
* `card_taste_sheet` — for any three of the five taste dimensions, the sections
  supported over those tastes number exactly `19683`.
* `moonshine_nine_sheet_bridge` — the commuting statement: with `N` the number
  of sections of a depth-nine sheet, the supplied numerals satisfy
  `repDim = 10 · N + 53`, `jCoefficient = 10 · N + 54`, `repDim = 3^11 + N + 53`,
  and `repDim` is the successor of the cuisine intensity of the Monster
  trivector mask.

Boundary: every statement here is a finite count or an arithmetic identity
between supplied numerals.  Nothing about the Monster group, its representation
theory, or modular forms is used or claimed.
-/

namespace Cuisine.NineSheet

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (TasteDimension)
open Cuisine.UmamiTransport

/-! ## Sheets: sections supported on part of the base -/

/-- The sections of the ternary fibre that are neutral outside `s`. -/
def Supported (s : Finset SSP) : Type := {F : Fabric // ∀ p, p ∉ s → F p = Trit.neg}

instance (s : Finset SSP) : Fintype (Supported s) := by
  classical
  unfold Supported
  infer_instance

/-- A section supported on `s` is exactly a ternary labelling of `s`. -/
def supportedEquiv (s : Finset SSP) : Supported s ≃ (s → Trit) where
  toFun F := fun p => F.val p.val
  invFun g := ⟨fun p => if h : p ∈ s then g ⟨p, h⟩ else Trit.neg, by
    intro p hp; simp [hp]⟩
  left_inv F := by
    apply Subtype.ext
    funext p
    by_cases h : p ∈ s
    · simp [h]
    · simp [h, F.property p h]
  right_inv g := by
    funext p
    simp

/-- **Sheet count.**  The sections supported on `s` number `3 ^ |s|`. -/
theorem card_supported (s : Finset SSP) : Fintype.card (Supported s) = 3 ^ s.card := by
  rw [Fintype.card_congr (supportedEquiv s), Fintype.card_fun, Fintype.card_coe]
  rfl

/-- **The depth-nine sheet has `19683` sections.** -/
theorem card_supported_nine (s : Finset SSP) (hs : s.card = 9) :
    Fintype.card (Supported s) = 19683 := by
  rw [card_supported, hs]
  norm_num

/-- The full fabric splits as a depth-nine sheet times a depth-six complement. -/
theorem card_fabric_split : Fintype.card Fabric = 3 ^ 9 * 3 ^ 6 := by
  rw [card_fabric]
  norm_num

theorem three_pow_nine : (3 : ℕ) ^ 9 = 19683 := by norm_num

/-! ## The `3 · 5` shape of the base -/

/-- A chosen bijection exhibiting the fifteen-element Monster prime base in the
shape `3 · 5`: three tones times the five cuisine taste dimensions.  As with any
two fifteen-element sets, the bijection is a choice; what is used below is only
the product shape. -/
def sspToneTaste : SSP ≃ TriTruth × TasteDimension where
  toFun
    | .p2 => (.low, .sweet) | .p3 => (.low, .salty) | .p5 => (.low, .sour)
    | .p7 => (.low, .bitter) | .p11 => (.low, .umami)
    | .p13 => (.mid, .sweet) | .p17 => (.mid, .salty) | .p19 => (.mid, .sour)
    | .p23 => (.mid, .bitter) | .p29 => (.mid, .umami)
    | .p31 => (.high, .sweet) | .p41 => (.high, .salty) | .p47 => (.high, .sour)
    | .p59 => (.high, .bitter) | .p71 => (.high, .umami)
  invFun
    | (.low, .sweet) => .p2 | (.low, .salty) => .p3 | (.low, .sour) => .p5
    | (.low, .bitter) => .p7 | (.low, .umami) => .p11
    | (.mid, .sweet) => .p13 | (.mid, .salty) => .p17 | (.mid, .sour) => .p19
    | (.mid, .bitter) => .p23 | (.mid, .umami) => .p29
    | (.high, .sweet) => .p31 | (.high, .salty) => .p41 | (.high, .sour) => .p47
    | (.high, .bitter) => .p59 | (.high, .umami) => .p71
  left_inv := by decide
  right_inv := by decide

theorem card_tone_taste : Fintype.card (TriTruth × TasteDimension) = 15 := by decide

/-- The base points lying over a set of taste dimensions. -/
def tasteBlock (T : Finset TasteDimension) : Finset SSP :=
  Finset.univ.filter (fun p => (sspToneTaste p).2 ∈ T)

/-- Each taste dimension carries exactly three base points, so a set of `k`
tastes carries `3k` of them; in particular three tastes carry nine. -/
theorem card_tasteBlock_three (T : Finset TasteDimension) (hT : T.card = 3) :
    (tasteBlock T).card = 9 := by
  revert hT
  revert T
  decide

/-- **A three-taste sheet is a depth-nine sheet**: it has `3 ^ 9 = 19683`
sections. -/
theorem card_taste_sheet (T : Finset TasteDimension) (hT : T.card = 3) :
    Fintype.card (Supported (tasteBlock T)) = 19683 :=
  card_supported_nine _ (card_tasteBlock_three T hT)

/-! ## The moonshine numerals against the sheet count -/

theorem repDim_eq_ten_mul_nine_sheet :
    AgdaMirror.Moonshine.repDim = 10 * 3 ^ 9 + 53 := by decide

theorem jCoefficient_eq_ten_mul_nine_sheet :
    AgdaMirror.Moonshine.jCoefficient = 10 * 3 ^ 9 + 54 := by decide

/-- The graded form recorded in `MonsterStructuredBulkCarrierExact`:
`196883 = 3^11 + 3^9 + 53`. -/
theorem repDim_eq_graded :
    AgdaMirror.Moonshine.repDim = 3 ^ 11 + 3 ^ 9 + 53 := by decide

/-- The bulk numeral `196830 = 10 · 3^9` of the pointed-bulk modules. -/
theorem bulk_eq_ten_mul_nine_sheet : 10 * 3 ^ 9 = 196830 := by norm_num

/-- **The commuting statement.**  Let `N` be the number of sections of a
depth-nine sheet of the hyperfabric over the Monster prime base.  Then the
supplied moonshine numerals are the stated affine functions of `N`, the graded
form holds, and the same `repDim` is the successor of the cuisine intensity that
`Cuisine.UmamiTransport` assigns to the Monster trivector mask.  Every clause is
an identity between finite counts; none of them is a statement about the Monster
group or about modular forms. -/
theorem moonshine_nine_sheet_bridge (s : Finset SSP) (hs : s.card = 9) :
    Fintype.card (Supported s) = 19683 ∧
      AgdaMirror.Moonshine.repDim = 10 * Fintype.card (Supported s) + 53 ∧
      AgdaMirror.Moonshine.jCoefficient = 10 * Fintype.card (Supported s) + 54 ∧
      AgdaMirror.Moonshine.repDim = 3 ^ 11 + Fintype.card (Supported s) + 53 ∧
      maskIntensity trivectorMask + 1 = AgdaMirror.Moonshine.repDim := by
  have hcard := card_supported_nine s hs
  refine ⟨hcard, ?_, ?_, ?_, repDim_eq_maskIntensity_succ⟩
  · rw [hcard]; decide
  · rw [hcard]; decide
  · rw [hcard]; decide

/-! ## The `3 · 5` grid: the two readings of a section commute -/

/-- Read a hyperfabric section on the `3 · 5` grid as a tone-indexed family of
taste rows. -/
def gridRows : Fabric ≃ (TriTruth → TasteDimension → Trit) :=
  (Equiv.arrowCongr sspToneTaste (Equiv.refl Trit)).trans (Equiv.curry _ _ _)

/-- Read the same section as a taste-indexed family of tone columns. -/
def gridCols : Fabric ≃ (TasteDimension → TriTruth → Trit) :=
  gridRows.trans (Equiv.piComm _)

/-- **The grid square commutes.**  Rows-then-columns and columns-then-rows give
the same entry, so the `3 · 5` factorisation of the base is a genuine
bi-indexing of the hyperfabric and not two unrelated readings. -/
theorem grid_flip (F : Fabric) (t : TriTruth) (d : TasteDimension) :
    gridCols F d t = gridRows F t d := rfl

@[simp] theorem gridRows_apply (F : Fabric) (t : TriTruth) (d : TasteDimension) :
    gridRows F t d = F (sspToneTaste.symm (t, d)) := rfl

/-- Both readings recover the section itself. -/
theorem gridRows_symm_apply (F : Fabric) : gridRows.symm (gridRows F) = F :=
  gridRows.symm_apply_apply F

/-- **The count factorises both ways.**  `3 ^ 15 = (3 ^ 5) ^ 3 = (3 ^ 3) ^ 5`:
three taste-rows of five, or five tone-columns of three, and the depth-nine
sheet `3 ^ 9 = 27 ^ 3` is exactly three of the five columns. -/
theorem card_fabric_grid :
    Fintype.card Fabric = (3 ^ 5) ^ 3 ∧
      Fintype.card Fabric = (3 ^ 3) ^ 5 ∧
      (3 : ℕ) ^ 9 = 27 ^ 3 ∧
      Fintype.card Fabric = 3 ^ 9 * 3 ^ 6 := by
  refine ⟨?_, ?_, by norm_num, card_fabric_split⟩ <;> · rw [card_fabric]; norm_num

end Cuisine.NineSheet
