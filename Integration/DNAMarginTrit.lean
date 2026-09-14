import Integration.TernaryHub

/-!
# The DNA-chemistry margin is the hub trit — and is *not* a complete coordinate

`Agda/DASHI/Biology/DNAChemistryTritQuotientBridge.agda` introduces a three-way
chemistry margin

```agda
data ChemistryMargin : Set where
  negativeMargin neutralMargin positiveMargin : ChemistryMargin
```

with maps to and from `DASHI.Foundations.SSPTritCarrier.SSPTrit` and both
round-trips proved by exhaustive `refl`.  It then states, in prose and in `Bool`
fields, that the ternary quotient must *not* be read as the DNA alphabet or as a
complete coordinate: `carrierAlphabetIsCAGT`, `ternaryRequiredAtEveryStep =
false`, and a four-element `AdmissibleFibreArity`.

This file makes both halves checkable.

## The positive half

* `marginEquivSSP` — the two Agda round-trips are exactly an `Equiv`, so the
  margin carrier is the SSP trit carrier.
* `marginPolarity`, `marginHub` — the SSP polarity transports back to the margin
  (`negativeMargin ↔ positiveMargin`, `neutralMargin` fixed), giving an
  `Integration.Levels.Transport` to `ZMod 3` with negation.  The margin is
  therefore the *same balanced digit* as the six carriers of
  `Integration.TernaryHub` and the ontology carrier of
  `Integration.Ontology`.
* `marginPolarity_unique` — and the transported involution is the **only** one
  that could be transported: any self-map of `ChemistryMargin` acting as
  negation in the balanced coordinate is `marginPolarity`.  So the identification
  fixes the structure rather than choosing it.

  The honesty note that goes with this row: the Agda module declares *no*
  involution on `ChemistryMargin`.  The polarity is induced by the bijection, so
  the row is an exact instance of the hub **for the induced structure**, not a
  claim that the biology lane had that structure already.

## The negative half

* `no_injection_arity_to_margin` — **the ternary quotient cannot index the
  fibre**: `AdmissibleFibreArity` has four elements and the margin three, so no
  injection exists.  This is the checkable content of
  `ternaryRequiredAtEveryStep = false`; the four-way case is genuinely lost.
* `sheetTrit_redundant` — the record's `trit` field is determined by its
  `margin` field, so `ChemistrySheetTrit` carries no more information than
  `rank × channel × margin × Bool × Bool`.  A "chemistry coordinate" built from
  it is a coordinate on the margin, not on base identity.

## Claim boundary

`ChemistryMargin` is a three-element label type and `AdmissibleFibreArity` a
four-element one.  Nothing here is a claim about DNA, nucleotides, base
identity, chemistry, or energetics; in particular nothing here relates the
carrier to `CAGT`, which is the point of the negative half.
-/

namespace Integration.DNAMarginTrit

open Integration.Levels
open Integration.TernaryHub

/-! ## The margin carrier -/

/-- Mirror of `DASHI.Biology.DNAChemistryTritQuotientBridge.ChemistryMargin`. -/
inductive ChemistryMargin
  | negativeMargin | neutralMargin | positiveMargin
  deriving DecidableEq, Repr, Fintype

open ChemistryMargin

/-- Mirror of `marginToTrit`. -/
def marginToTrit : ChemistryMargin → SSPTrit
  | negativeMargin => .negOne
  | neutralMargin => .zero
  | positiveMargin => .posOne

/-- Mirror of `tritToMargin`. -/
def tritToMargin : SSPTrit → ChemistryMargin
  | .negOne => negativeMargin
  | .zero => neutralMargin
  | .posOne => positiveMargin

theorem margin_roundtrip (m : ChemistryMargin) : tritToMargin (marginToTrit m) = m := by
  decide +kernel +revert

theorem trit_roundtrip (t : SSPTrit) : marginToTrit (tritToMargin t) = t := by
  decide +kernel +revert

/-- The two Agda round-trips, as an equivalence. -/
def marginEquivSSP : ChemistryMargin ≃ SSPTrit where
  toFun := marginToTrit
  invFun := tritToMargin
  left_inv := margin_roundtrip
  right_inv := trit_roundtrip

/-! ## Joining the hub -/

/-- The polarity transported from `SSPTrit`.  The Agda module declares no
involution on `ChemistryMargin`; this is the induced one. -/
def marginPolarity : ChemistryMargin → ChemistryMargin
  | negativeMargin => positiveMargin
  | neutralMargin => neutralMargin
  | positiveMargin => negativeMargin

theorem marginPolarity_involutive (m : ChemistryMargin) :
    marginPolarity (marginPolarity m) = m := by decide +kernel +revert

/-- `marginToTrit` intertwines the induced polarity with the SSP polarity. -/
theorem marginToTrit_polarity (m : ChemistryMargin) :
    marginToTrit (marginPolarity m) = sspTritInv (marginToTrit m) := by
  decide +kernel +revert

/-- The balanced coordinate of a margin. -/
def balMargin (m : ChemistryMargin) : ZMod 3 := balSSP (marginToTrit m)

theorem balMargin_polarity (m : ChemistryMargin) :
    balMargin (marginPolarity m) = - balMargin m := by decide +kernel +revert

/-- **The margin joins the ternary hub.** -/
def marginHub : Transport ChemistryMargin (ZMod 3) marginPolarity zneg :=
  ⟨marginEquivSSP.trans balSSPEquiv, balMargin_polarity⟩

/-- The transported involution is unique: any self-map acting as negation in the
balanced coordinate is `marginPolarity`. -/
theorem marginPolarity_unique (op : ChemistryMargin → ChemistryMargin)
    (h : ∀ m, balMargin (op m) = - balMargin m) (m : ChemistryMargin) :
    op m = marginPolarity m := by
  have hinj : Function.Injective balMargin := by decide +kernel
  exact hinj (by rw [h m, balMargin_polarity])

/-! ## The ternary quotient is not a complete coordinate -/

/-- Mirror of `AdmissibleFibreArity`. -/
inductive AdmissibleFibreArity
  | forcedArity | twoWayArity | threeWayArity | fourWayArity
  deriving DecidableEq, Repr, Fintype

/-- **The ternary quotient cannot index the admissible fibre**: four arities do
not embed in three margins.  This is the checkable content of
`ternaryRequiredAtEveryStep = false`. -/
theorem no_injection_arity_to_margin :
    ¬ ∃ f : AdmissibleFibreArity → ChemistryMargin, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact absurd (Fintype.card_le_of_injective f hf) (by decide +kernel)

/-! ## The sheet record is redundant in its trit field -/

/-- The Bool-and-margin part of `ChemistrySheetTrit`, over abstract carriers for
`rank` and `channel`. -/
structure ChemistrySheetTrit (Rank Channel : Type) where
  /-- The four-adic lift rank. -/
  rank : Rank
  /-- The sheet channel. -/
  channel : Channel
  /-- The chemistry margin. -/
  margin : ChemistryMargin
  /-- The trit coordinate. -/
  trit : SSPTrit
  /-- ... which is *derived* from the margin. -/
  tritMatchesMargin : trit = marginToTrit margin
  /-- Whether base identity is preserved (unconstrained). -/
  preservesBaseIdentity : Bool
  /-- Whether this is a complete chemistry coordinate (unconstrained). -/
  isCompleteChemistryCoordinate : Bool

/-- **The trit field carries no information.**  A sheet trit is exactly a rank, a
channel, a margin and two free flags. -/
def sheetTrit_redundant (Rank Channel : Type) :
    ChemistrySheetTrit Rank Channel ≃ (Rank × Channel × ChemistryMargin × Bool × Bool) where
  toFun s := ⟨s.rank, s.channel, s.margin, s.preservesBaseIdentity,
              s.isCompleteChemistryCoordinate⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, marginToTrit p.2.2.1, rfl, p.2.2.2.1, p.2.2.2.2⟩
  left_inv := by rintro ⟨r, c, m, t, rfl, b₁, b₂⟩; rfl
  right_inv _ := rfl

/-- The two flag fields are free: two sheet trits can agree on rank, channel,
margin and trit and still disagree on `isCompleteChemistryCoordinate`. -/
theorem sheetFlags_underdetermined :
    ∃ s t : ChemistrySheetTrit Unit Unit,
      s.margin = t.margin ∧
        s.isCompleteChemistryCoordinate ≠ t.isCompleteChemistryCoordinate :=
  ⟨⟨(), (), neutralMargin, .zero, rfl, false, false⟩,
   ⟨(), (), neutralMargin, .zero, rfl, false, true⟩, rfl, Bool.noConfusion⟩

end Integration.DNAMarginTrit
