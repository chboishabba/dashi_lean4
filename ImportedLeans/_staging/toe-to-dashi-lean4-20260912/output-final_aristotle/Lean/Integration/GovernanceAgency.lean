import Integration.ObserverPlurality

/-!
# The governance lane's agency surface: declared emptiness versus proved independence

`Agda/DASHI/Governance/AliceBrownInstitutionalAgencyChoiceBridgeExact.agda`
carries two devices.

The first is a *declared-empty* promotion type:

```agda
data FormalOptionPromotesAgency : Set where

formalOptionDoesNotPromoteAgency : FormalOptionPromotesAgency → ⊥
formalOptionDoesNotPromoteAgency ()
```

The second is `InstitutionalAgencySurface`, a record of five free `Bool` fields,
and `AliceInstitutionalChoiceBoundary`, a record of six free `Bool` fields whose
canonical inhabitant fixes particular values.

This file separates what those devices prove from what they are read as
proving.

## Declared emptiness proves nothing about the surface

* `promotionRoute_isEmpty` — the promotion type is empty.  True, and immediate:
  it was declared with no constructors.
* `emptyPromotion_proves_everything` — **and that is exactly why it carries no
  information**: an inhabitant of an empty type proves *any* proposition, so the
  eliminator `PromotionRoute → ⊥` is a fact about the declaration and not about
  formal options, agency, or their relation.  Filing it as "formal availability
  does not imply agency" would be inferring a theorem from a name.

## What can be proved instead

* `agency_not_determined_by_formalOption` — **the honest statement**: on the
  corpus's own record, `formalOptionPresented` does not determine
  `effectivelyAccessible`; two surfaces agree on the first and differ on the
  second.  This is a genuine underdetermination, in the style of
  `Integration.ObserverPlurality.not_refines_of_collapse`.
* `contest_not_determined_by_accessible`, and the general
  `surface_fields_independent`: **no field of the record determines any other**,
  because the record is exactly `Bool⁵`.
* `surfaceEquivBool5`, `card_surface` — the record has 32 inhabitants: it
  imposes no constraint whatever, which is the precise sense in which it is an
  open socket.
* `boundary_record_unconstrained` — the same for the six-field boundary record:
  its canonical inhabitant's values are a *choice*, not a theorem, since all 64
  assignments are inhabited.

## Claim boundary

Every carrier here is `Bool`.  Nothing in this file is a claim about
institutions, access, agency, education, disability, or any cited source; the
field names are labels reproduced from the Agda record so that the socket can be
identified.
-/

namespace Integration.GovernanceAgency

open Integration.ObserverPlurality (not_refines_of_collapse)

/-! ## The declared-empty promotion type -/

/-- Mirror of `data FormalOptionPromotesAgency : Set where` — declared with no
constructors. -/
inductive PromotionRoute : Type

theorem promotionRoute_isEmpty : IsEmpty PromotionRoute := ⟨fun r => nomatch r⟩

/-- **An empty promotion type licenses every conclusion.**  So the Agda
eliminator `FormalOptionPromotesAgency → ⊥` records a decision not to supply a
promotion route; it is not evidence about what it is named after. -/
theorem emptyPromotion_proves_everything (Q : Prop) (r : PromotionRoute) : Q := nomatch r

/-! ## The agency surface -/

/-- Mirror of `InstitutionalAgencySurface`: five free `Bool` fields. -/
structure InstitutionalAgencySurface where
  /-- Whether a formal option is presented. -/
  formalOptionPresented : Bool
  /-- Whether it is effectively accessible. -/
  effectivelyAccessible : Bool
  /-- Whether the subject can contest. -/
  subjectCanContest : Bool
  /-- Whether the subject can refuse. -/
  subjectCanRefuse : Bool
  /-- Whether evidence is returned for review. -/
  evidenceReturnedForReview : Bool
  deriving DecidableEq, Fintype

/-- The record is exactly `Bool⁵`. -/
def surfaceEquivBool5 :
    InstitutionalAgencySurface ≃ (Bool × Bool × Bool × Bool × Bool) where
  toFun s := ⟨s.formalOptionPresented, s.effectivelyAccessible, s.subjectCanContest,
              s.subjectCanRefuse, s.evidenceReturnedForReview⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_surface : Fintype.card InstitutionalAgencySurface = 32 := by decide

/-- **Formal availability does not determine effective accessibility** on the
corpus's own record. -/
theorem agency_not_determined_by_formalOption :
    ¬ Integration.LeastSufficient.Refines
        (fun s : InstitutionalAgencySurface => s.formalOptionPresented)
        (fun s : InstitutionalAgencySurface => s.effectivelyAccessible) :=
  not_refines_of_collapse
    (x := ⟨true, true, true, true, true⟩) (y := ⟨true, false, true, true, true⟩)
    rfl Bool.noConfusion

/-- Nor does effective accessibility determine the ability to contest. -/
theorem contest_not_determined_by_accessible :
    ¬ Integration.LeastSufficient.Refines
        (fun s : InstitutionalAgencySurface => s.effectivelyAccessible)
        (fun s : InstitutionalAgencySurface => s.subjectCanContest) :=
  not_refines_of_collapse
    (x := ⟨true, true, true, true, true⟩) (y := ⟨true, true, false, true, true⟩)
    rfl Bool.noConfusion

/-- **No field determines any other.**  Given two field projections that differ
somewhere, one does not refine the other: the general reason both statements
above hold, and the precise content of "these surfaces are independent". -/
theorem surface_fields_independent
    (f g : InstitutionalAgencySurface → Bool)
    {x y : InstitutionalAgencySurface} (hf : f x = f y) (hg : g x ≠ g y) :
    ¬ Integration.LeastSufficient.Refines f g :=
  not_refines_of_collapse hf hg

/-! ## The boundary record -/

/-- Mirror of `AliceInstitutionalChoiceBoundary`: six free `Bool` fields. -/
structure ChoiceBoundary where
  /-- "Formal availability = agency". -/
  formalAvailabilityEqualsAgency : Bool
  /-- "Student voice may be replaced by parent voice". -/
  studentVoiceCanBeReplacedByParentVoice : Bool
  /-- "Parent expertise may be situated evidence". -/
  parentExpertiseMayBeSituatedEvidence : Bool
  /-- "Institutional record = whole system". -/
  institutionalRecordEqualsWholeSystem : Bool
  /-- "Participation and accessibility are distinct". -/
  participationAndAccessibilityAreDistinct : Bool
  /-- "Source papers establish religious coercion". -/
  sourcePapersEstablishReligiousCoercion : Bool
  deriving DecidableEq, Fintype

/-- The Agda module's canonical inhabitant. -/
def canonicalChoiceBoundary : ChoiceBoundary :=
  ⟨false, false, true, false, true, false⟩

/-- **The canonical values are a choice, not a theorem**: all 64 assignments are
inhabited, so nothing in the record excludes the opposite one. -/
theorem boundary_record_unconstrained :
    Fintype.card ChoiceBoundary = 64 ∧
    ∃ b : ChoiceBoundary,
      b.formalAvailabilityEqualsAgency ≠
        canonicalChoiceBoundary.formalAvailabilityEqualsAgency :=
  ⟨by decide, ⟨⟨true, false, true, false, true, false⟩, Bool.noConfusion⟩⟩

end Integration.GovernanceAgency
