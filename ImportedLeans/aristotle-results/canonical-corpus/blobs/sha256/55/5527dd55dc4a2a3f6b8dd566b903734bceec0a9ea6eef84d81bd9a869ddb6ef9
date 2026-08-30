import Integration.TernaryHub

/-!
# What a "receipt" record actually pins down

The dominant idiom of the corpus is the *receipt*: a record with a field
`carrier : Set`, some distinguished elements of that carrier, classifier
functions into small enumerations, and a list of `≡`-equations pinning the
classifiers' values at the distinguished elements — usually together with a
canonical inhabitant built from the module's own definitions.
`DASHI/Foundations/SSPTritCarrier.agda` (58 direct importers) is the archetype
and is mirrored here.

The question this file answers is: *given only an inhabitant of the receipt,
what is determined?*

* `carrierEquivTrit` — the carrier is determined up to bijection: the two
  round-trip fields make it a three-element type, canonically identified with
  `Trit`.  So the receipt does carry real content, and any downstream module
  that only needs "a ternary carrier" is entitled to it.
* `values_pairwise_ne`, `values_exhaust` — the three distinguished elements are
  pairwise distinct and exhaust the carrier.  Distinctness comes from the
  *polarity classifier*, not from the carrier: it is the classifier equations
  that do the work.
* `alignment_unconstrained` — **but the receipt does not pin the alignment of
  the bridge**: for *every* one of the three digits `t` there is an inhabitant
  of the receipt whose `toTritCarrier` sends the value labelled "negative" to
  `t`.  A downstream module that reads the bridge as sign-preserving is using an
  assumption the receipt does not supply.
* `canonicalReceipt` — the Agda's own inhabitant, which of course *is* aligned;
  the point of `alignment_unconstrained` is that this is a property of that
  inhabitant, not of the interface.

The corresponding one-line repair is recorded as `AlignedReceipt`: add the
single field `toTritCarrier negativeValue ≡ neg`, and alignment becomes forced
(`aligned_forced`).

Boundary: `String` label fields and the `semanticPieces` list of the Agda record
are omitted here; they are equations between fixed constants and add no
constraint on the carrier, which is itself part of the finding.
-/

namespace Integration.ReceiptSocket

open Integration.TernaryHub
open AgdaMirror.DASHIAlgebra (Trit)

/-- Mirror of `SSPTritPolarity`. -/
inductive Polarity | negative | neutral | positive
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `SSPTritNeutrality`. -/
inductive Neutrality | nonNeutral | neutral
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the substantive part of `SSPTritCarrierReceipt`: the carrier, its
three distinguished values, the polarity and neutrality classifiers with their
equations, the boolean neutrality test, and the `Trit` bridge with both
round-trip laws. -/
structure Receipt : Type 1 where
  /-- The carrier the receipt is about. -/
  carrier : Type
  /-- The value labelled "−1". -/
  negativeValue : carrier
  /-- The value labelled "0". -/
  neutralValue : carrier
  /-- The value labelled "+1". -/
  positiveValue : carrier
  /-- The polarity classifier. -/
  polarity : carrier → Polarity
  polarityOfNegative : polarity negativeValue = .negative
  polarityOfNeutral : polarity neutralValue = .neutral
  polarityOfPositive : polarity positiveValue = .positive
  /-- The neutrality classifier. -/
  neutrality : carrier → Neutrality
  neutralityOfNegative : neutrality negativeValue = .nonNeutral
  neutralityOfNeutral : neutrality neutralValue = .neutral
  neutralityOfPositive : neutrality positiveValue = .nonNeutral
  /-- The boolean neutrality test. -/
  isNeutral : carrier → Bool
  isNeutralOfNegative : isNeutral negativeValue = false
  isNeutralOfNeutral : isNeutral neutralValue = true
  isNeutralOfPositive : isNeutral positiveValue = false
  /-- The bridge to the balanced-ternary digit. -/
  toTritCarrier : carrier → Trit
  /-- …and back. -/
  fromTritCarrier : Trit → carrier
  toTritFromTrit : ∀ t, toTritCarrier (fromTritCarrier t) = t
  fromTritToTrit : ∀ c, fromTritCarrier (toTritCarrier c) = c

namespace Receipt

variable (R : Receipt)

/-- **The carrier is determined up to bijection.**  The two round-trip fields
are exactly an equivalence with the balanced-ternary digit. -/
def carrierEquivTrit : R.carrier ≃ Trit where
  toFun := R.toTritCarrier
  invFun := R.fromTritCarrier
  left_inv := R.fromTritToTrit
  right_inv := R.toTritFromTrit

/-- The three distinguished values are pairwise distinct — separated by the
polarity classifier, not by the carrier. -/
theorem values_pairwise_ne :
    R.negativeValue ≠ R.neutralValue ∧ R.negativeValue ≠ R.positiveValue ∧
      R.neutralValue ≠ R.positiveValue := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := R.polarityOfNegative
    rw [h, R.polarityOfNeutral] at this
    exact absurd this (by decide)
  · have := R.polarityOfNegative
    rw [h, R.polarityOfPositive] at this
    exact absurd this (by decide)
  · have := R.polarityOfNeutral
    rw [h, R.polarityOfPositive] at this
    exact absurd this (by decide)

/-- The carrier is a three-element type. -/
theorem card_carrier : Nat.card R.carrier = 3 := by
  have : Nat.card R.carrier = Nat.card Trit := Nat.card_congr R.carrierEquivTrit
  rw [this]
  have : Nat.card Trit = Fintype.card Trit := Nat.card_eq_fintype_card
  rw [this]
  rfl

/-- …and the three distinguished values exhaust it. -/
theorem values_exhaust (c : R.carrier) :
    c = R.negativeValue ∨ c = R.neutralValue ∨ c = R.positiveValue := by
  obtain ⟨h1, h2, h3⟩ := R.values_pairwise_ne
  set e := R.carrierEquivTrit with he
  have e1 : e R.negativeValue ≠ e R.neutralValue := fun h => h1 (e.injective h)
  have e2 : e R.negativeValue ≠ e R.positiveValue := fun h => h2 (e.injective h)
  have e3 : e R.neutralValue ≠ e R.positiveValue := fun h => h3 (e.injective h)
  have key : ∀ a b d x : Trit, a ≠ b → a ≠ d → b ≠ d → x = a ∨ x = b ∨ x = d := by decide
  rcases key (e R.negativeValue) (e R.neutralValue) (e R.positiveValue) (e c) e1 e2 e3 with
    h | h | h
  exacts [Or.inl (e.injective h), Or.inr (Or.inl (e.injective h)),
    Or.inr (Or.inr (e.injective h))]

end Receipt

/-! ## The canonical inhabitant, and the alignment gap -/

/-- The classifier of the corpus's own carrier. -/
def tritPolarity : Trit → Polarity
  | .neg => .negative | .zer => .neutral | .pos => .positive

def tritNeutrality : Trit → Neutrality
  | .neg => .nonNeutral | .zer => .neutral | .pos => .nonNeutral

def tritIsNeutral : Trit → Bool
  | .neg => false | .zer => true | .pos => false

/-- The Agda's canonical inhabitant, transcribed. -/
def canonicalReceipt : Receipt where
  carrier := Trit
  negativeValue := .neg
  neutralValue := .zer
  positiveValue := .pos
  polarity := tritPolarity
  polarityOfNegative := rfl
  polarityOfNeutral := rfl
  polarityOfPositive := rfl
  neutrality := tritNeutrality
  neutralityOfNegative := rfl
  neutralityOfNeutral := rfl
  neutralityOfPositive := rfl
  isNeutral := tritIsNeutral
  isNeutralOfNegative := rfl
  isNeutralOfNeutral := rfl
  isNeutralOfPositive := rfl
  toTritCarrier := id
  fromTritCarrier := id
  toTritFromTrit _ := rfl
  fromTritToTrit _ := rfl

/-- A relabelled inhabitant: the same carrier and the same bridge, but the three
distinguished values permuted by `σ`, with the classifiers permuted to match.
Every field of the receipt is satisfied. -/
def relabelledReceipt (σ : Trit ≃ Trit) : Receipt where
  carrier := Trit
  negativeValue := σ .neg
  neutralValue := σ .zer
  positiveValue := σ .pos
  polarity := fun x => tritPolarity (σ.symm x)
  polarityOfNegative := by simp [tritPolarity]
  polarityOfNeutral := by simp [tritPolarity]
  polarityOfPositive := by simp [tritPolarity]
  neutrality := fun x => tritNeutrality (σ.symm x)
  neutralityOfNegative := by simp [tritNeutrality]
  neutralityOfNeutral := by simp [tritNeutrality]
  neutralityOfPositive := by simp [tritNeutrality]
  isNeutral := fun x => tritIsNeutral (σ.symm x)
  isNeutralOfNegative := by simp [tritIsNeutral]
  isNeutralOfNeutral := by simp [tritIsNeutral]
  isNeutralOfPositive := by simp [tritIsNeutral]
  toTritCarrier := id
  fromTritCarrier := id
  toTritFromTrit _ := rfl
  fromTritToTrit _ := rfl

/-- **The receipt does not pin the alignment of its own `Trit` bridge.**  For
each of the three digits there is an inhabitant whose "negative" value is sent
to it. -/
theorem alignment_unconstrained (t : Trit) :
    ∃ R : Receipt, ∃ h : R.carrier = Trit,
      (h ▸ R.negativeValue) = t := by
  classical
  refine ⟨relabelledReceipt (Equiv.swap .neg t), rfl, ?_⟩
  show (Equiv.swap (Trit.neg) t) Trit.neg = t
  simp

/-- The concrete failure: an inhabitant whose "negative" value is the positive
digit. -/
theorem misaligned_receipt_exists :
    (relabelledReceipt (Equiv.swap .neg .pos)).negativeValue = Trit.pos := by
  show (Equiv.swap (Trit.neg) (Trit.pos)) Trit.neg = Trit.pos
  simp

/-! ## The one-field repair -/

/-- The receipt with the missing alignment field added. -/
structure AlignedReceipt extends Receipt where
  /-- The bridge sends the value labelled "negative" to the negative digit. -/
  negativeAligned : toTritCarrier negativeValue = Trit.neg

/-- With that one field, alignment is forced everywhere: the bridge is then the
unique polarity-respecting identification. -/
theorem aligned_forced (R : AlignedReceipt) :
    R.toTritCarrier R.negativeValue = .neg ∧
      (R.toTritCarrier R.neutralValue = .zer ∨ R.toTritCarrier R.neutralValue = .pos) := by
  refine ⟨R.negativeAligned, ?_⟩
  obtain ⟨h1, _, _⟩ := R.toReceipt.values_pairwise_ne
  have hne : R.toTritCarrier R.neutralValue ≠ R.toTritCarrier R.negativeValue := by
    intro h
    exact h1 (R.toReceipt.carrierEquivTrit.injective h).symm
  rw [R.negativeAligned] at hne
  have key : ∀ x : Trit, x ≠ Trit.neg → x = .zer ∨ x = .pos := by decide
  exact key _ hne

/-- The canonical inhabitant satisfies the repaired interface. -/
def canonicalAlignedReceipt : AlignedReceipt where
  toReceipt := canonicalReceipt
  negativeAligned := rfl

end Integration.ReceiptSocket
