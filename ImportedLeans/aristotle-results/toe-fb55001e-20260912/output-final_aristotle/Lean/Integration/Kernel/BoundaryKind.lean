import Integration.Kernel.Quotient

/-!
# Release stage and release mechanism are orthogonal coordinates

`Agda/DASHI/Core/KnowledgeBoundaryKindBidiExact.agda` (in the 6 September
tranche archive shipped with this project) makes a distinction that
`Integration.Kernel.Instances.SourceStage` does not carry.  `SourceStage` shows
that the public surface does not recover the evidence stage.  The boundary-kind
module observes that even a *known* stage transition — bounded/private to
publicly released — does not say **which mechanism** did the releasing: routine
patent publication, a contractual proprietary period, controlled government
data, export control, classification/declassification, an internal
institutional boundary, or discretionary disclosure.

**What that Agda module contains, and what it does not.**  `BoundaryKind` is a
real eight-constructor datatype and `TypedBoundaryTransition` genuinely pairs a
kind with two `BoundaryStateReceipt`s and equality proofs about the states.  But
its `BoundaryKindBoundary` record stores the inequalities
("patent publication is not declassification", …) as `Bool` fields with
`≡ false` obligations: they are declarations, not derived results.  This file
proves the corresponding statements instead, as descent facts about the two
coordinates.

## What is proved

§1 is generic, about any product of a transition coordinate and a mechanism
coordinate:

* **`kind_does_not_descend_through_transition`** and
  **`transition_does_not_descend_through_kind`** — with two distinct values on
  each side, neither coordinate is a function of the other.
* **`only_constants_descend_through_transition`** — the stronger form: on a
  fixed transition, *everything* computable from the transition coordinate
  alone is blind to the mechanism.
* `pair_refines_both`, `pair_strictly_refines_transition` — the pair is the
  join, and strictly finer than either factor, so recording the kind is a
  refinement of the release record rather than a correction of it.
* **`pooling_by_transition_merges_mechanisms`** — pooling releases by their
  transition alone puts every mechanism in one class.

§2 instantiates this on the seven mechanism labels with the single
private→public transition:

* `kinds_are_pairwise_distinct` and, as the named instances of the Agda
  declarations, `patent_publication_is_not_declassification`,
  `proprietary_period_is_not_classification`,
  `export_control_is_not_classification`.
* **`released_publicly_does_not_determine_mechanism`** — the headline: the fact
  that something was once non-public and is now public is compatible with every
  mechanism, so a "was private, now public" ledger silently merges patent
  publication with declassification.
* **`like_for_like_requires_the_kind_coordinate`** — matching on the transition
  is strictly weaker than matching on the mechanism, which is what the Agda
  record's `sameBoundaryKindRequiredForLikeForLikeEnrichment` field stipulates.

**Claim boundary.**  §1 is about arbitrary types.  The labels in §2 are finite
constructors introduced here; the file does not model any real disclosure
regime, and makes no claim about any actual document, person or institution.
-/

namespace Integration.Kernel.BoundaryKind

open Integration.Kernel.Quotient

universe u v w

/-! ## §1 Generic: a transition coordinate and a mechanism coordinate -/

section Generic

variable {T : Type u} {K : Type v}

/-- A release record: what the transition was, and by what mechanism. -/
abbrev Release (T : Type u) (K : Type v) : Type max u v := T × K

/-- The transition coordinate. -/
def transition : Release T K → T := Prod.fst

/-- The mechanism coordinate. -/
def kind : Release T K → K := Prod.snd

/-- **The transition does not determine the mechanism.** -/
theorem kind_does_not_descend_through_transition (t : T) {k₁ k₂ : K} (h : k₁ ≠ k₂) :
    ¬ DescendsThrough (kind : Release T K → K) transition :=
  not_descendsThrough_of_collision (x := (t, k₁)) (y := (t, k₂)) rfl h

/-- Nor does the mechanism determine the transition. -/
theorem transition_does_not_descend_through_kind (k : K) {t₁ t₂ : T} (h : t₁ ≠ t₂) :
    ¬ DescendsThrough (transition : Release T K → T) kind :=
  not_descendsThrough_of_collision (x := (t₁, k)) (y := (t₂, k)) rfl h

/-- **Everything computable from the transition alone is blind to the
mechanism.**  Fixing the transition, no transition-level test separates two
mechanisms. -/
theorem only_constants_descend_through_transition {W : Type w} (C : Release T K → W)
    (h : DescendsThrough C transition) (t : T) (k₁ k₂ : K) : C (t, k₁) = C (t, k₂) := by
  obtain ⟨f, hf⟩ := h
  rw [← hf (t, k₁), ← hf (t, k₂)]
  rfl

theorem pair_refines_transition : RefinedBy (transition : Release T K → T) id :=
  fun _ _ h => congrArg transition h

theorem pair_refines_kind : RefinedBy (kind : Release T K → K) id :=
  fun _ _ h => congrArg kind h

/-- Recording the mechanism strictly refines the transition record: the
transition reading survives unchanged, so this is a refinement and not a
retraction. -/
theorem pair_strictly_refines_transition (t : T) {k₁ k₂ : K} (h : k₁ ≠ k₂) :
    StrictlyRefines (transition : Release T K → T) (id : Release T K → Release T K) where
  law := pair_refines_transition
  witness := ⟨(t, k₁), (t, k₂), rfl, fun hEq => h (congrArg kind hEq)⟩

/-- **Pooling by transition merges every mechanism.**  The class of a release
under the transition-only quotient contains every mechanism whatsoever. -/
theorem pooling_by_transition_merges_mechanisms (t : T) (k k' : K) :
    ((t, k') : Release T K) ∈ fibre (transition : Release T K → T) (t, k) := rfl

end Generic

/-! ## §2 The seven mechanisms behind one private→public transition -/

/-- The boundary state of a knowledge object. -/
inductive BoundaryState : Type
  | boundedPrivate
  | releasedPublicly
  deriving DecidableEq, Repr

/-- The mechanism by which a boundary was crossed.  These are labels. -/
inductive Mechanism : Type
  | ordinaryPatentConfidentiality
  | contractualProprietaryBoundary
  | controlledGovernmentData
  | exportControlledBoundary
  | classifiedNationalSecurityBoundary
  | internalInstitutionalBoundary
  | discretionaryDisclosureBoundary
  deriving DecidableEq, Repr

open Mechanism

/-- The single private→public transition, as a coordinate value. -/
abbrev Transition : Type := BoundaryState × BoundaryState

/-- The transition every release in this section shares. -/
def privateToPublic : Transition := (BoundaryState.boundedPrivate, BoundaryState.releasedPublicly)

/-- A release: the transition, together with the mechanism that produced it. -/
abbrev TypedRelease : Type := Release Transition Mechanism

/-- The release of a given mechanism across the private→public boundary. -/
def released (m : Mechanism) : TypedRelease := (privateToPublic, m)

theorem kinds_are_pairwise_distinct (m m' : Mechanism) (h : m ≠ m') :
    kind (released m) ≠ kind (released m') := h

/-- The three named inequalities the Agda record carries as `Bool` fields. -/
theorem patent_publication_is_not_declassification :
    kind (released ordinaryPatentConfidentiality) ≠
      kind (released classifiedNationalSecurityBoundary) := by decide

theorem proprietary_period_is_not_classification :
    kind (released contractualProprietaryBoundary) ≠
      kind (released classifiedNationalSecurityBoundary) := by decide

theorem export_control_is_not_classification :
    kind (released exportControlledBoundary) ≠
      kind (released classifiedNationalSecurityBoundary) := by decide

/-- Every mechanism presents the same transition. -/
theorem every_mechanism_shares_the_transition (m m' : Mechanism) :
    transition (released m) = transition (released m') := rfl

/-- **"Was private, now public" does not determine the mechanism.**  A ledger
that records only the stage transition merges patent publication with
declassification. -/
theorem released_publicly_does_not_determine_mechanism :
    ¬ DescendsThrough (kind : TypedRelease → Mechanism) transition :=
  kind_does_not_descend_through_transition privateToPublic
    (k₁ := ordinaryPatentConfidentiality) (k₂ := classifiedNationalSecurityBoundary) (by decide)

/-- No transition-level test separates two mechanisms at all. -/
theorem no_transition_level_test_separates_mechanisms {W : Type w} (C : TypedRelease → W)
    (h : DescendsThrough C transition) (m m' : Mechanism) :
    C (released m) = C (released m') :=
  only_constants_descend_through_transition C h privateToPublic m m'

/-- **Like-for-like matching needs the mechanism coordinate.**  Two releases can
match on the transition and fail to match on the mechanism, so transition
matching is strictly weaker. -/
theorem like_for_like_requires_the_kind_coordinate :
    transition (released ordinaryPatentConfidentiality) =
        transition (released classifiedNationalSecurityBoundary) ∧
      kind (released ordinaryPatentConfidentiality) ≠
        kind (released classifiedNationalSecurityBoundary) :=
  ⟨rfl, by decide⟩

/-- Stage and mechanism are jointly a strict refinement of stage alone: adding
the mechanism does not revise the stage reading. -/
theorem mechanism_refines_the_release_record :
    StrictlyRefines (transition : TypedRelease → Transition) (id : TypedRelease → TypedRelease) :=
  pair_strictly_refines_transition privateToPublic
    (k₁ := ordinaryPatentConfidentiality) (k₂ := classifiedNationalSecurityBoundary) (by decide)

end Integration.Kernel.BoundaryKind
