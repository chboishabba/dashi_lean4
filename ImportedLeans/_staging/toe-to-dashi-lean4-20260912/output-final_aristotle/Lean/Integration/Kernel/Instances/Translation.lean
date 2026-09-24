import Integration.Kernel.Reopen

/-!
# Charts, translations and path-dependent reception

Two more instances of the kernel, both about *transport* rather than inference.

## §1 Multi-chart records and lossy translation

A `Record` carries six coordinates that the corpus insists are different charts
of the same situation: legal/state, clinical, lived-subject, community,
commercial and sovereign.

* `clinicalTranslation` preserves the clinical coordinate and blanks the
  subject-authorship one.  `translation_preserves_clinical` and
  `translation_erases_subject` prove exactly that: **a translation can preserve
  one coordinate and erase another.**
* `erased_coordinate_is_unrecoverable` — no function of the translated record
  returns the original subject coordinate.  Erasure is not repairable
  downstream.
* Reintroducing it afterwards produces an `introduced` coordinate, and
  `reintroduction_is_not_restoration` (an instance of
  `Integration.Kernel.Reopen.no_rule_recovers_origin`) shows that this is not
  the same as the inherited lineage.

## §2 Reception history is path-dependent

With `reinterpret` and `institutionalise` acting on a fine state:

* `reinterpret_institutionalise_noncommute` — `R ∘ I ≠ I ∘ R`;
* `same_present_vocabulary_not_same_history` — the two paths agree on the
  coarse present coordinate and differ on the fine one, so **same present
  vocabulary ⇏ same reception history**;
* `same_future_cone_not_same_transport_history` — the same statement read
  forwards: two admissible paths landing in the same coarse future cone retain
  different fine relation coordinates.
* `coarse_code_is_not_a_history_certificate` — no function of the coarse code
  returns the path taken.

**Claim boundary.** A "chart" is a coordinate of a six-field record of labels; a
"path" is a composite of two functions on a two-bit state.  Nothing is claimed
about any actual legal, clinical or intellectual history.
-/

namespace Integration.Kernel.Instances.Translation

open Integration.Kernel.Reopen

/-! ## §1 Charts -/

/-- A situation described in six charts at once. -/
structure Record where
  /-- The state/legal chart. -/
  legal : ℕ
  /-- The clinical chart. -/
  clinical : ℕ
  /-- The lived-subject chart, including authorship of the account. -/
  subject : ℕ
  /-- The community chart. -/
  community : ℕ
  /-- The commercial chart. -/
  commercial : ℕ
  /-- The sovereign chart. -/
  sovereign : ℕ
  deriving DecidableEq, Repr

/-- A translation into the clinical register: the clinical coordinate survives,
the subject's authorship does not. -/
def clinicalTranslation (r : Record) : Record := { r with subject := 0 }

theorem translation_preserves_clinical (r : Record) :
    (clinicalTranslation r).clinical = r.clinical := rfl

/-- **A translation can preserve one coordinate and erase another.** -/
theorem translation_erases_subject :
    ∃ r : Record, (clinicalTranslation r).clinical = r.clinical ∧
      (clinicalTranslation r).subject ≠ r.subject := by
  refine ⟨⟨0, 1, 1, 0, 0, 0⟩, rfl, ?_⟩
  simp [clinicalTranslation]

/-- The erased coordinate cannot be recovered from the translated record. -/
theorem erased_coordinate_is_unrecoverable :
    ¬ ∃ f : Record → ℕ, ∀ r : Record, f (clinicalTranslation r) = r.subject := by
  rintro ⟨f, hf⟩
  have h1 := hf ⟨0, 0, 0, 0, 0, 0⟩
  have h2 := hf ⟨0, 0, 1, 0, 0, 0⟩
  simp [clinicalTranslation] at h1 h2
  rw [h1] at h2
  exact zero_ne_one h2

/-- **Reintroduced downstream ≠ restored inherited lineage.**  A value put back
after the translation carries the `introduced` origin, and no rule reading the
value alone can tell the two apart. -/
theorem reintroduction_is_not_restoration :
    ¬ ∃ f : ℕ → Origin, ∀ c : Coordinate ℕ, f c.value = c.origin :=
  no_rule_recovers_origin 0

/-! ## §2 Reception paths -/

/-- The fine state: a coarse present coordinate together with a fine relation
coordinate. -/
abbrev Fine := Bool × Bool

/-- Institutionalisation. -/
def institutionalise (s : Fine) : Fine := (s.1, true)

/-- Reinterpretation. -/
def reinterpret (s : Fine) : Fine := (s.1, !s.2)

/-- **`R ∘ I ≠ I ∘ R`.** -/
theorem reinterpret_institutionalise_noncommute :
    reinterpret ∘ institutionalise ≠ institutionalise ∘ reinterpret := by
  intro h
  have := congrFun h (true, true)
  simp [reinterpret, institutionalise, Prod.ext_iff] at this

/-- The coarse present coordinate. -/
def coarse (s : Fine) : Bool := s.1

/-- **Same present vocabulary ⇏ same reception history.** -/
theorem same_present_vocabulary_not_same_history (s : Fine) :
    coarse (reinterpret (institutionalise s)) = coarse (institutionalise (reinterpret s)) ∧
      reinterpret (institutionalise s) ≠ institutionalise (reinterpret s) := by
  refine ⟨rfl, ?_⟩
  simp [reinterpret, institutionalise, Prod.ext_iff]

/-- **Same future cone ⇏ same admitted transport history**: two admissible
paths land in the same coarse code and keep different fine coordinates. -/
theorem same_future_cone_not_same_transport_history :
    ∃ p q : Fine → Fine,
      (∀ s, coarse (p s) = coarse (q s)) ∧ (∀ s, (p s).2 ≠ (q s).2) := by
  refine ⟨reinterpret ∘ institutionalise, institutionalise ∘ reinterpret, fun s => rfl, fun s => ?_⟩
  simp [reinterpret, institutionalise]

/-- No rule reading the coarse code returns which path was taken. -/
theorem coarse_code_is_not_a_history_certificate :
    ¬ ∃ f : Bool → Fine, ∀ s : Fine,
        f (coarse (reinterpret (institutionalise s))) = reinterpret (institutionalise s) ∧
          f (coarse (institutionalise (reinterpret s))) = institutionalise (reinterpret s) := by
  rintro ⟨f, hf⟩
  obtain ⟨h1, h2⟩ := hf (true, true)
  rw [show coarse (institutionalise (reinterpret ((true, true) : Fine)))
      = coarse (reinterpret (institutionalise ((true, true) : Fine))) from rfl, h1] at h2
  simp [reinterpret, institutionalise, Prod.ext_iff] at h2

end Integration.Kernel.Instances.Translation
