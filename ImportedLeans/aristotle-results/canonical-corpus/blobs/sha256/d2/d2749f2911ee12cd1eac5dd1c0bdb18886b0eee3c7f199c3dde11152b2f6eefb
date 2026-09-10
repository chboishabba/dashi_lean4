import Integration.Kernel.Merge

/-!
# Telemetry gap and requirement authority

Fourth component of the shared kernel: the two governance constraints without
which the refine/merge machinery can be gamed.

## §1–§2 Telemetry: physical ≠ reported ≠ believed ≠ action

A `Telemetry` carries three read-outs of the same world — what is physically the
case, what is reported, and what is believed — together with the action taken.
`Faithful` (report = physical) and `Credulous` (belief = report) are the two
bridges.

* `telemetry_layers_separate` — a single witness in which all three read-outs
  differ at some world, so the three layers are genuinely independent data.
* `rational_wrt_report_not_rational_wrt_truth` — an action optimal against the
  *reported* state that is not optimal against the physical one:
  **rational search relative to a bad observation ⇏ rational search relative to
  the truth.**
* `faithful_credulous_transfers` — the positive counterpart: when the report is
  faithful and the belief credulous, belief-rationality *is*
  truth-rationality.  So the gap is exactly the failure of those two bridges,
  nothing more.
* `report_cannot_certify_itself` — no function from the reported state alone can
  return the physical state correctly for all telemetries with a given report,
  which is why a status claim has to be read off the canonical state and not
  off a report about it.

## §3 Requirement authority: a producer may not weaken its consumer

A `Requirement` is the set of worlds a consumer will accept; a producer's
residual fibre `F` *satisfies* it when `F ⊆ admits`.

* `weakening_manufactures_satisfaction` — without a guard, revising the
  requirement to a weaker one turns a failure into a success, with no change on
  the producer's side at all.  This is the cheat.
* `StrengthPreserving` and `satisfies_of_strength_preserving` — an authorised
  revision may only tighten (or keep) the admitted set, and then satisfying the
  revised requirement still entails satisfying the original: the cheat is
  closed exactly by the non-weakening condition.
* `authorised_revision_composes` — authorised revisions compose, so a sequence
  of small authorised revisions cannot add up to a weakening.

**Claim boundary.** "Authority" is modelled only as the non-weakening side
condition on a revision; no institution, permission system or trust model is
formalised, and nothing here checks *who* performed a revision.
-/

namespace Integration.Kernel.Authority

open Set Integration.Kernel.ResidualFibre

variable {Ω S A : Type*}

/-! ## §1 The three state layers -/

/-- Three read-outs of the same world plus the action taken. -/
structure Telemetry (Ω S A : Type*) where
  /-- What is physically the case. -/
  physical : Ω → S
  /-- What the system reports. -/
  reported : Ω → S
  /-- What the operator believes. -/
  believed : Ω → S
  /-- What is done. -/
  action : Ω → A

/-- The report matches the physical state. -/
def Faithful (T : Telemetry Ω S A) : Prop := ∀ w, T.reported w = T.physical w

/-- The belief matches the report. -/
def Credulous (T : Telemetry Ω S A) : Prop := ∀ w, T.believed w = T.reported w

/-- All three layers can differ at one and the same world. -/
theorem telemetry_layers_separate :
    ∃ T : Telemetry Unit ℕ Unit,
      (∀ w, T.physical w ≠ T.reported w) ∧ (∀ w, T.reported w ≠ T.believed w) ∧
        (∀ w, T.physical w ≠ T.believed w) := by
  refine ⟨⟨fun _ => 0, fun _ => 1, fun _ => 2, fun _ => ()⟩, ?_, ?_, ?_⟩ <;> intro w <;> simp

/-! ## §2 Rationality is relative to the layer you read -/

/-- A decision problem: which actions are good in which physical state. -/
structure DecisionProblem (S A : Type*) where
  /-- `good s a` : action `a` is acceptable in state `s`. -/
  good : S → A → Prop

/-- The action is rational against the estimate `est`. -/
def RationalWrt (D : DecisionProblem S A) (T : Telemetry Ω S A) (est : Ω → S) : Prop :=
  ∀ w, D.good (est w) (T.action w)

/-- **Rational search relative to a bad observation ⇏ rational search relative
to the truth.** -/
theorem rational_wrt_report_not_rational_wrt_truth :
    ∃ (D : DecisionProblem Bool Bool) (T : Telemetry Unit Bool Bool),
      RationalWrt D T T.reported ∧ ¬ RationalWrt D T T.physical := by
  refine ⟨⟨fun s a => a = s⟩, ⟨fun _ => true, fun _ => false, fun _ => false, fun _ => false⟩,
    fun _ => rfl, ?_⟩
  intro h
  exact Bool.noConfusion (h ())

/-- When the report is faithful and the belief credulous, belief-rationality is
truth-rationality. -/
theorem faithful_credulous_transfers {D : DecisionProblem S A} {T : Telemetry Ω S A}
    (hf : Faithful T) (hc : Credulous T) :
    RationalWrt D T T.believed ↔ RationalWrt D T T.physical := by
  constructor <;> intro h w
  · have := h w; rwa [hc w, hf w] at this
  · have := h w; rwa [← hf w, ← hc w] at this

/-- No rule reading the report alone returns the physical state correctly: two
telemetries agreeing on every report differ on the physical layer.  A status
claim therefore has to come from the canonical state, not from a report. -/
theorem report_cannot_certify_itself :
    ¬ ∃ f : Bool → Bool, ∀ T : Telemetry Unit Bool Bool, ∀ w, f (T.reported w) = T.physical w := by
  rintro ⟨f, hf⟩
  have h1 := hf ⟨fun _ => true, fun _ => false, fun _ => false, fun _ => true⟩ ()
  have h2 := hf ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => true⟩ ()
  rw [h2] at h1
  exact Bool.noConfusion h1

/-! ## §3 Requirement authority -/

/-- What a consumer will accept. -/
structure Requirement (Ω : Type*) where
  /-- The admitted worlds. -/
  admits : Set Ω

/-- The producer's residual fibre meets the requirement. -/
def Satisfies (F : Set Ω) (r : Requirement Ω) : Prop := F ⊆ r.admits

/-- `r'` is a weakening of `r`: strictly more worlds are admitted. -/
def Weakens (r' r : Requirement Ω) : Prop := r.admits ⊂ r'.admits

/-- An authorised revision may only tighten or keep the admitted set. -/
def StrengthPreserving (r' r : Requirement Ω) : Prop := r'.admits ⊆ r.admits

theorem strengthPreserving_not_weakens {r' r : Requirement Ω} (h : StrengthPreserving r' r) :
    ¬ Weakens r' r := fun hw => hw.ne (Subset.antisymm hw.subset h)

/-- **A producer attempting to satisfy a consumer may not weaken the consumer.**
Without the guard, an unchanged producer is turned from failing into passing by
revising the requirement alone. -/
theorem weakening_manufactures_satisfaction :
    ∃ (F : Set Bool) (r r' : Requirement Bool),
      Weakens r' r ∧ Satisfies F r' ∧ ¬ Satisfies F r := by
  refine ⟨univ, ⟨{true}⟩, ⟨univ⟩, ⟨subset_univ _, ?_⟩, subset_univ _, ?_⟩
  · intro h
    have : (false : Bool) ∈ ({true} : Set Bool) := h (mem_univ _)
    exact Bool.noConfusion this
  · intro h
    have : (false : Bool) ∈ ({true} : Set Bool) := h (mem_univ _)
    exact Bool.noConfusion this

/-- Under an authorised (non-weakening) revision, satisfying the revised
requirement still entails satisfying the original one. -/
theorem satisfies_of_strength_preserving {F : Set Ω} {r r' : Requirement Ω}
    (h : StrengthPreserving r' r) (hs : Satisfies F r') : Satisfies F r := hs.trans h

/-- Authorised revisions compose: no sequence of them adds up to a weakening. -/
theorem authorised_revision_composes {r r' r'' : Requirement Ω}
    (h₁ : StrengthPreserving r'' r') (h₂ : StrengthPreserving r' r) :
    StrengthPreserving r'' r := h₁.trans h₂

theorem authorised_chain_not_weakening {r r' r'' : Requirement Ω}
    (h₁ : StrengthPreserving r'' r') (h₂ : StrengthPreserving r' r) : ¬ Weakens r'' r :=
  strengthPreserving_not_weakens (authorised_revision_composes h₁ h₂)

end Integration.Kernel.Authority
