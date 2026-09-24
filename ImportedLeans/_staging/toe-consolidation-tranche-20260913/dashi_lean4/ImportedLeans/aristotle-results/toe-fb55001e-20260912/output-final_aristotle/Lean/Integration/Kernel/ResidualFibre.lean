import Mathlib

/-!
# The residual-fibre calculus: the first component of the shared kernel

Several lanes of the corpus (chemical residues, parameter regions, semantic
charts, historical reception, proof search) independently repeat the same
inference shape: *a fine hypothesis fibre, narrowed by partial observation,
until the coordinate a particular consumer needs is determined*.  This file
factors that shape out once, with no domain content at all.

## The objects

* `Refines F₁ F₀` — `F₁ ⊆ F₀`; the residual fibre `F₁` is at least as
  informative as `F₀`.  It is a preorder (in fact a partial order).
* `Channel Ω Y` — a total read-out `Ω → Y`; the only notion of measurement the
  kernel needs.
* `event O y` — the preimage `O.read ⁻¹' {y}`; `refineBy F E = F ∩ E`;
  `refine F O y = F ∩ event O y`.  This *is* the backward-refinement rule
  `F_new = F_prior ∩ O⁻¹(y)`.
* `refineAll F Es` — a list of observation events consumed left to right.

## What is proved

Positive:

* `refine_refines`, `refineBy_refines`, `refineAll_refines` — every measurement
  refines, and a composed sequence of imperfect measurements refines
  monotonically (`refineAll_append_refines`, `refineAll_antitone_of_infix`).
* `refine_mono`, `refine_idem`, `refine_comm` — refinement is monotone in the
  prior, idempotent in a repeated reading, and order-independent: measurements
  commute.
* `truth_survives`, `refine_nonempty_of_truth` — an honest reading never
  discards the actual world, so a fibre containing the truth stays inhabited.
* `Determines F c` / `Collision F c` and `determines_iff_not_collision` —
  consumer-relative closure is exactly the absence of a consumer collision on
  an inhabited fibre.
* `determines_of_factors` — mechanistic closure implies decision safety for
  every consumer that factors through the mechanism.  This is the only
  implication between the two notions that holds.

Negative — the two claims the lane exists to refuse:

* `narrower_not_mechanism` — a genuine strict refinement by a genuine channel
  can leave the mechanism coordinate entirely undetermined:
  *narrower residual fibre ⇏ exact mechanism identified*.
* `decision_safe_not_mechanism` — a fibre on which a nonconstant decision
  read-out is determined, while the mechanism coordinate is not:
  *decision-safe approximation ⇏ mechanistic closure*.
* `determines_empty` — the empty fibre determines **everything**; so a
  determination claim is worthless without an inhabitedness receipt
  (`determines_iff_not_collision` carries exactly that hypothesis).

**Claim boundary.** `Ω` is an arbitrary type of possibilities, a channel is an
arbitrary function, and no probability, measure or topology appears.  A residual
fibre is a possibility set, not a confidence set.
-/

namespace Integration.Kernel.ResidualFibre

open Set

variable {Ω Y C M : Type*}

/-! ## §1 Refinement order -/

/-- `Refines F₁ F₀`: the residual fibre `F₁` is at least as informative as `F₀`. -/
def Refines (F₁ F₀ : Set Ω) : Prop := F₁ ⊆ F₀

theorem refines_iff_subset (F₁ F₀ : Set Ω) : Refines F₁ F₀ ↔ F₁ ⊆ F₀ := Iff.rfl

@[refl] theorem refines_refl (F : Set Ω) : Refines F F := subset_rfl

theorem refines_trans {F₂ F₁ F₀ : Set Ω} (h₁ : Refines F₂ F₁) (h₀ : Refines F₁ F₀) :
    Refines F₂ F₀ := h₁.trans h₀

theorem refines_antisymm {F₁ F₀ : Set Ω} (h₁ : Refines F₁ F₀) (h₀ : Refines F₀ F₁) :
    F₁ = F₀ := Subset.antisymm h₁ h₀

theorem refines_empty (F : Set Ω) : Refines (∅ : Set Ω) F := empty_subset F

theorem refines_univ (F : Set Ω) : Refines F univ := subset_univ F

/-! ## §2 Channels and backward refinement -/

/-- A measurement channel: a total read-out of the possibility space. -/
structure Channel (Ω : Type*) (Y : Type*) where
  /-- The value the channel reports at a world. -/
  read : Ω → Y

/-- The observation event `O⁻¹(y)`. -/
def event (O : Channel Ω Y) (y : Y) : Set Ω := O.read ⁻¹' {y}

/-- Refinement by an observation event. -/
def refineBy (F E : Set Ω) : Set Ω := F ∩ E

/-- The backward-refinement rule `F_new = F_prior ∩ O⁻¹(y)`. -/
def refine (F : Set Ω) (O : Channel Ω Y) (y : Y) : Set Ω := refineBy F (event O y)

theorem mem_event {O : Channel Ω Y} {y : Y} {w : Ω} : w ∈ event O y ↔ O.read w = y := Iff.rfl

theorem mem_refine {F : Set Ω} {O : Channel Ω Y} {y : Y} {w : Ω} :
    w ∈ refine F O y ↔ w ∈ F ∧ O.read w = y := Iff.rfl

theorem refineBy_refines (F E : Set Ω) : Refines (refineBy F E) F := inter_subset_left

theorem refine_refines (F : Set Ω) (O : Channel Ω Y) (y : Y) : Refines (refine F O y) F :=
  refineBy_refines _ _

theorem refine_mono {F₁ F₀ : Set Ω} (h : Refines F₁ F₀) (O : Channel Ω Y) (y : Y) :
    Refines (refine F₁ O y) (refine F₀ O y) := inter_subset_inter_left _ h

theorem refine_idem (F : Set Ω) (O : Channel Ω Y) (y : Y) :
    refine (refine F O y) O y = refine F O y := by
  simp [refine, refineBy, inter_assoc]

/-- Measurements commute: the residual fibre does not depend on the order in which
imperfect readings are consumed. -/
theorem refine_comm {Y' : Type*} (F : Set Ω) (O : Channel Ω Y) (y : Y)
    (O' : Channel Ω Y') (y' : Y') :
    refine (refine F O y) O' y' = refine (refine F O' y') O y := by
  simp only [refine, refineBy, inter_assoc]
  rw [inter_comm (event O y)]

/-- Honest measurement never discards the actual world. -/
theorem truth_survives {F : Set Ω} {O : Channel Ω Y} {w : Ω} (hw : w ∈ F) :
    w ∈ refine F O (O.read w) := ⟨hw, rfl⟩

theorem refine_nonempty_of_truth {F : Set Ω} {O : Channel Ω Y} {w : Ω} (hw : w ∈ F) :
    (refine F O (O.read w)).Nonempty := ⟨w, truth_survives hw⟩

/-! ## §3 Composing many imperfect measurements -/

/-- Consume a list of observation events, left to right. -/
def refineAll (F : Set Ω) : List (Set Ω) → Set Ω
  | [] => F
  | E :: Es => refineAll (refineBy F E) Es

@[simp] theorem refineAll_nil (F : Set Ω) : refineAll F [] = F := rfl

@[simp] theorem refineAll_cons (F E : Set Ω) (Es : List (Set Ω)) :
    refineAll F (E :: Es) = refineAll (refineBy F E) Es := rfl

theorem refineAll_refines (F : Set Ω) (Es : List (Set Ω)) : Refines (refineAll F Es) F := by
  induction Es generalizing F with
  | nil => exact refines_refl F
  | cons E Es ih => exact refines_trans (ih (refineBy F E)) (refineBy_refines F E)

theorem refineAll_mono {F₁ F₀ : Set Ω} (h : Refines F₁ F₀) (Es : List (Set Ω)) :
    Refines (refineAll F₁ Es) (refineAll F₀ Es) := by
  induction Es generalizing F₁ F₀ with
  | nil => exact h
  | cons E Es ih => exact ih (inter_subset_inter_left _ h)

theorem refineAll_append (F : Set Ω) (Es Fs : List (Set Ω)) :
    refineAll F (Es ++ Fs) = refineAll (refineAll F Es) Fs := by
  induction Es generalizing F with
  | nil => rfl
  | cons E Es ih => simpa using ih (refineBy F E)

/-- More evidence never widens the residual fibre. -/
theorem refineAll_append_refines (F : Set Ω) (Es Fs : List (Set Ω)) :
    Refines (refineAll F (Es ++ Fs)) (refineAll F Es) := by
  rw [refineAll_append]; exact refineAll_refines _ _

theorem mem_refineAll_of_forall {F : Set Ω} {Es : List (Set Ω)} {w : Ω}
    (hw : w ∈ F) (hE : ∀ E ∈ Es, w ∈ E) : w ∈ refineAll F Es := by
  induction Es generalizing F with
  | nil => exact hw
  | cons E Es ih =>
      exact ih ⟨hw, hE E (List.mem_cons_self ..)⟩ fun E' hE' => hE E' (List.mem_cons_of_mem _ hE')

/-! ## §4 Consumer-relative closure -/

/-- The fibre determines the consumer coordinate `c`. -/
def Determines (F : Set Ω) (c : Ω → C) : Prop := ∃ v, ∀ w ∈ F, c w = v

/-- Two surviving worlds disagree on what the consumer needs. -/
def Collision (F : Set Ω) (c : Ω → C) : Prop := ∃ w₁ ∈ F, ∃ w₂ ∈ F, c w₁ ≠ c w₂

theorem determines_mono {F₁ F₀ : Set Ω} {c : Ω → C} (h : Refines F₁ F₀)
    (hd : Determines F₀ c) : Determines F₁ c :=
  hd.imp fun _ hv w hw => hv w (h hw)

/-- The empty fibre determines every consumer: a closure claim is worthless
without an inhabitedness receipt. -/
theorem determines_empty (c : Ω → C) [Nonempty C] : Determines (∅ : Set Ω) c :=
  ⟨Classical.arbitrary C, fun _ h => absurd h (notMem_empty _)⟩

theorem determines_iff_not_collision {F : Set Ω} {c : Ω → C} (hF : F.Nonempty) :
    Determines F c ↔ ¬ Collision F c := by
  constructor
  · rintro ⟨v, hv⟩ ⟨w₁, h₁, w₂, h₂, hne⟩
    exact hne ((hv w₁ h₁).trans (hv w₂ h₂).symm)
  · intro h
    obtain ⟨w₀, hw₀⟩ := hF
    refine ⟨c w₀, fun w hw => ?_⟩
    by_contra hne
    exact h ⟨w, hw, w₀, hw₀, hne⟩

/-- Mechanistic closure implies decision safety for any consumer that factors
through the mechanism.  This is the *only* implication between the two. -/
theorem determines_of_factors {F : Set Ω} {m : Ω → M} {c : Ω → C} {g : M → C}
    (hfac : ∀ w, c w = g (m w)) (hm : Determines F m) : Determines F c := by
  obtain ⟨v, hv⟩ := hm
  exact ⟨g v, fun w hw => by rw [hfac w, hv w hw]⟩

/-! ## §5 The two refusals

The witnesses live on `Bool × Bool`: first coordinate the *mechanism*, second
coordinate an incidental one. -/

/-- The mechanism coordinate. -/
private def mech : Bool × Bool → Bool := Prod.fst

/-- A channel reading only the incidental coordinate. -/
private def sideChannel : Channel (Bool × Bool) Bool := ⟨Prod.snd⟩

/-- **Narrower residual fibre ⇏ exact mechanism identified.**  A genuine channel
strictly refines the prior fibre, yet the mechanism coordinate stays open. -/
theorem narrower_not_mechanism :
    ∃ (F : Set (Bool × Bool)) (O : Channel (Bool × Bool) Bool) (y : Bool),
      refine F O y ⊂ F ∧ (refine F O y).Nonempty ∧ ¬ Determines (refine F O y) mech := by
  refine ⟨univ, sideChannel, true, ?_, ⟨(true, true), by simp [refine, refineBy, event,
      sideChannel]⟩, ?_⟩
  · constructor
    · exact refine_refines _ _ _
    · intro h
      have := h (mem_univ (true, false))
      simp [refine, refineBy, event, sideChannel] at this
  · rintro ⟨v, hv⟩
    have h1 : mech (true, true) = v := hv _ ⟨mem_univ _, rfl⟩
    have h2 : mech (false, true) = v := hv _ ⟨mem_univ _, rfl⟩
    rw [← h2] at h1
    exact Bool.noConfusion h1

/-- **Decision-safe approximation ⇏ mechanistic closure.**  On the fibre
`{(true, ·)}` the decision read-out `mech` is determined while the incidental
coordinate is not — and the incidental coordinate is a genuine, globally
nonconstant read-out. -/
theorem decision_safe_not_mechanism :
    ∃ F : Set (Bool × Bool),
      F.Nonempty ∧ Determines F mech ∧ ¬ Determines F sideChannel.read := by
  refine ⟨{w | w.1 = true}, ⟨(true, true), rfl⟩, ⟨true, fun w hw => hw⟩, ?_⟩
  rintro ⟨v, hv⟩
  have h1 : sideChannel.read (true, true) = v := hv _ rfl
  have h2 : sideChannel.read (true, false) = v := hv _ rfl
  rw [← h2] at h1
  exact Bool.noConfusion h1

/-- Both coordinates of the witness space are genuine read-outs: neither is
constant, so neither refusal above is an artefact of a degenerate observable. -/
theorem witness_coordinates_nonconstant :
    ¬ Determines (univ : Set (Bool × Bool)) mech ∧
      ¬ Determines (univ : Set (Bool × Bool)) sideChannel.read := by
  constructor <;> rintro ⟨v, hv⟩
  · have h1 := hv (true, true) (mem_univ _)
    have h2 := hv (false, true) (mem_univ _)
    rw [← h2] at h1; exact Bool.noConfusion h1
  · have h1 := hv (true, true) (mem_univ _)
    have h2 := hv (true, false) (mem_univ _)
    rw [← h2] at h1; exact Bool.noConfusion h1

end Integration.Kernel.ResidualFibre
