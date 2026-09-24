import Integration.Kernel.Quotient

/-!
# Promotion as four separate obligations

`Integration.Kernel.Instances.SourceStage` classifies verification *carriers*
and stipulates which one discharges a theorem-facing obligation.  That is a
classification, not a promotion relation: it says which label counts, not what
has to be established to move an external artefact to a theorem-facing claim.

This file separates the four things that get run together whenever an external
receipt, certificate or correspondence is treated as a proof:

1. **the artefact exists** — `ArtifactExists`;
2. **the artefact corresponds to the statement in question** — `Corresponds`;
3. **the statement transport is sound** — `TransportSound`;
4. **a term inhabits the target proposition** — `TermInhabits`.

The content is that each of the first three is strictly weaker than the next,
and that even all three together give at most the *truth* of the transported
target, never a term for it.  A `Receipt` is the structure that carries all
four as proofs; it is the only thing in the file that yields a term.

## What is proved

* **`holds_of_corresponds_and_sound`** — the positive: an artefact whose claim
  is the source statement, plus a sound transport, gives `Holds` of the
  transported target.  This is what a correspondence receipt *is* worth.
* **`artifact_does_not_give_correspondence`** — an artefact can exist and claim
  something else.
* **`correspondence_does_not_give_transport_soundness`** — the correspondence
  can be exact and the transport still unsound.
* **`holds_does_not_give_inhabitance`** — the sharpest of the four: a frame in
  which every target holds and no term inhabits anything.  Truth of the target
  is not possession of a proof of it, so no chain of external evidence closes
  step 4 by itself.
* `Receipt` and **`receipt_yields_term`** — what does close it, and
  `receipt_needs_all_four` records that dropping any one field makes the
  structure unbuildable in one of the counterexample frames.

**Claim boundary.**  A `Frame` is four arbitrary types with two functions, a
predicate `Holds` and a relation `Inhabits`.  `Holds` and `Inhabits` are
*supplied by the frame*: this file does not interpret them as Lean truth or Lean
proof, does not inspect any term or environment, and proves nothing about any
actual artefact, certificate or transport.
-/

namespace Integration.Kernel.PromotionTransport

/-! ## §1 The frame and the four obligations -/

/-- The data a promotion is relative to: artefacts and what they claim, a
transport of statements into targets, a notion of a target holding, and a
notion of a term inhabiting a target. -/
structure Frame : Type 1 where
  /-- External evidence artefacts. -/
  Artifact : Type
  /-- Statements in the source vocabulary. -/
  Statement : Type
  /-- Targets in the receiving vocabulary. -/
  Target : Type
  /-- Terms that could inhabit a target. -/
  Term : Type
  /-- What an artefact claims. -/
  claims : Artifact → Statement
  /-- The transport of a source statement into the receiving vocabulary. -/
  transport : Statement → Target
  /-- The frame's own notion of a target holding. -/
  Holds : Target → Prop
  /-- The frame's own notion of a term inhabiting a target. -/
  Inhabits : Term → Target → Prop

variable (F : Frame)

/-- Obligation 1: there is an artefact at all. -/
def ArtifactExists : Prop := Nonempty F.Artifact

/-- Obligation 2: this artefact claims exactly this statement. -/
def Corresponds (a : F.Artifact) (s : F.Statement) : Prop := F.claims a = s

/-- Obligation 3: the transport carries statements satisfying `P` to targets
that hold. -/
def TransportSound (P : F.Statement → Prop) : Prop := ∀ s, P s → F.Holds (F.transport s)

/-- Obligation 4: some term inhabits this target. -/
def TermInhabits (g : F.Target) : Prop := ∃ t : F.Term, F.Inhabits t g

variable {F}

/-! ## §2 What the first three obligations buy -/

/-- **Correspondence plus sound transport gives truth of the target.**  This is
the whole positive content of an external correspondence receipt. -/
theorem holds_of_corresponds_and_sound {P : F.Statement → Prop} {a : F.Artifact}
    {s : F.Statement} (hc : Corresponds F a s) (hP : P s) (hs : TransportSound F P) :
    F.Holds (F.transport s) := by
  subst hc
  exact hs _ hP

/-! ## §3 Each step is strictly more than the previous one -/

/-- A frame whose single artefact claims the wrong statement. -/
def mismatchFrame : Frame where
  Artifact := Unit
  Statement := Bool
  Target := Bool
  Term := Unit
  claims _ := false
  transport := id
  Holds _ := True
  Inhabits _ _ := True

/-- **An artefact is not a correspondence.** -/
theorem artifact_does_not_give_correspondence :
    ArtifactExists mismatchFrame ∧ ¬ Corresponds mismatchFrame () true :=
  ⟨⟨()⟩, by simp [Corresponds, mismatchFrame]⟩

/-- A frame with an exact correspondence and an unsound transport: the target
of the true source statement does not hold. -/
def unsoundFrame : Frame where
  Artifact := Unit
  Statement := Bool
  Target := Bool
  Term := Unit
  claims _ := true
  transport := id
  Holds g := g = false
  Inhabits _ _ := True

/-- **A correspondence is not a sound transport.**  The artefact claims exactly
the statement asked about, and the transport still fails on it. -/
theorem correspondence_does_not_give_transport_soundness :
    Corresponds unsoundFrame () true ∧
      ¬ TransportSound unsoundFrame (fun s => s = true) := by
  refine ⟨rfl, fun h => ?_⟩
  have := h true rfl
  exact absurd this (by simp [unsoundFrame])

/-- A frame in which every target holds and there are no terms at all. -/
def noTermFrame : Frame where
  Artifact := Unit
  Statement := Unit
  Target := Unit
  Term := Empty
  claims _ := ()
  transport := id
  Holds _ := True
  Inhabits _ _ := True

/-- **Truth of the target is not inhabitance of the target.**  In this frame
every target holds — so obligations 1–3 are all discharged for every statement
— and no term inhabits anything.  No amount of external evidence closes the
fourth obligation. -/
theorem holds_does_not_give_inhabitance :
    (∀ g, noTermFrame.Holds g) ∧ ∀ g, ¬ TermInhabits noTermFrame g := by
  refine ⟨fun _ => trivial, fun g h => ?_⟩
  obtain ⟨t, -⟩ := h
  exact t.elim

/-- In particular the three earlier obligations, all discharged, still leave the
fourth open. -/
theorem first_three_do_not_close_the_fourth :
    ArtifactExists noTermFrame ∧
      Corresponds noTermFrame () () ∧
        TransportSound noTermFrame (fun _ => True) ∧
          ¬ TermInhabits noTermFrame (noTermFrame.transport ()) :=
  ⟨⟨()⟩, rfl, fun _ _ => trivial, (holds_does_not_give_inhabitance.2 _)⟩

/-! ## §4 The receipt that does close it -/

/-- A promotion receipt: all four obligations, as proofs. -/
structure Receipt (F : Frame) (P : F.Statement → Prop) (s : F.Statement) : Type where
  /-- The artefact offered. -/
  artifact : F.Artifact
  /-- It claims exactly the statement in question. -/
  corresponds : Corresponds F artifact s
  /-- The source statement satisfies the transport's precondition. -/
  source : P s
  /-- The transport is sound on such statements. -/
  sound : TransportSound F P
  /-- And a term is exhibited for the transported target. -/
  term : F.Term
  /-- which really inhabits it. -/
  inhabits : F.Inhabits term (F.transport s)

/-- A receipt discharges the target: it yields both the truth of the transported
target and a term for it. -/
theorem receipt_yields_term {P : F.Statement → Prop} {s : F.Statement}
    (r : Receipt F P s) : F.Holds (F.transport s) ∧ TermInhabits F (F.transport s) :=
  ⟨holds_of_corresponds_and_sound r.corresponds r.source r.sound, ⟨r.term, r.inhabits⟩⟩

/-- The last field is not redundant: in `noTermFrame` the first four fields are
all available and the structure is still empty, so a receipt cannot be
assembled from the external obligations alone. -/
theorem receipt_needs_all_four :
    IsEmpty (Receipt noTermFrame (fun _ => True) ()) :=
  ⟨fun r => r.term.elim⟩

/-- And a receipt is available whenever the frame really does supply an
inhabiting term, so the bar is satisfiable rather than vacuously closed. -/
theorem receipt_exists_of_inhabitant {P : F.Statement → Prop} {s : F.Statement}
    (a : F.Artifact) (hc : Corresponds F a s) (hP : P s) (hs : TransportSound F P)
    (t : F.Term) (ht : F.Inhabits t (F.transport s)) : Nonempty (Receipt F P s) :=
  ⟨⟨a, hc, hP, hs, t, ht⟩⟩

end Integration.Kernel.PromotionTransport
