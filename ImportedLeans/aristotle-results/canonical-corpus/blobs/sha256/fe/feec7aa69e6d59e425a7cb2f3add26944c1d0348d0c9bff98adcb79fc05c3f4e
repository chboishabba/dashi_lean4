import Integration.DeclaredCarrier
import Integration.ContextIndexedRole

/-!
# Consumer-indexed realisation and adequacy

The recurring Level-II shape is a pipeline

```
      represent        realise        observe c        answer c
  S ─────────────▶ R ─────────────▶ X ─────────────▶ Obs c ⇢ Ans c
```

a source `S`, a representation `R` of it, a realisation `X` that the
representation is turned into, and then — **per consumer** — an observation of
the realisation and a question the consumer wants answered about the source.
Formalisation/reconstruction lanes, provisioning/mediator lanes and
model-completeness lanes all instantiate it.

The single principle this file enforces is:

> adequacy is a three-place relation between a stage of the pipeline, a
> consumer and a declared carrier of states; it never upgrades itself.

Accordingly four notions are kept apart, and each separation is proved by a
witness rather than asserted:

* `RepresentationAdequate` — the representation alone answers the question;
* `RealisationAdequate` — the realised state answers it (the *mediator* level);
* `AdequateFor c` — the consumer's own observation of the realised state
  answers *its* question;
* `AdequateGlobally` — every consumer in a declared family is adequate.

No new factorisation or determination notion is introduced: every one of these
is `Integration.CoordinateSufficiency.Determines` of some composite, and the
declared-carrier version is `Integration.DeclaredCarrier.DeterminesOn`.

## Contents

* `Pipeline`, `Pipeline.state`, `ConsumerSpec` — the shape;
* `adequate_chain` — the implications that *do* hold, downstream to upstream;
* `representation_not_realisation`, `realisation_not_consumer` — and both
  converses refuted, so the stages are genuinely distinct;
* `adequateFor_not_transfers` — **`AdequateFor c₁ R` does not imply
  `AdequateFor c₂ R`**: one observation, two consumers, one adequate and one
  not;
* `AdequateOn` — adequacy on a declared carrier;
* `adequateOn_not_adequate` — **`DeterminesOn (D, O, C)` does not imply
  `Determines (O, C)`**, in the adequacy vocabulary;
* `Exhaustive` — exhaustiveness as *evidence*: a record carrying the proof that
  the declared carrier is everything;
* `adequate_of_adequateOn_exhaustive` — **`AdequateOnDeclaredCarrier` +
  `Exhaustive` → `AdequateGlobally`**, the only licensed upgrade;
* `ExhaustiveFamily`, `adequateGlobally_of_family` — the same upgrade along the
  consumer index;
* `CoverageDeclaration`, `flag_does_not_give_exhaustive`,
  `exhaustive_flag_free` — and the negative that makes the previous item
  load-bearing: a `Bool` field asserting exhaustive coverage yields no
  `Exhaustive` evidence, since the flag can be set on a carrier that is not
  exhaustive at all.

Every carrier below is `ℕ`, `Bool`, `Unit` or a finite label type.  Nothing here
is a claim about any domain.
-/

namespace Integration.RealisationAdequacy

open Integration.CoordinateSufficiency
open Integration.DeclaredCarrier
open Integration.ContextIndexedRole

/-! ## The pipeline and its consumers -/

/-- A source, a representation of it and a realisation of the representation. -/
structure Pipeline (S R X : Type) where
  /-- How a source state is represented. -/
  represent : S → R
  /-- How a representation is realised. -/
  realise : R → X

variable {S R X : Type}

/-- The realised state of a source. -/
def Pipeline.state (P : Pipeline S R X) : S → X := fun s => P.realise (P.represent s)

/-- A consumer: what it can observe of the realisation, and what it needs to
know about the source. -/
structure ConsumerSpec (S X : Type) where
  /-- The consumer's observation carrier. -/
  Obs : Type
  /-- What the consumer observes of the realised state. -/
  observe : X → Obs
  /-- The consumer's answer carrier. -/
  Ans : Type
  /-- The question the consumer needs answered about the source. -/
  demand : S → Ans

/-! ## The four adequacy notions -/

/-- The representation alone answers the consumer's question. -/
def RepresentationAdequate (P : Pipeline S R X) (c : ConsumerSpec S X) : Prop :=
  Determines P.represent c.demand

/-- The realised state answers the consumer's question: the mediator level. -/
def RealisationAdequate (P : Pipeline S R X) (c : ConsumerSpec S X) : Prop :=
  Determines P.state c.demand

/-- **Consumer adequacy.**  The consumer's own observation of the realised state
answers the consumer's own question. -/
def AdequateFor (P : Pipeline S R X) (c : ConsumerSpec S X) : Prop :=
  Determines (fun s => c.observe (P.state s)) c.demand

/-- **Global adequacy** over a declared family of consumers. -/
def AdequateGlobally {ι : Type} (P : Pipeline S R X) (cs : ι → ConsumerSpec S X) : Prop :=
  ∀ i, AdequateFor P (cs i)

/-! ## What follows from what -/

/-- Consumer adequacy implies mediator adequacy: the observation is a further
coarsening, so if it suffices then the state it is computed from suffices. -/
theorem realisationAdequate_of_adequateFor {P : Pipeline S R X} {c : ConsumerSpec S X}
    (h : AdequateFor P c) : RealisationAdequate P c :=
  determines_of_upstream c.observe h

/-- Mediator adequacy implies representation adequacy, for the same reason. -/
theorem representationAdequate_of_realisationAdequate {P : Pipeline S R X}
    {c : ConsumerSpec S X} (h : RealisationAdequate P c) : RepresentationAdequate P c :=
  determines_of_upstream P.realise h

/-- **The chain.**  Adequacy propagates upstream and only upstream. -/
theorem adequate_chain {P : Pipeline S R X} {c : ConsumerSpec S X} (h : AdequateFor P c) :
    RealisationAdequate P c ∧ RepresentationAdequate P c :=
  ⟨realisationAdequate_of_adequateFor h,
    representationAdequate_of_realisationAdequate (realisationAdequate_of_adequateFor h)⟩

/-- **Refining the observation preserves adequacy.**  If a coarser observation
`o'` — a reading `f` of `o` — already answers the question, then `o` does. -/
theorem adequate_of_finer_observation {P : Pipeline S R X} {Obs Obs' Ans : Type}
    {o : X → Obs} {o' : X → Obs'} {q : S → Ans} (f : Obs → Obs')
    (hf : ∀ x, o' x = f (o x))
    (h : Determines (fun s => o' (P.state s)) q) :
    Determines (fun s => o (P.state s)) q := by
  intro x y hxy
  refine h x y ?_
  show o' (P.state x) = o' (P.state y)
  rw [hf, hf]
  exact congrArg f hxy

/-! ### The stages are distinct -/

/-- A pipeline whose representation is faithful and whose realisation is not. -/
def collapsingPipeline : Pipeline ℕ ℕ Unit where
  represent := id
  realise := fun _ => ()

/-- The consumer of the collapsing pipeline. -/
def collapsedConsumer : ConsumerSpec ℕ Unit where
  Obs := Unit
  observe := id
  Ans := ℕ
  demand := id

/-- **Representation adequacy does not give realisation adequacy.**  A faithful
representation that is realised into a one-point carrier answers nothing. -/
theorem representation_not_realisation :
    RepresentationAdequate collapsingPipeline collapsedConsumer ∧
      ¬ RealisationAdequate collapsingPipeline collapsedConsumer := by
  refine ⟨fun x y hxy => hxy, ?_⟩
  intro h
  have h01 : (0 : ℕ) = 1 := h 0 1 rfl
  omega

/-- A faithful pipeline. -/
def faithfulPipeline : Pipeline ℕ ℕ ℕ where
  represent := id
  realise := id

/-- A consumer of it that sees only parity but wants the state. -/
def parityConsumer : ConsumerSpec ℕ ℕ where
  Obs := ℕ
  observe := fun n => n % 2
  Ans := ℕ
  demand := id

/-- **Realisation adequacy does not give consumer adequacy.**  The realised
state determines the answer; the consumer's view of it does not.  This is the
mediator/consumer separation. -/
theorem realisation_not_consumer :
    RealisationAdequate faithfulPipeline parityConsumer ∧
      ¬ AdequateFor faithfulPipeline parityConsumer := by
  refine ⟨fun x y hxy => hxy, ?_⟩
  intro h
  have h02 : (0 : ℕ) = 2 := h 0 2 rfl
  omega

/-- A consumer that sees parity and only wants parity. -/
def parityQuestion : ConsumerSpec ℕ ℕ where
  Obs := ℕ
  observe := fun n => n % 2
  Ans := ℕ
  demand := fun n => n % 2

/-- **Adequacy is consumer-relative.**  One pipeline, one observation, two
consumers: the observation is adequate for the consumer that asks about parity
and inadequate for the consumer that asks about the state.  So `AdequateFor c₁`
never transfers to `AdequateFor c₂`. -/
theorem adequateFor_not_transfers :
    AdequateFor faithfulPipeline parityQuestion ∧
      ¬ AdequateFor faithfulPipeline parityConsumer :=
  ⟨fun _ _ hxy => hxy, realisation_not_consumer.2⟩

/-! ## Declared carriers, and the one licensed upgrade -/

/-- Adequacy **on a declared carrier** of source states.  States outside the
carrier are never compared. -/
def AdequateOn (D : S → Prop) (P : Pipeline S R X) (c : ConsumerSpec S X) : Prop :=
  DeterminesOn D (fun s => c.observe (P.state s)) c.demand

/-- Global adequacy restricts to any declared carrier. -/
theorem adequateOn_of_adequateFor {D : S → Prop} {P : Pipeline S R X} {c : ConsumerSpec S X}
    (h : AdequateFor P c) : AdequateOn D P c := determinesOn_of_determines h

/-- **Exhaustiveness as evidence.**  Not a `Bool` field: a record whose single
field is the proof that the declared carrier is all of `S`. -/
structure Exhaustive (D : S → Prop) where
  /-- Every state of the ambient type lies in the declared carrier. -/
  covers : ∀ s, D s

/-- **The licensed upgrade.**  Adequacy on the declared carrier plus
exhaustiveness *evidence* gives adequacy outright — and this is the only route
from the local claim to the global one. -/
theorem adequate_of_adequateOn_exhaustive {D : S → Prop} {P : Pipeline S R X}
    {c : ConsumerSpec S X} (h : AdequateOn D P c) (e : Exhaustive D) : AdequateFor P c :=
  fun x y hxy => h x y (e.covers x) (e.covers y) hxy

/-- The declared carrier of the witness below: the two smallest naturals. -/
def small (n : ℕ) : Prop := n < 2

/-- **`DeterminesOn` does not imply `Determines`, in the adequacy vocabulary.**
Parity is adequate for the state-question on the two-element declared carrier
and inadequate on `ℕ`.  A model complete in its own chart licenses nothing about
the exterior. -/
theorem adequateOn_not_adequate :
    AdequateOn small faithfulPipeline parityConsumer ∧
      ¬ AdequateFor faithfulPipeline parityConsumer := by
  refine ⟨?_, realisation_not_consumer.2⟩
  intro x y hx hy hxy
  have hx' : x < 2 := hx
  have hy' : y < 2 := hy
  have hxy' : x % 2 = y % 2 := hxy
  show x = y
  omega

/-- Hence the exhaustiveness hypothesis of `adequate_of_adequateOn_exhaustive`
is load-bearing: the declared carrier here has no `Exhaustive` evidence. -/
theorem small_not_exhaustive : ¬ Nonempty (Exhaustive small) := by
  rintro ⟨e⟩
  have h5 : (5 : ℕ) < 2 := e.covers 5
  omega

/-! ### Exhaustiveness along the consumer index -/

/-- The consumer family `cs` is exhaustive of the consumers that matter: every
consumer of interest is one of the listed ones. -/
structure ExhaustiveFamily {ι : Type} (cs : ι → ConsumerSpec S X)
    (interest : ConsumerSpec S X → Prop) where
  /-- Every consumer of interest appears in the family. -/
  listed : ∀ c, interest c → ∃ i, cs i = c

/-- **Adequacy for a listed family upgrades to adequacy for every consumer of
interest exactly when the family is exhaustive of them.** -/
theorem adequateFor_of_exhaustiveFamily {ι : Type} {P : Pipeline S R X}
    {cs : ι → ConsumerSpec S X} {interest : ConsumerSpec S X → Prop}
    (hfam : ExhaustiveFamily cs interest) (hall : AdequateGlobally P cs)
    {c : ConsumerSpec S X} (hc : interest c) : AdequateFor P c := by
  obtain ⟨i, rfl⟩ := hfam.listed c hc
  exact hall i

/-- **And without exhaustiveness of the family it fails.**  A one-element family
containing only the parity-question consumer is globally adequate, while the
state-question consumer — not in the family — is not adequate. -/
theorem adequateGlobally_not_universal :
    AdequateGlobally faithfulPipeline (fun _ : Unit => parityQuestion) ∧
      ¬ AdequateFor faithfulPipeline parityConsumer :=
  ⟨fun _ => adequateFor_not_transfers.1, adequateFor_not_transfers.2⟩

/-! ### A declared coverage flag is not evidence -/

/-- A declared carrier together with a `Bool` field asserting that it is
exhaustive: the shape the corpus atlases use. -/
structure CoverageDeclaration (S : Type) where
  /-- The declared carrier. -/
  carrier : S → Prop
  /-- The artefact's own assertion that the carrier is everything. -/
  claimsExhaustive : Bool

/-- **A coverage flag yields no exhaustiveness evidence.**  Here is a
declaration whose flag is set and whose carrier is not exhaustive, so no
inference from the flag to `Exhaustive` can be sound. -/
theorem flag_does_not_give_exhaustive :
    ∃ d : CoverageDeclaration ℕ,
      d.claimsExhaustive = true ∧ ¬ Nonempty (Exhaustive d.carrier) :=
  ⟨⟨small, true⟩, rfl, small_not_exhaustive⟩

/-- And the flag is free in the other direction too: two declarations of the
same carrier disagreeing only on the flag. -/
theorem exhaustive_flag_free :
    ∃ d e : CoverageDeclaration ℕ,
      d.carrier = e.carrier ∧ d.claimsExhaustive ≠ e.claimsExhaustive :=
  ⟨⟨small, true⟩, ⟨small, false⟩, rfl, by decide⟩

/-- **The upgrade, packaged.**  Adequacy on a declared carrier plus genuine
exhaustiveness evidence gives global adequacy; the same adequacy plus a set
`Bool` flag gives nothing, because the flag is compatible with a non-exhaustive
carrier.  The two halves together are the discipline this file enforces. -/
theorem upgrade_needs_evidence_not_a_flag :
    (∀ (D : ℕ → Prop) (P : Pipeline ℕ R X) (c : ConsumerSpec ℕ X),
      AdequateOn D P c → Exhaustive D → AdequateFor P c) ∧
    (∃ d : CoverageDeclaration ℕ,
      d.claimsExhaustive = true ∧
        AdequateOn d.carrier faithfulPipeline parityConsumer ∧
        ¬ AdequateFor faithfulPipeline parityConsumer) :=
  ⟨fun _ _ _ h e => adequate_of_adequateOn_exhaustive h e,
    ⟨⟨small, true⟩, rfl, adequateOn_not_adequate.1, adequateOn_not_adequate.2⟩⟩

end Integration.RealisationAdequacy
