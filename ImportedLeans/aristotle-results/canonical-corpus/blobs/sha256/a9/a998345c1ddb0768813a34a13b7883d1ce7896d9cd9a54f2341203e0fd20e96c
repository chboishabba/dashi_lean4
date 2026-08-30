import Integration.PipelineAdequacy

/-!
# Claim transport: when may a locally valid claim cross a stage boundary?

The Level-II owners answer *what information does this representation preserve?*
This file asks the next question — *when may a valid claim be transported across
a stage?* — and answers it **negatively for the general shape**: the warrant that
licenses a composition is itself an instance of the existing determination owner,
so no new generic object is introduced here.

## The situation

Two locally valid arrows

```
        r₁              r₂
   S ───────▶ M ───────▶ N
```

with

* an intermediate consumer `C₁` whose question `q₁ : S → A₁` the first stage
  answers (`Determines r₁ q₁`), and
* a downstream consumer `C₂` whose question `qM : M → A` is stated **in the
  intermediate representation's own language** and which the second stage
  answers (`Determines r₂ qM`).

The global inference under test is: *does the composite answer the final
question `q : S → A` about the source?*

## What is proved

* `local_claims_do_not_compose` — the general negative.  Both local claims hold
  and the composite fails.  So `AdequateFor C₁ r₁ + AdequateFor C₂ r₂` does not
  give adequacy of `r₂ ∘ r₁`.
* `Warrant` — the missing piece, named: the downstream consumer's question, read
  back through the upstream representation, must already answer the final
  question.
* `transport_of_warrant` — the warrant plus the downstream local claim licenses
  the composite.  This is the positive theorem.
* `warrant_of_transport_of_refining` — and the warrant is *necessary* whenever
  the downstream question refines the downstream representation.
* `upstream_determination_not_sufficient` — the weaker hypothesis one is tempted
  to use instead (`Determines r₁ q`: the first stage preserves the final
  question) is **not** enough, even with both local claims.
* `transport_forces_upstream` — while it is forced by transport, so it is
  necessary and not sufficient.
* `warrant_forces_upstream`, `no_warrant_of_not_upstream` — a warrant can only
  coarsen what the upstream stage kept, so a first-stage collision rules out
  *every* warrant at once, whatever the downstream consumer asks;
* `warrant_is_a_determination`, `warrant_failure_is_a_collision` — **the
  classification**: the warrant is definitionally `Determines`, and its failure
  is definitionally a `Collision`.  Level II owns the obstruction; this file
  adds no owner.
* `sim`, `determines_iff_sim_le` — the equivalence-relation reading: a stage
  transports a claim exactly when the equivalence it induces refines the
  equivalence the downstream consumer needs.  `sim_not_transitive_across_consumers`
  is the literal shape `x ∼_{C₁} y` and `x ≁_{C₂} y`.
* `three_stage_transport`, `three_stage_needs_every_warrant` — the same
  discipline along a three-stage chain: one warrant per boundary, and dropping
  any one of them breaks the inference.

Every carrier is `ℕ`, `Unit` or a finite label type.  Nothing here is a claim
about any domain.
-/

namespace Integration.ClaimTransport

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision

variable {S M N A A₁ : Type}

/-! ## The composite -/

/-- The composite of two stages. -/
def compose (r₁ : S → M) (r₂ : M → N) : S → N := fun s => r₂ (r₁ s)

/-! ## The general negative -/

/-- **Local adequacy does not compose.**  The first stage answers its own
consumer's question, the second stage answers its own consumer's question, and
the composite answers the final question about the source in neither.

Witness: `r₁` is the parity reduction and `q₁` is the parity question (valid);
`r₂` is the identity and `qM` is the identity question (valid); the final
question is the state itself, which the composite has already destroyed. -/
theorem local_claims_do_not_compose :
    ∃ (r₁ : ℕ → ℕ) (r₂ : ℕ → ℕ) (q₁ qM q : ℕ → ℕ),
      Determines r₁ q₁ ∧ Determines r₂ qM ∧ ¬ Determines (compose r₁ r₂) q := by
  refine ⟨fun n => n % 2, id, fun n => n % 2, id, id, fun _ _ h => h, fun _ _ h => h, ?_⟩
  intro h
  have : (0 : ℕ) = 2 := h 0 2 rfl
  omega

/-! ## The warrant -/

/-- **The warrant.**  The downstream consumer's question `qM`, read back through
the upstream representation `r₁`, already answers the final question `q`.

This is not a new notion: it is `Determines` of the pulled-back question. -/
def Warrant (r₁ : S → M) (qM : M → A) (q : S → A) : Prop :=
  Determines (fun s => qM (r₁ s)) q

/-- **Transport is licensed by the warrant.**  Given the downstream local claim
and the warrant, the composite answers the final question. -/
theorem transport_of_warrant {r₁ : S → M} {r₂ : M → N} {qM : M → A} {q : S → A}
    (h₂ : Determines r₂ qM) (w : Warrant r₁ qM q) : Determines (compose r₁ r₂) q :=
  fun x y hxy => w x y (h₂ _ _ hxy)

/-- **And the warrant is necessary** whenever the downstream question refines the
downstream representation — i.e. when knowing `qM` already fixes what the second
stage produces. -/
theorem warrant_of_transport_of_refining {r₁ : S → M} {r₂ : M → N} {qM : M → A}
    {q : S → A} (href : Determines qM r₂) (h : Determines (compose r₁ r₂) q) :
    Warrant r₁ qM q :=
  fun x y hxy => h x y (href _ _ hxy)

/-- The composite claim forces the upstream stage to preserve the final
question. -/
theorem transport_forces_upstream {r₁ : S → M} {r₂ : M → N} {q : S → A}
    (h : Determines (compose r₁ r₂) q) : Determines r₁ q :=
  fun x y hxy => h x y (congrArg r₂ hxy)

/-- **But upstream preservation is not sufficient**, even together with both
local claims.  Here `r₁` is the identity — so it preserves *everything*,
including the final question — the two local claims hold, and the composite
still fails, because the downstream consumer's question is not the final one.

So the warrant genuinely relates the two consumers; it is not a property of the
upstream stage alone. -/
theorem upstream_determination_not_sufficient :
    ∃ (r₁ : ℕ → ℕ) (r₂ : ℕ → Unit) (q₁ q : ℕ → ℕ) (qM : ℕ → Unit),
      Determines r₁ q ∧ Determines r₁ q₁ ∧ Determines r₂ qM ∧
        ¬ Determines (compose r₁ r₂) q := by
  refine ⟨id, fun _ => (), id, id, fun _ => (), fun _ _ h => h, fun _ _ h => h,
    fun _ _ _ => rfl, ?_⟩
  intro h
  have : (0 : ℕ) = 1 := h 0 1 rfl
  omega

/-! ## Classification: the obstruction is owned by Level II -/

/-- **The warrant is a determination claim.**  Definitionally, so no new owner
is created by naming it. -/
theorem warrant_is_a_determination (r₁ : S → M) (qM : M → A) (q : S → A) :
    Warrant r₁ qM q ↔ Determines (fun s => qM (r₁ s)) q := Iff.rfl

/-- **A failing warrant is a collision**, again for the pulled-back question.
A witness for the failure is exactly the `Collision` datum the existing owner
uses, so a claim-transport failure of this shape is filed under
`FactorisationCollision`. -/
def warrant_failure_is_a_collision {r₁ : S → M} {qM : M → A} {q : S → A}
    (w : Collision (fun s => qM (r₁ s)) q) : ¬ Warrant r₁ qM q :=
  fun h => w.separate (h w.left w.right w.collide)

/-- **A warrant forces the upstream stage to preserve the final question.**  The
downstream reading `qM` is applied *after* the upstream stage, so it can only
coarsen what that stage kept. -/
theorem warrant_forces_upstream {r₁ : S → M} {qM : M → A} {q : S → A}
    (w : Warrant r₁ qM q) : Determines r₁ q :=
  fun x y h => w x y (congrArg qM h)

/-- **Hence a first-stage collision rules out every warrant at once**: no choice
of downstream consumer question can license the composite. -/
theorem no_warrant_of_not_upstream {r₁ : S → M} {q : S → A} (h : ¬ Determines r₁ q)
    (qM : M → A) : ¬ Warrant r₁ qM q :=
  fun w => h (warrant_forces_upstream w)

/-- Conversely a warrant rules out every such collision. -/
theorem no_collision_of_warrant {r₁ : S → M} {qM : M → A} {q : S → A}
    (h : Warrant r₁ qM q) : IsEmpty (Collision (fun s => qM (r₁ s)) q) :=
  ⟨fun w => w.separate (h w.left w.right w.collide)⟩

/-! ## The equivalence-relation reading -/

/-- The equivalence a reading induces on states: `x ∼ y` when the reading cannot
tell them apart. -/
def sim {X Y : Type} (o : X → Y) (x y : X) : Prop := o x = o y

/-- **Determination is refinement of the induced equivalences.**  A reading
answers a question exactly when its equivalence is finer than the question's. -/
theorem determines_iff_sim_le {X Y Z : Type} (o : X → Y) (c : X → Z) :
    Determines o c ↔ ∀ x y, sim o x y → sim c x y := Iff.rfl

/-- **Consumer-relative equivalence, in the literal shape.**  Two states
identified by one consumer's reading and separated by another's.  This is the
reason local adequacy cannot be chained: the equivalence a stage preserves is
the equivalence of *its own* consumer. -/
theorem sim_not_transitive_across_consumers :
    ∃ (x y : ℕ) (c₁ c₂ : ℕ → ℕ), sim c₁ x y ∧ ¬ sim c₂ x y :=
  ⟨0, 2, fun n => n % 2, id, by simp only [sim], by simp only [sim, id]; omega⟩

/-! ## Negative claims do not compose either -/

/-- **A barrier at each of two boundaries is not a barrier across both.**  A
refutation is a claim too, and chaining refutations is invalid: here the first
reading fails to determine the second, the second fails to determine the third,
and the first determines the third outright.

Witness: parity, halving and parity again, on `ℕ`. -/
theorem barriers_do_not_compose :
    ∃ (r₁ q₁ q₂ : ℕ → ℕ),
      ¬ Determines r₁ q₁ ∧ ¬ Determines q₁ q₂ ∧ Determines r₁ q₂ := by
  refine ⟨fun n => n % 2, fun n => n / 2, fun n => n % 2, ?_, ?_, fun _ _ h => h⟩
  · intro h; have : (0 : ℕ) / 2 = 2 / 2 := h 0 2 rfl; omega
  · intro h; have : (0 : ℕ) % 2 = 1 % 2 := h 0 1 rfl; omega

/-- The valid direction: a barrier composes *forwards* along a refinement.  If
the first reading already fails for a question, then any reading it factors
through fails for it too. -/
theorem barrier_transports_upstream {r₁ : S → M} {r₂ : M → N} {q : S → A}
    (h : ¬ Determines r₁ q) : ¬ Determines (compose r₁ r₂) q :=
  fun hc => h (transport_forces_upstream hc)

/-! ## Three stages -/

/-- **Transport along a three-stage chain.**  One warrant per boundary. -/
theorem three_stage_transport {S M N P A : Type} {r₁ : S → M} {r₂ : M → N} {r₃ : N → P}
    {qN : N → A} {qM : M → A} {q : S → A}
    (h₃ : Determines r₃ qN) (w₂ : Determines (fun m => qN (r₂ m)) qM)
    (w₁ : Warrant r₁ qM q) :
    Determines (fun s => r₃ (r₂ (r₁ s))) q :=
  fun x y hxy => w₁ x y (w₂ _ _ (h₃ _ _ hxy))

/-- **And every warrant is load-bearing.**  Dropping the first boundary's
warrant already breaks the chain: here the last two stages are the identity and
their claims hold, but the first stage has destroyed the final question. -/
theorem three_stage_needs_every_warrant :
    ∃ (r₁ r₂ r₃ qN qM q : ℕ → ℕ),
      Determines r₃ qN ∧ Determines (fun m => qN (r₂ m)) qM ∧
        ¬ Determines (fun s => r₃ (r₂ (r₁ s))) q := by
  refine ⟨fun n => n % 2, id, id, id, id, id, fun _ _ h => h, fun _ _ h => h, ?_⟩
  intro h
  have : (0 : ℕ) = 2 := h 0 2 rfl
  omega

end Integration.ClaimTransport
