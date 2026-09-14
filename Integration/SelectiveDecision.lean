import Integration.CoordinateSufficiency

/-!
# Selective decisions: three-way verdicts with abstention

Several lanes of the corpus reach the same situation independently: a rule does
not merely accept or reject, it may also decline to decide, and the declination
is then *compiled away* into some concrete action.  The domain vocabulary is
different every time — abstain/hold in a control lane, suspend/refine in an
epistemic one, a severity band in a monitoring one — but the mathematics is one
object: a three-valued verdict, a resolution map into an action type, and the
question of what the resolution destroys.

This file owns that object, and then consumes the corpus surface that already
has an executable instance of it,
`Agda/DASHI/Control/LearnedAbstentionBoundary.agda`.

## Contents

### The generic owner

* `Verdict` — reject / abstain / accept;
* `Resolution`, `resolve` — compiling a verdict into an action, abstention going
  to a designated default;
* `resolve_not_injective_of_default_collision` and
  `verdict_not_determined_of_default_collision` — **the generic cost**: as soon
  as the default action coincides with a determinate one, the executed action no
  longer determines the verdict.  Abstention is invisible downstream;
* `abstention_is_reachable_iff` — for a rule gated by two thresholds, the
  abstention region is non-empty exactly when the thresholds leave a gap.  A
  three-way rule whose thresholds are adjacent is a two-way rule.

### The corpus instance

Mirror of the Agda module's `Direction`, `Action`, `Decision` and
`compileDecision`, with the three lemmas it proves re-proved
(`abstention_compiles_to_hold`, `neutral_does_not_flatten`,
`hold_preserves_exposure`, `abstention_preserves_exposure`), and then the
content the module does *not* state:

* `compile_never_flattens` — `flatten` is not in the image of `compileDecision`
  at all, so the risk directive is genuinely a second channel and not the third
  value of the directional carrier;
* `action_does_not_determine_direction` — the compiled action does not determine
  the belief;
* `direction_essential_only_when_not_abstaining` — **the interesting one**: the
  direction coordinate is essential to the action when the abstain flag is
  `false` and inessential when it is `true`.  Coordinate essentiality here is
  itself context-dependent, which is exactly the shape
  `Integration.ContextIndexedRole` owns;
* `exposure_does_not_determine_abstention` — and downstream of execution the
  abstention is unrecoverable from the exposure trajectory.

### The corpus threshold pair

`Agda/DASHI/Physics/SeverityMapping.agda` declares `safeThresholdᵣ = 3` and
`brokenThresholdᵣ = 4`.  `corpus_thresholds_admit_no_abstention` records the
consequence: with those two numbers the gated rule *never* abstains, so the lane
has a two-valued decision written in three-valued vocabulary.  `clamp9` is
separately non-injective (`clamp9_collides`), which is an ordinary aggregation
collision in the sense of `Integration.CoordinateSufficiency`.

Nothing here is a claim about trading, control, monitoring or physics.  The
carriers are three- and four-element label types and `ℕ`.
-/

namespace Integration.SelectiveDecision

open Integration.CoordinateSufficiency

/-! ## The generic three-way verdict -/

/-- A decision that may decline to decide. -/
inductive Verdict
  /-- The negative determinate verdict. -/
  | reject
  /-- Declining to decide. -/
  | abstain
  /-- The positive determinate verdict. -/
  | accept
  deriving DecidableEq, Repr, Fintype

/-- How a verdict is compiled into an action: the two determinate verdicts get
their own actions, and abstention is resolved to a designated default. -/
structure Resolution (Act : Type) where
  /-- The action taken on a reject verdict. -/
  onReject : Act
  /-- The action taken on an accept verdict. -/
  onAccept : Act
  /-- The action taken when the rule abstains. -/
  onAbstain : Act

/-- Compiling a verdict. -/
def resolve {Act : Type} (R : Resolution Act) : Verdict → Act
  | .reject => R.onReject
  | .abstain => R.onAbstain
  | .accept => R.onAccept

/-- **The generic cost of abstention.**  If the default action is one of the
determinate actions, the resolution is not injective. -/
theorem resolve_not_injective_of_default_collision {Act : Type} (R : Resolution Act)
    (h : R.onAbstain = R.onReject) : ¬ Function.Injective (resolve R) := by
  intro hinj
  exact absurd (hinj (show resolve R .abstain = resolve R .reject from h)) (by decide)

/-- The same statement in the vocabulary of the observation owner: the executed
action does not determine the verdict that produced it. -/
theorem verdict_not_determined_of_default_collision {Act : Type} (R : Resolution Act)
    (h : R.onAbstain = R.onReject) : ¬ Determines (resolve R) (fun v : Verdict => v) :=
  not_determines_of_collision (O := resolve R) (C := fun v : Verdict => v)
    (x₁ := .abstain) (x₂ := .reject) h (by decide)

/-! ## A rule gated by two thresholds -/

/-- Accept below the safe threshold, reject at or above the broken threshold,
abstain in between. -/
def gated (safe broken s : ℕ) : Verdict :=
  if s ≤ safe then .accept else if broken ≤ s then .reject else .abstain

/-- **The abstention region is non-empty exactly when the thresholds leave a
gap.**  A three-valued rule whose thresholds are adjacent is a two-valued
rule. -/
theorem abstention_is_reachable_iff (safe broken : ℕ) :
    (∃ s, gated safe broken s = .abstain) ↔ safe + 1 < broken := by
  constructor
  · rintro ⟨s, hs⟩
    unfold gated at hs
    by_cases h1 : s ≤ safe
    · rw [if_pos h1] at hs; exact absurd hs (by decide)
    · rw [if_neg h1] at hs
      by_cases h2 : broken ≤ s
      · rw [if_pos h2] at hs; exact absurd hs (by decide)
      · omega
  · intro h
    refine ⟨safe + 1, ?_⟩
    unfold gated
    rw [if_neg (by omega), if_neg (by omega)]

/-- The two threshold constants declared in `DASHI/Physics/SeverityMapping.agda`. -/
def corpusSafeThreshold : ℕ := 3

/-- The broken threshold declared in the same module. -/
def corpusBrokenThreshold : ℕ := 4

/-- **The corpus's own thresholds admit no abstention.**  With safe `3` and
broken `4` there is no severity at which the gated rule declines: the lane's
three-valued vocabulary carries a two-valued rule. -/
theorem corpus_thresholds_admit_no_abstention :
    ¬ ∃ s, gated corpusSafeThreshold corpusBrokenThreshold s = .abstain := by
  rw [abstention_is_reachable_iff]
  decide

/-- Widening the broken threshold restores it. -/
theorem widened_thresholds_admit_abstention :
    ∃ s, gated corpusSafeThreshold 6 s = .abstain := by
  rw [abstention_is_reachable_iff]
  decide

/-- The severity clamp of the same Agda module. -/
def clamp9 (n : ℕ) : ℕ := min n 9

/-- **The clamp is an aggregation collision.**  Every severity of nine or more
reports the same value, so no downstream rule reads a defect magnitude off the
clamped code. -/
theorem clamp9_collides : clamp9 9 = clamp9 12 ∧ (9 : ℕ) ≠ 12 := by
  constructor
  · decide
  · decide

/-- Hence the clamped code does not determine the severity. -/
theorem clamp9_not_determines : ¬ Determines clamp9 (fun n : ℕ => n) :=
  not_determines_of_collision clamp9_collides.1 clamp9_collides.2

/-! ## The corpus instance: `DASHI.Control.LearnedAbstentionBoundary` -/

/-- Mirror of the Agda `Direction`. -/
inductive Direction
  /-- The negative direction. -/
  | down
  /-- The indifferent direction. -/
  | neutral
  /-- The positive direction. -/
  | up
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `Action`. -/
inductive Action
  /-- Act in the negative direction. -/
  | sell
  /-- Do nothing. -/
  | hold
  /-- Act in the positive direction. -/
  | buy
  /-- Close the exposure. -/
  | flatten
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `Decision`: a direction together with an abstain flag. -/
structure Decision where
  /-- The believed direction. -/
  direction : Direction
  /-- Whether the rule declines to act on it. -/
  abstain : Bool
  deriving DecidableEq, Repr

/-- Mirror of the Agda `compileDecision`. -/
def compileDecision : Decision → Action
  | ⟨_, true⟩ => .hold
  | ⟨.down, false⟩ => .sell
  | ⟨.neutral, false⟩ => .hold
  | ⟨.up, false⟩ => .buy

/-- The Agda `abstentionCompilesToHold`, re-proved. -/
theorem abstention_compiles_to_hold (d : Direction) :
    compileDecision ⟨d, true⟩ = .hold := by cases d <;> rfl

/-- The Agda `neutralDoesNotFlatten`, re-proved. -/
theorem neutral_does_not_flatten : compileDecision ⟨.neutral, false⟩ = .hold := rfl

/-- **`flatten` is not in the image of `compileDecision`.**  The Agda module
says in prose that closing exposure "cannot be produced by `compileDecision`";
this is the statement, proved.  So the risk directive is a genuinely separate
channel and not a fourth verdict. -/
theorem compile_never_flattens (d : Decision) : compileDecision d ≠ .flatten := by
  obtain ⟨dir, ab⟩ := d
  cases ab <;> cases dir <;> decide

/-- **The compiled action does not determine the belief.**  Abstaining on a
down belief and abstaining on an up belief are the same action. -/
theorem action_does_not_determine_direction :
    ¬ Determines compileDecision Decision.direction :=
  not_determines_of_collision (x₁ := ⟨.down, true⟩) (x₂ := ⟨.up, true⟩) rfl (by decide)

/-- Nor the abstain flag: a neutral belief acted on and a neutral belief
abstained from compile to the same action. -/
theorem action_does_not_determine_abstention :
    ¬ Determines compileDecision Decision.abstain :=
  not_determines_of_collision (x₁ := ⟨.neutral, false⟩) (x₂ := ⟨.neutral, true⟩) rfl
    (by decide)

/-- **Essentiality of the direction coordinate is itself context-dependent.**
With the abstain flag `false` the direction separates the action; with it `true`
it does not.  So "this coordinate matters" is not a property of the coordinate
alone — it is a property of the coordinate *at a context*, which is the shape
`Integration.ContextIndexedRole` owns. -/
theorem direction_essential_only_when_not_abstaining :
    compileDecision ⟨.down, false⟩ ≠ compileDecision ⟨.up, false⟩ ∧
      compileDecision ⟨.down, true⟩ = compileDecision ⟨.up, true⟩ :=
  ⟨by decide, rfl⟩

/-- The abstain coordinate, by contrast, is essential at the down context. -/
theorem abstain_essential_at_down :
    compileDecision ⟨.down, false⟩ ≠ compileDecision ⟨.down, true⟩ := by decide

/-- Mirror of the Agda `ExecutionSemantics`. -/
structure ExecutionSemantics (Exposure : Type) where
  /-- The effect of selling. -/
  applySell : Exposure → Exposure
  /-- The effect of buying. -/
  applyBuy : Exposure → Exposure
  /-- The flat exposure. -/
  flatExposure : Exposure

/-- Mirror of the Agda `execute`. -/
def execute {Exposure : Type} (E : ExecutionSemantics Exposure) : Action → Exposure → Exposure
  | .sell, x => E.applySell x
  | .hold, x => x
  | .buy, x => E.applyBuy x
  | .flatten, _ => E.flatExposure

/-- The Agda `holdPreservesExposure`, re-proved. -/
theorem hold_preserves_exposure {Exposure : Type} (E : ExecutionSemantics Exposure)
    (x : Exposure) : execute E .hold x = x := rfl

/-- The Agda `abstentionPreservesExposure`, re-proved. -/
theorem abstention_preserves_exposure {Exposure : Type} (E : ExecutionSemantics Exposure)
    (d : Direction) (x : Exposure) : execute E (compileDecision ⟨d, true⟩) x = x := by
  cases d <;> rfl

/-- **Execution erases abstention.**  Because abstention is observationally the
identity, no exposure trajectory distinguishes "believed nothing" from "believed
something and declined": for every execution semantics and every state, the two
decisions leave the same exposure. -/
theorem exposure_does_not_determine_abstention {Exposure : Type}
    (E : ExecutionSemantics Exposure) (x : Exposure) :
    execute E (compileDecision ⟨.neutral, false⟩) x
      = execute E (compileDecision ⟨.up, true⟩) x := rfl

/-- Assembled as an instance of the generic owner: the corpus's compilation is
the resolution whose abstention default is `hold`, which is also the action of a
determinate verdict.  So the generic non-injectivity theorem applies to it. -/
def corpusResolution : Resolution Action where
  onReject := .sell
  onAccept := .buy
  onAbstain := .hold

/-- The corpus's own resolution is the one whose default collides — with the
`neutral` verdict rather than with `reject`, which is why the collision is
stated directly here rather than by instantiating
`resolve_not_injective_of_default_collision`. -/
theorem corpus_resolution_faithful (d : Direction) :
    resolve corpusResolution (match d with
      | .down => .reject | .neutral => .abstain | .up => .accept)
      = compileDecision ⟨d, false⟩ ∨ d = .neutral := by
  cases d
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

end Integration.SelectiveDecision
