import Integration.Experiment.Protocol

/-!
# Lane 4 — risk as a consumer of the prediction, not a parallel system

Risk in this calculus is a *consumer* `R : State → RiskProfile` of exactly the
same state model the prediction lane uses.  Nothing about risk is computed from
a separate object, and the file proves that:

* `risk_envelope_is_the_image_of_the_fibre` — the risk envelope is the image,
  under the risk map, of the *same fibre* that carries the prediction envelope;
* `risk_inherits_determination` — whatever the instruments determine about the
  state, they determine about the risk derived from it.

## The operational theorem

```
O x = O y  ∧  R x ≠ R y   ⟹   current instrumentation is insufficient
                              for the risk question
```

is `instrumentation_insufficient_for_the_risk_question`: it is the existing
`Collision` owner applied to the risk consumer, so its conclusion is the strong
one — *no* reading of the instruments, and no post-processing of them, answers
the risk question.  `Verdict` packages the two outcomes as a datum that cannot
be inhabited both ways (`verdict_is_exclusive`).

Nothing here asserts that any physical system is safe or unsafe.  A `Hazard` is
a rational-valued function of an abstract state together with a rational
threshold.
-/

namespace Integration.Experiment.Risk

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PredictionEnvelope

variable {State Y Z : Type}

/-! ## §1 Hazards and risk profiles -/

/-- A hazard: a named quantity of the state and the threshold beyond which the
hazard is declared. -/
structure Hazard (State : Type) where
  /-- A label for the hazard. -/
  name : String
  /-- The state quantity being thresholded. -/
  quantity : State → ℚ
  /-- The threshold. -/
  threshold : ℚ

/-- Whether the hazard is exceeded in a state. -/
def Hazard.exceeded (h : Hazard State) (x : State) : Bool := decide (h.threshold < h.quantity x)

/-- The risk profile of a state under a declared list of hazards: one flag per
hazard, in order. -/
def profile (hs : List (Hazard State)) (x : State) : List Bool := hs.map (fun h => h.exceeded x)

/-- The profile has one entry per declared hazard. -/
theorem profile_length (hs : List (Hazard State)) (x : State) :
    (profile hs x).length = hs.length := by simp [profile]

/-! ## §2 Risk sits downstream of the prediction -/

/-- **The risk envelope is the image of the prediction fibre.**  It is computed
from the same set of states the prediction envelope is computed from, so risk
cannot drift away from the model that produces the prediction. -/
theorem risk_envelope_is_the_image_of_the_fibre (O : State → Y) (R : State → Z) (y : Y) :
    Pred O R y = R '' {x | O x = y} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- **Risk inherits determination.**  If the instruments determine the state
quantity a risk map reads, they determine the risk. -/
theorem risk_inherits_determination {W : Type} (O : State → Y) (C : State → Z) (g : Z → W)
    (h : Determines O C) : Determines O (fun x => g (C x)) :=
  fun x y hxy => congrArg g (h x y hxy)

/-- In particular a threshold risk is determined whenever its underlying
quantity is. -/
theorem threshold_risk_determined_of_quantity (O : State → Y) (h : Hazard State)
    (hq : Determines O h.quantity) : Determines O h.exceeded :=
  risk_inherits_determination O h.quantity (fun q => decide (h.threshold < q)) hq

/-- **And the converse fails**, which is why risk is worth asking about
separately: a coarse instrument can settle the risk question without settling
the quantity.  Here the sign of a value decides a zero-threshold hazard while
leaving the value itself wide open. -/
theorem threshold_risk_can_be_determined_without_the_quantity :
    ∃ (O : ℚ → Bool) (h : Hazard ℚ),
      Determines O h.exceeded ∧ ¬ Determines O h.quantity := by
  refine ⟨fun q => decide (0 < q), ⟨"positive", id, 0⟩, ?_, ?_⟩
  · intro x y hxy
    simpa [Hazard.exceeded] using hxy
  · intro hdet
    have : (1 : ℚ) = 2 := hdet 1 2 (by norm_num)
    norm_num at this

/-! ## §3 The instrumentation verdict -/

/-- **The operational theorem.**  Two states the instruments cannot tell apart
whose risk differs: the instrumentation is insufficient for the risk question,
and the insufficiency is structural — no reading of the instruments answers
it. -/
theorem instrumentation_insufficient_for_the_risk_question
    {O : State → Y} {R : State → Z} {x y : State}
    (hne : x ≠ y) (hobs : O x = O y) (hrisk : R x ≠ R y) :
    ¬ Determines O R ∧ ∀ f : Y → Z, ¬ ∀ s, R s = f (O s) :=
  let w : Collision O R := ⟨x, y, hne, hobs, hrisk⟩
  ⟨w.not_determines, fun f => w.no_reading f⟩

/-- The verdict on a set of instruments, relative to a risk question. -/
inductive Verdict (O : State → Y) (R : State → Z)
  /-- The instruments answer the risk question. -/
  | sufficient (h : Determines O R)
  /-- They do not, and here is the pair they confuse. -/
  | insufficient (w : Collision O R)

/-- **The verdict is exclusive**: the two constructors cannot both be
inhabited, so "sufficient for the risk question" is a genuine dichotomy and not
a matter of presentation. -/
theorem verdict_is_exclusive {O : State → Y} {R : State → Z}
    (h : Determines O R) (w : Collision O R) : False := w.not_determines h

/-- **The verdict is relative to the question.**  The same instruments are
sufficient for one hazard and insufficient for another, so a risk claim must
name its hazard list. -/
theorem verdict_depends_on_the_hazard :
    ∃ (O : ℚ × ℚ → ℚ) (h₁ h₂ : Hazard (ℚ × ℚ)),
      Determines O h₁.exceeded ∧ ¬ Determines O h₂.exceeded := by
  refine ⟨fun p => p.1, ⟨"first", fun p => p.1, 0⟩, ⟨"second", fun p => p.2, 0⟩, ?_, ?_⟩
  · intro x y hxy
    have hx : x.1 = y.1 := hxy
    simp [Hazard.exceeded, hx]
  · intro hdet
    have := hdet (0, 1) (0, -1) rfl
    simp [Hazard.exceeded] at this
    norm_num at this

/-- **Risk observability, stated as envelope width.**  The instruments answer
the risk question exactly when every risk envelope is a single profile: the
same criterion the prediction lane uses, applied to the risk consumer. -/
theorem risk_observable_iff_envelope_subsingleton (O : State → Y) (R : State → Z) :
    Determines O R ↔ ∀ y, (Pred O R y).Subsingleton :=
  determines_iff_envelope_subsingleton O R

end Integration.Experiment.Risk
