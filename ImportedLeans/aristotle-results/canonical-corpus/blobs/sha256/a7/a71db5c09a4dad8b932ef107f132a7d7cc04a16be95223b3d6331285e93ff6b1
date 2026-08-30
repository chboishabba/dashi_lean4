import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 8 seed — model ladders and held-out prediction

The roadmap asks for a ladder of models

```
M₀ ≺ M₁ ≺ M₂ ≺ ⋯
```

read **not** as "more complex is better" but as *additional state, additional
assumptions, additional possible predictions* — and then asks the decisive
question:

```
does added model structure actually improve held-out prediction?
```

This file answers that question generically, and the answer is a negative that
is worth having.

A **rung** is abstracted to the only thing that matters for observation: the set
of time-series it can produce, `reach : Set (ℝ → ℝ)`.  A rung *extends* another
when its reach is larger — which is exactly what "adding state and parameters"
does to the set of achievable predictions.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `Rung`, `Extends`, `survivors`, `Explains`, `envelopeAt`, `Predicts`, `RisksAt` | definition | the ladder vocabulary |
| `survivors_mono`, `explains_mono` | theorem | a higher rung inherits every fit of a lower one |
| `refutation_travels_down` | theorem | refutation travels down the ladder, never up |
| `envelopeAt_mono` | theorem | held-out prediction envelopes only ever *widen* up the ladder |
| **`added_structure_never_adds_a_held_out_prediction`** | theorem (negative) | every held-out reading predicted by the higher rung was already predicted by the lower one |
| `richer_rung_risks_no_more` | theorem | and the higher rung forbids no more than the lower one |
| **`added_structure_can_destroy_the_held_out_prediction`** | theorem (negative) | a worked instance: constants vs. affine on one exact reading — the constant rung makes a sharp held-out prediction, the affine rung makes none at all |
| `EarnedRung`, `EarnedRung.could_have_failed` | definition / theorem | the only sound way up the ladder: the lower rung is *refuted* by the calibration data, the higher rung explains it **and** predicts a held-out reading it could have got wrong |
| `earned_step_is_not_mere_extension` | theorem | extension alone never earns a step |

## Claim boundary

`reach` is a declared set of functions; no theorem here says any physical system
is in any rung.  "Predicts" means *every* surviving member of the rung agrees
with the reading inside its declared tolerance — a possibility statement, not a
probability.  Nothing here ranks rungs by likelihood, information criteria, or
any other statistical score.
-/

namespace Integration.Experiment.ModelLadder

open Set
open Integration.Experiment.ParameterRegion (Reading)

/-! ## §1 Rungs -/

/-- **A rung of a model ladder**, abstracted to its observational content: the
set of time-series of the observable that the model can produce as its state,
parameters and assumptions range over everything the rung allows. -/
structure Rung where
  /-- The predicted time-series the rung can produce. -/
  reach : Set (ℝ → ℝ)

/-- `M ≺ M'`: the higher rung can produce everything the lower one can.  Adding
state, parameters or free functions to a model does exactly this. -/
def Extends (M M' : Rung) : Prop := M.reach ⊆ M'.reach

theorem extends_refl (M : Rung) : Extends M M := subset_rfl

theorem extends_trans {M M' M'' : Rung} (h : Extends M M') (h' : Extends M' M'') :
    Extends M M'' := h.trans h'

/-- A predicted series **fits** a reading when it lies inside the reading's
declared tolerance. -/
def FitsReading (g : ℝ → ℝ) (r : Reading) : Prop := |r.value - g r.time| ≤ r.tol

/-- The members of a rung that survive a body of evidence. -/
def survivors (M : Rung) (E : List Reading) : Set (ℝ → ℝ) :=
  {g | g ∈ M.reach ∧ ∀ r ∈ E, FitsReading g r}

/-- The rung **explains** the evidence when something in it survives. -/
def Explains (M : Rung) (E : List Reading) : Prop := (survivors M E).Nonempty

/-- The held-out **prediction envelope** of a rung at a time. -/
def envelopeAt (M : Rung) (E : List Reading) (t : ℝ) : Set ℝ :=
  (fun g => g t) '' survivors M E

/-- The rung **predicts** a held-out reading when *every* survivor of the
calibration data agrees with it. -/
def Predicts (M : Rung) (E : List Reading) (r : Reading) : Prop :=
  ∀ g ∈ survivors M E, FitsReading g r

/-- The rung **risks** something at a time when some value is outside its
held-out envelope: there is an observation it forbids. -/
def RisksAt (M : Rung) (E : List Reading) (t : ℝ) : Prop :=
  ∃ v : ℝ, v ∉ envelopeAt M E t

/-! ## §2 What going up the ladder does, and does not, buy -/

theorem survivors_mono {M M' : Rung} (h : Extends M M') (E : List Reading) :
    survivors M E ⊆ survivors M' E :=
  fun _ hg => ⟨h hg.1, hg.2⟩

/-- A higher rung inherits every fit of a lower one. -/
theorem explains_mono {M M' : Rung} (h : Extends M M') {E : List Reading}
    (hE : Explains M E) : Explains M' E :=
  hE.mono (survivors_mono h E)

/-- **Refutation travels down the ladder, never up.**  Data that refute a higher
rung refute every rung below it; data that a lower rung explains can never
refute a higher one. -/
theorem refutation_travels_down {M M' : Rung} (h : Extends M M')
    {E : List Reading} (hE : ¬ Explains M' E) : ¬ Explains M E :=
  fun hM => hE (explains_mono h hM)

/-- **Held-out envelopes only widen up the ladder.** -/
theorem envelopeAt_mono {M M' : Rung} (h : Extends M M') (E : List Reading) (t : ℝ) :
    envelopeAt M E t ⊆ envelopeAt M' E t :=
  image_mono (survivors_mono h E)

/-- **Negative: added model structure never adds a held-out prediction.**
Whatever the higher rung predicts about held-out data after calibration, the
lower rung already predicted.  Improvement in prediction can therefore never
come from enlarging the reach alone — it can only come from the lower rung being
*refuted*. -/
theorem added_structure_never_adds_a_held_out_prediction {M M' : Rung} (h : Extends M M')
    {E : List Reading} {r : Reading} (hr : Predicts M' E r) : Predicts M E r :=
  fun g hg => hr g (survivors_mono h E hg)

/-- Correspondingly, a higher rung forbids no more than a lower one. -/
theorem richer_rung_risks_no_more {M M' : Rung} (h : Extends M M') {E : List Reading} {t : ℝ}
    (hM' : RisksAt M' E t) : RisksAt M E t := by
  obtain ⟨v, hv⟩ := hM'
  exact ⟨v, fun hmem => hv (envelopeAt_mono h E t hmem)⟩

/-! ## §3 A worked instance: constants versus affine -/

/-- `M₀`: the observable is constant. -/
def constRung : Rung where
  reach := {g | ∃ c : ℝ, g = fun _ => c}

/-- `M₁`: the observable is affine in time — one extra parameter. -/
def affineRung : Rung where
  reach := {g | ∃ a b : ℝ, g = fun t => a * t + b}

theorem const_extends_affine : Extends constRung affineRung := by
  rintro g ⟨c, rfl⟩
  exact ⟨0, c, by funext t; simp⟩

/-- One exact reading: the observable was `1` at time `0`. -/
def oneExactReading : List Reading := [⟨0, 1, 0, le_rfl⟩]

theorem constRung_survivors :
    survivors constRung oneExactReading = {fun _ => (1 : ℝ)} := by
  ext g
  constructor
  · rintro ⟨⟨c, rfl⟩, hfit⟩
    have := hfit ⟨0, 1, 0, le_rfl⟩ (by simp [oneExactReading])
    simp only [FitsReading, abs_nonpos_iff, sub_eq_zero] at this
    simp [this]
  · rintro rfl
    refine ⟨⟨1, rfl⟩, ?_⟩
    intro r hr
    simp only [oneExactReading, List.mem_singleton] at hr
    subst hr
    simp [FitsReading]

/-- The constant rung makes a **sharp** held-out prediction at every time. -/
theorem constRung_envelope (t : ℝ) :
    envelopeAt constRung oneExactReading t = {1} := by
  simp [envelopeAt, constRung_survivors]

/-- The affine rung makes **no** held-out prediction away from the calibration
time: its envelope is everything. -/
theorem affineRung_envelope {t : ℝ} (ht : t ≠ 0) :
    envelopeAt affineRung oneExactReading t = univ := by
  ext v
  simp only [mem_univ, iff_true]
  refine ⟨fun s => ((v - 1) / t) * s + 1, ⟨⟨(v - 1) / t, 1, rfl⟩, ?_⟩, ?_⟩
  · intro r hr
    simp only [oneExactReading, List.mem_singleton] at hr
    subst hr
    simp [FitsReading]
  · field_simp
    ring

/-- **Negative: added model structure can destroy the held-out prediction.**
With one exact calibration reading, the constant rung forbids the value `0` at
time `2` while the affine rung — which extends it — forbids nothing at all
there.  Going up the ladder made the model *less* testable on held-out data,
not more accurate on it. -/
theorem added_structure_can_destroy_the_held_out_prediction :
    Extends constRung affineRung ∧
      RisksAt constRung oneExactReading 2 ∧
      ¬ RisksAt affineRung oneExactReading 2 := by
  refine ⟨const_extends_affine, ⟨0, ?_⟩, ?_⟩
  · rw [constRung_envelope]
    simp
  · rintro ⟨v, hv⟩
    exact hv (by rw [affineRung_envelope (by norm_num)]; trivial)

/-! ## §4 Earning a step up the ladder -/

/-- **An earned step up the ladder.**  Mirroring the novelty constraint on
repairs (`Integration.Experiment.RepairSearch`), a higher rung is promoted only
when all four conditions hold: the lower rung is refuted by the calibration
data, the higher rung explains them, the higher rung *risks* something at the
held-out time, and the held-out reading is nevertheless predicted. -/
structure EarnedRung (M M' : Rung) (E : List Reading) (held : Reading) : Prop where
  /-- The higher rung really is higher. -/
  extends' : Extends M M'
  /-- The lower rung fails on the calibration data. -/
  lower_refuted : ¬ Explains M E
  /-- The higher rung fits them. -/
  higher_explains : Explains M' E
  /-- The higher rung forbids some outcome at the held-out time: the test was
  a real one. -/
  risked : RisksAt M' E held.time
  /-- And the held-out reading came out as predicted. -/
  survived : Predicts M' E held

/-- An earned step was a genuine test: the higher rung forbade some value at the
held-out time. -/
theorem EarnedRung.could_have_failed {M M' : Rung} {E : List Reading} {held : Reading}
    (h : EarnedRung M M' E held) : ∃ v : ℝ, v ∉ envelopeAt M' E held.time := h.risked

/-- **Extension alone never earns a step.**  If the lower rung already explains
the calibration data, no extension of it can be earned, however much held-out
data it goes on to predict.  This is the ladder-level form of
`fitRestored ≠ supported`. -/
theorem earned_step_is_not_mere_extension {M M' : Rung} {E : List Reading} {held : Reading}
    (hE : Explains M E) : ¬ EarnedRung M M' E held :=
  fun h => h.lower_refuted hE

/-- And an earned step really does improve matters on the calibration data:
the lower rung is refuted there while the higher one is not. -/
theorem earned_step_separates_on_calibration {M M' : Rung} {E : List Reading} {held : Reading}
    (h : EarnedRung M M' E held) : ¬ Explains M E ∧ Explains M' E :=
  ⟨h.lower_refuted, h.higher_explains⟩

end Integration.Experiment.ModelLadder
