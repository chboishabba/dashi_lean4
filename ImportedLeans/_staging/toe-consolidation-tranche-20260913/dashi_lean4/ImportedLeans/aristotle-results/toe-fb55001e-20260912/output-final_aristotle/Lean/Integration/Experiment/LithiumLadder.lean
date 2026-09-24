import Mathlib
import Integration.Experiment.ModelLadder

/-!
# Stage 8 — a worked model ladder

`Integration.Experiment.ModelLadder` proves the *generic* facts about ladders
`M₀ ≺ M₁ ≺ ⋯`.  This file instantiates them on a four-rung ladder whose rungs
are labelled by the roadmap's cell-model story:

```
M₀ : charge bookkeeping             observable constant in time
M₁ : state-of-charge ODE            observable affine in time
M₂ : SOC + a thermal relaxation     affine plus one exponential mode
M₃ : SOC + thermal + a second mode  affine plus two exponential modes
```

**These are declared observational rungs, not physics.**  The label on a rung is
a comment; the Lean content is the set of time-series the rung can produce, and
no theorem in this file says that a lithium cell — or anything else — produces
any of them.  What the file demonstrates is the *reasoning over the ladder* that
the roadmap asks for, on a ladder that is genuinely nested and genuinely
four-deep.

## The question the ladder is used to answer

> does added model structure actually improve held-out prediction?

Here, concretely and provably:

* the step `M₀ ≺ M₁` **is earned**: two calibration readings refute `M₀`, `M₁`
  explains them, `M₁` forbids a value at the held-out time, and the held-out
  reading comes out as `M₁` predicted;
* the step `M₁ ≺ M₂` **is not earned** — and worse, it *destroys* the held-out
  prediction: on the same calibration data `M₂` forbids nothing whatsoever at
  the held-out time.

So on this ladder, one added state earns its place and the next one does not,
and the criterion that separates them is refutation plus a risked held-out
test — exactly the `EarnedRung` discipline.
-/

namespace Integration.Experiment.LithiumLadder

open Set
open Integration.Experiment.ParameterRegion (Reading)
open Integration.Experiment.ModelLadder

/-! ## §1 The four rungs -/

/-- `M₀` — charge bookkeeping: the observable does not move. -/
def bookkeeping : Rung where
  reach := {g | ∃ c : ℝ, g = fun _ => c}

/-- `M₁` — a state-of-charge ODE under a constant current: the observable is
affine in time. -/
def socRung : Rung where
  reach := {g | ∃ a b : ℝ, g = fun t => a * t + b}

/-- `M₂` — SOC together with one thermal relaxation mode. -/
noncomputable def socThermal : Rung where
  reach := {g | ∃ a b c : ℝ, g = fun t => a * t + b + c * Real.exp (-t)}

/-- `M₃` — SOC, thermal relaxation and a second (faster) mode. -/
noncomputable def socThermalTwo : Rung where
  reach := {g | ∃ a b c d : ℝ,
    g = fun t => a * t + b + c * Real.exp (-t) + d * Real.exp (-2 * t)}

/-- **The ladder is a chain.**  Each rung really does contain the one below it:
setting the new coefficient to zero recovers the previous rung. -/
theorem ladder_is_a_chain :
    Extends bookkeeping socRung ∧ Extends socRung socThermal ∧
      Extends socThermal socThermalTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, rfl⟩
    exact ⟨0, c, by funext t; simp⟩
  · rintro g ⟨a, b, rfl⟩
    exact ⟨a, b, 0, by funext t; simp⟩
  · rintro g ⟨a, b, c, rfl⟩
    exact ⟨a, b, c, 0, by funext t; simp⟩

theorem bookkeeping_le_socThermal : Extends bookkeeping socThermal :=
  extends_trans ladder_is_a_chain.1 ladder_is_a_chain.2.1

/-! ## §2 The calibration data and the held-out reading -/

/-- Two exact calibration readings: the observable is `0` at `t = 0` and `1` at
`t = 1`. -/
def calibration : List Reading := [⟨0, 0, 0, le_rfl⟩, ⟨1, 1, 0, le_rfl⟩]

/-- The held-out reading: `2` at `t = 2`. -/
def heldOut : Reading := ⟨2, 2, 0, le_rfl⟩

theorem fits_calibration_iff {g : ℝ → ℝ} :
    (∀ r ∈ calibration, FitsReading g r) ↔ g 0 = 0 ∧ g 1 = 1 := by
  constructor
  · intro h
    have h0 := h ⟨0, 0, 0, le_rfl⟩ (by simp [calibration])
    have h1 := h ⟨1, 1, 0, le_rfl⟩ (by simp [calibration])
    simp only [FitsReading, abs_nonpos_iff, sub_eq_zero] at h0 h1
    exact ⟨h0.symm, h1.symm⟩
  · rintro ⟨h0, h1⟩ r hr
    simp only [calibration, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [FitsReading, h0, h1]

/-! ## §3 `M₀` is refuted, `M₁` is earned -/

/-- **`M₀` cannot explain the calibration data.** -/
theorem bookkeeping_is_refuted : ¬ Explains bookkeeping calibration := by
  rintro ⟨g, ⟨c, rfl⟩, hfit⟩
  obtain ⟨h0, h1⟩ := fits_calibration_iff.1 hfit
  exact absurd (h0.symm.trans h1) (by norm_num)

/-- **`M₁` explains them, and uniquely**: the surviving series is the identity. -/
theorem socRung_survivors :
    survivors socRung calibration = {fun t : ℝ => t} := by
  ext g
  constructor
  · rintro ⟨⟨a, b, rfl⟩, hfit⟩
    obtain ⟨h0, h1⟩ := fits_calibration_iff.1 hfit
    have hb : b = 0 := by linarith [h0]
    have ha : a = 1 := by rw [hb] at h1; linarith
    subst ha; subst hb
    funext t; simp
  · rintro rfl
    refine ⟨⟨1, 0, by funext t; simp⟩, ?_⟩
    exact fits_calibration_iff.2 ⟨rfl, rfl⟩

theorem socRung_explains : Explains socRung calibration := by
  rw [Explains, socRung_survivors]
  exact ⟨_, rfl⟩

theorem socRung_envelope (t : ℝ) : envelopeAt socRung calibration t = {t} := by
  simp [envelopeAt, socRung_survivors]

/-- `M₁` stakes something at the held-out time. -/
theorem socRung_risks : RisksAt socRung calibration heldOut.time := by
  refine ⟨0, ?_⟩
  rw [show heldOut.time = (2 : ℝ) from rfl, socRung_envelope]
  norm_num

/-- And the held-out reading comes out as `M₁` predicted. -/
theorem socRung_predicts : Predicts socRung calibration heldOut := by
  intro g hg
  rw [socRung_survivors] at hg
  subst hg
  simp [FitsReading, heldOut]

/-- **The step `M₀ ≺ M₁` is earned.**  All four conditions of `EarnedRung` hold:
the lower rung is refuted, the higher rung explains the calibration data, it
forbids a value at the held-out time, and the held-out reading confirmed it. -/
theorem soc_step_is_earned : EarnedRung bookkeeping socRung calibration heldOut where
  extends' := ladder_is_a_chain.1
  lower_refuted := bookkeeping_is_refuted
  higher_explains := socRung_explains
  risked := socRung_risks
  survived := socRung_predicts

/-! ## §4 The next step is *not* earned, and costs the prediction -/

/-- **No step above `M₁` can be earned on this calibration data**, whatever the
held-out reading: `M₁` already explains it.  Climbing further would have to be
justified by *new* data that refute `M₁`. -/
theorem no_further_step_is_earned (M : Rung) (r : Reading) :
    ¬ EarnedRung socRung M calibration r :=
  earned_step_is_not_mere_extension socRung_explains

/-- `M₂` forbids **nothing** at the held-out time: its envelope there is all of
`ℝ`.  The extra thermal mode has exactly enough freedom to reach any value at
`t = 2` while still matching both calibration readings. -/
theorem socThermal_envelope_at_two :
    envelopeAt socThermal calibration 2 = univ := by
  have hE : Real.exp (-1) < 1 := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
    exact this
  have hne : (1 - Real.exp (-1)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  ext v
  simp only [mem_univ, iff_true]
  set c : ℝ := (v - 2) / (1 - Real.exp (-1)) ^ 2 with hc
  refine ⟨fun t => (1 + c - c * Real.exp (-1)) * t + (-c) + c * Real.exp (-t),
    ⟨⟨1 + c - c * Real.exp (-1), -c, c, rfl⟩, ?_⟩, ?_⟩
  · refine fits_calibration_iff.2 ⟨?_, ?_⟩
    · simp
    · simp; ring
  · have h2 : Real.exp (-(2 : ℝ)) = Real.exp (-1) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    show (1 + c - c * Real.exp (-1)) * 2 + -c + c * Real.exp (-(2:ℝ)) = v
    rw [h2]
    have : c * (1 - Real.exp (-1)) ^ 2 = v - 2 := by
      rw [hc]; exact div_mul_cancel₀ _ hne
    nlinarith [this]

/-- **Negative, on this ladder: added structure destroyed the held-out
prediction.**  `M₁` forbids `0` at `t = 2`; `M₂`, which extends it and explains
exactly the same calibration data, forbids nothing at all there. -/
theorem thermal_step_destroys_the_prediction :
    Extends socRung socThermal ∧
      RisksAt socRung calibration 2 ∧
      ¬ RisksAt socThermal calibration 2 := by
  refine ⟨ladder_is_a_chain.2.1, socRung_risks, ?_⟩
  rintro ⟨v, hv⟩
  exact hv (by rw [socThermal_envelope_at_two]; trivial)

/-- And the generic reason, instantiated: anything `M₂` predicts about held-out
data, `M₁` already predicted. -/
theorem thermal_adds_no_prediction (r : Reading)
    (h : Predicts socThermal calibration r) : Predicts socRung calibration r :=
  added_structure_never_adds_a_held_out_prediction ladder_is_a_chain.2.1 h

end Integration.Experiment.LithiumLadder
