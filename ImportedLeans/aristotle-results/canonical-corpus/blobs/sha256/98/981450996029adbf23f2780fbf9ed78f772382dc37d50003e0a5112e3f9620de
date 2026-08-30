import Mathlib
import Integration.Experiment.RepairObligations

/-!
# Stage 7, lane 6 — repair search constrained by novelty

`TOE_STAGE6_INFERENCE.md` frontier item 8 records the gap closed here:

> **Repairs are gated but not searched.**  No enumeration, no cost, no proposal
> generator; `RepairProposal` must be constructed by hand.

Stage 6 stopped patch generators from being *unrestricted*: a repair must name a
class and stay refutable.  That is still not enough to earn scientific support,
because a repair constructed **from** a dataset explains that dataset by
construction.  The rule this file enforces is

```
a repair must make a new prediction that was not used to construct it,
and that prediction must survive.
```

So the workflow is

```
refutation → repair proposal → held-out prediction → promotion or rejection
```

and `fitRestored` and `supported` are kept apart by proof.

## The objects

* `Forbids F D r` — having fitted `D`, the family rules the reading `r` out;
* `RisksSomethingAt F D t` — some value at time `t` is forbidden: the family
  sticks its neck out there;
* `ValidatedRepair` — a repair proposal *plus* a held-out reading at a time not
  in the construction data, a proof that the repair risked something there, and
  a proof that the held-out reading was survived;
* `RepairStatus` — `fitRestored` and `supported`, provably distinct.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `forbids_of_not_fits`, `forbidden_reading_falsifies` | theorem | a forbidden reading really would have destroyed the repair |
| **`validated_repair_could_have_failed`** | theorem | every validated repair had a dataset that would have falsified it: the promotion is not free |
| `validated_repair_restores_fit`, `validated_repair_survives_the_held_out_reading` | theorem | the two halves of the promotion |
| **`freeFamily_risks_nothing`**, **`no_validated_repair_from_the_free_family`** | negative | the unrestricted patch generator can never be promoted, at any held-out time |
| **`fit_and_refutability_do_not_give_a_held_out_prediction`** | negative | even a *refutable* repair that fits perfectly can be blind at the held-out time — `fitRestored ⇏ supported` is not a convention but a theorem |
| `offsetValidated`, `offset_repair_is_promoted` | definition/theorem | the worked promotion: the measurement-model repair of Stage 6 predicts `y(3) = 5` before that reading is taken, and survives it |
| `exists_cheapest_validated_repair` | theorem | the search step: among finitely many validated repairs a cost-minimal one exists |
| `cheapest_is_still_validated` | theorem | and selection by cost cannot smuggle in an unvalidated repair |

## Claim boundary

"Survives" means the held-out reading leaves the surviving region nonempty under
declared tolerances.  Nothing here estimates a cost, proposes a repair
automatically, or claims that a promoted repair is true.
-/

namespace Integration.Experiment.RepairSearch

open Set
open Integration.Experiment.ParameterRegion
open Integration.Experiment.RepairObligations

variable {Θ : Type*}

/-! ## §1 Risking something -/

/-- **The family, having fitted `D`, forbids the reading `r`**: no surviving
parameter can accommodate it. -/
def Forbids (F : ParamFamily Θ) (D : List Reading) (r : Reading) : Prop :=
  ∀ θ ∈ Compatible F D, ¬ Fits F θ r

/-- **The family risks something at time `t`**: some value there is forbidden.
A family that risks nothing at a time can never be supported by a measurement at
that time. -/
def RisksSomethingAt (F : ParamFamily Θ) (D : List Reading) (t : ℝ) : Prop :=
  ∃ y : ℝ, ∀ θ ∈ Compatible F D, F.predict θ t ≠ y

/-- An exact reading of a forbidden value. -/
def sharpReading (t y : ℝ) : Reading := ⟨t, y, 0, le_refl 0⟩

@[simp] theorem sharpReading_time (t y : ℝ) : (sharpReading t y).time = t := rfl
@[simp] theorem sharpReading_value (t y : ℝ) : (sharpReading t y).value = y := rfl
@[simp] theorem sharpReading_tol (t y : ℝ) : (sharpReading t y).tol = 0 := rfl

/-- Risking a value at `t` gives an exact reading the family forbids. -/
theorem forbids_of_not_fits {F : ParamFamily Θ} {D : List Reading} {t : ℝ}
    (h : RisksSomethingAt F D t) :
    ∃ y, Forbids F D (sharpReading t y) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y, fun θ hθ hfits => ?_⟩
  have : |y - F.predict θ t| ≤ 0 := hfits
  have h0 : y - F.predict θ t = 0 := abs_nonpos_iff.mp this
  exact hy θ hθ (by linarith)

/-- **A forbidden reading would have falsified the repair.**  This is what makes
a held-out prediction a genuine test rather than a description. -/
theorem forbidden_reading_falsifies {F : ParamFamily Θ} {D : List Reading} {r : Reading}
    (h : Forbids F D r) : Compatible F (r :: D) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro θ ⟨hp, hf⟩
  refine h θ ⟨hp, fun r' hr' => hf r' (List.mem_cons_of_mem _ hr')⟩ ?_
  exact hf r (List.mem_cons_self ..)

/-! ## §2 A validated repair -/

/-- **A validated repair.**  Everything a `RepairProposal` demands, plus:

* a held-out reading whose time is *not* among the construction data;
* a proof that the repair, fitted to the construction data alone, already
  forbade some outcome at that time;
* a proof that the held-out reading is nevertheless survived.

The third field is what a repair *earns*; the second is what makes earning it
possible; the first is what stops the repair from being fitted to the very data
that is supposed to test it. -/
structure ValidatedRepair (Θ : Type*) where
  /-- Which missing capability the repair supplies. -/
  klass : RepairClass
  /-- The repaired family. -/
  family : ParamFamily Θ
  /-- The data the original family failed on, used to construct the repair. -/
  data : List Reading
  /-- The repair restores fit to the construction data. -/
  restoresFit : (Compatible family data).Nonempty
  /-- The repair remains refutable in principle. -/
  isRefutable : Refutable family
  /-- A reading taken after the repair was fixed. -/
  heldOut : Reading
  /-- Its time was not used in the construction. -/
  notUsed : ∀ r ∈ data, r.time ≠ heldOut.time
  /-- **The novelty condition**: the repair forbade some outcome there. -/
  risked : RisksSomethingAt family data heldOut.time
  /-- **The test passed**: the held-out reading is survived. -/
  confirmed : (Compatible family (heldOut :: data)).Nonempty

namespace ValidatedRepair

variable (v : ValidatedRepair Θ)

/-- A validated repair fits the data it was built from. -/
theorem restores_fit : (Compatible v.family v.data).Nonempty := v.restoresFit

/-- And it fits the data it was tested on. -/
theorem survives_the_held_out_reading :
    (Compatible v.family (v.heldOut :: v.data)).Nonempty := v.confirmed

/-- **The promotion was not free.**  There is a reading at the held-out time
which, had it occurred, would have left the repaired family with no surviving
parameter at all. -/
theorem could_have_failed :
    ∃ y : ℝ, Compatible v.family (sharpReading v.heldOut.time y :: v.data) = ∅ := by
  obtain ⟨y, hy⟩ := forbids_of_not_fits v.risked
  exact ⟨y, forbidden_reading_falsifies hy⟩

end ValidatedRepair

/-! ## §3 The two statuses are distinct -/

/-- The status a repair can hold. -/
inductive RepairStatus
  /-- The repair explains the data it was built from. -/
  | fitRestored
  /-- The repair additionally survived a prediction it was not built from. -/
  | supported
  deriving DecidableEq, Repr

/-- The statuses are not the same thing. -/
theorem fitRestored_ne_supported : RepairStatus.fitRestored ≠ RepairStatus.supported := by decide

/-- A bare proposal has the weaker status. -/
def statusOf (_ : RepairProposal Θ) : RepairStatus := RepairStatus.fitRestored

/-- A validated repair has the stronger one. -/
def statusOfValidated (_ : ValidatedRepair Θ) : RepairStatus := RepairStatus.supported

/-! ## §4 The unrestricted repair can never be promoted -/

/-- **The unrestricted patch generator risks nothing**, at any time it has not
already measured: every value there is still attainable. -/
theorem freeFamily_risks_nothing {D : List Reading} (hD : Functional D) {t : ℝ}
    (ht : ∀ r ∈ D, r.time ≠ t) : ¬ RisksSomethingAt freeFamily D t := by
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, hgt⟩ := freeFamily_predicts_nothing hD ht y
  exact hy g hg hgt

/-- **Hence it can never be promoted.**  Fit alone, however perfect, does not
produce a validated repair. -/
theorem no_validated_repair_from_the_free_family :
    ¬ ∃ v : ValidatedRepair (ℝ → ℝ), v.family = freeFamily ∧ Functional v.data := by
  rintro ⟨v, hfam, hfun⟩
  have hrisk : RisksSomethingAt freeFamily v.data v.heldOut.time := hfam ▸ v.risked
  exact freeFamily_risks_nothing hfun v.notUsed hrisk

/-! ## §5 Fit and refutability are still not support -/

/-- A family that is perfectly informative before `t = 2` and completely
unconstrained after it: the second parameter is a free value at late times. -/
noncomputable def blindAfterTwo : ParamFamily (ℝ × ℝ) where
  prior := univ
  predict := fun q t => if t ≤ 2 then q.1 * t else q.2

/-- Two exact early readings, explained by slope `3`. -/
def earlyData : List Reading :=
  [⟨1, 3, 0, le_refl 0⟩, ⟨2, 6, 0, le_refl 0⟩]

theorem earlyData_functional : Functional earlyData := by
  intro r hr r' hr' h
  fin_cases hr <;> fin_cases hr' <;> simp_all

theorem blindAfterTwo_compatible :
    Compatible blindAfterTwo earlyData = {q : ℝ × ℝ | q.1 = 3} := by
  ext q
  constructor
  · rintro ⟨-, hf⟩
    have h1 : |(3 : ℝ) - (if (1 : ℝ) ≤ 2 then q.1 * 1 else q.2)| ≤ 0 :=
      hf ⟨1, 3, 0, le_refl 0⟩ (List.mem_cons_self ..)
    rw [if_pos (by norm_num)] at h1
    have := abs_nonpos_iff.mp h1
    show q.1 = 3
    linarith
  · intro hq
    refine ⟨mem_univ _, fun r hr => ?_⟩
    have hq3 : q.1 = 3 := hq
    fin_cases hr
    · show |(3 : ℝ) - (if (1 : ℝ) ≤ 2 then q.1 * 1 else q.2)| ≤ 0
      rw [if_pos (by norm_num), hq3]
      norm_num
    · show |(6 : ℝ) - (if (2 : ℝ) ≤ 2 then q.1 * 2 else q.2)| ≤ 0
      rw [if_pos (by norm_num), hq3]
      norm_num

/-- The family is genuinely refutable: two incompatible early readings destroy
it. -/
theorem blindAfterTwo_refutable : Refutable blindAfterTwo := by
  refine ⟨[⟨1, 3, 0, le_refl 0⟩, ⟨2, 7, 0, le_refl 0⟩], ?_, ?_⟩
  · intro r hr r' hr' h
    fin_cases hr <;> fin_cases hr' <;> simp_all
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨-, hf⟩
    have h1 : |(3 : ℝ) - (if (1 : ℝ) ≤ 2 then q.1 * 1 else q.2)| ≤ 0 :=
      hf ⟨1, 3, 0, le_refl 0⟩ (List.mem_cons_self ..)
    have h2 : |(7 : ℝ) - (if (2 : ℝ) ≤ 2 then q.1 * 2 else q.2)| ≤ 0 :=
      hf ⟨2, 7, 0, le_refl 0⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [if_pos (by norm_num)] at h1
    rw [if_pos (by norm_num)] at h2
    have e1 := abs_nonpos_iff.mp h1
    have e2 := abs_nonpos_iff.mp h2
    linarith

/-- **`fitRestored ⇏ supported`, as a theorem.**  This repair fits the data
exactly, is refutable, and is nonetheless *blind* at the held-out time `t = 3`:
it forbids nothing there, so no measurement at `t = 3` can promote it.  Support
is a property of the prediction the repair forces, not of the fit it
achieves. -/
theorem fit_and_refutability_do_not_give_a_held_out_prediction :
    (Compatible blindAfterTwo earlyData).Nonempty ∧
      Refutable blindAfterTwo ∧
      ¬ RisksSomethingAt blindAfterTwo earlyData 3 := by
  refine ⟨⟨(3, 0), by rw [blindAfterTwo_compatible]; rfl⟩, blindAfterTwo_refutable, ?_⟩
  rintro ⟨y, hy⟩
  have hmem : ((3 : ℝ), y) ∈ Compatible blindAfterTwo earlyData := by
    rw [blindAfterTwo_compatible]; rfl
  have := hy (3, y) hmem
  apply this
  show (if (3 : ℝ) ≤ 2 then (3 : ℝ) * 3 else y) = y
  rw [if_neg (by norm_num)]

/-! ## §6 The worked promotion -/

/-- The Stage-6 measurement-model repair `y = θt + 5`, fitted to `offsetData`,
predicts `y(3) = 5`.  It therefore forbids `y(3) = 7`. -/
theorem offsetRead_risks_at_three : RisksSomethingAt offsetRead offsetData 3 := by
  refine ⟨7, fun θ hθ => ?_⟩
  obtain ⟨-, hf⟩ := hθ
  have h1 : |(5 : ℝ) - (θ * 1 + 5)| ≤ 0 := hf ⟨1, 5, 0, le_refl 0⟩ (List.mem_cons_self ..)
  have hθ0 : θ = 0 := by
    have := abs_nonpos_iff.mp h1
    linarith
  show θ * 3 + 5 ≠ 7
  rw [hθ0]
  norm_num

/-- The held-out reading, taken after the repair was fixed. -/
def heldOutReading : Reading := ⟨3, 5, 0, le_refl 0⟩

theorem offsetRead_survives_heldOut :
    (Compatible offsetRead (heldOutReading :: offsetData)).Nonempty := by
  refine ⟨0, mem_univ _, fun r hr => ?_⟩
  have hall : ∀ r' ∈ heldOutReading :: offsetData, r'.value = 5 ∧ r'.tol = 0 := by
    intro r' hr'
    fin_cases hr' <;> exact ⟨rfl, rfl⟩
  obtain ⟨hval, htol⟩ := hall r hr
  show |r.value - ((0 : ℝ) * r.time + 5)| ≤ r.tol
  rw [hval, htol]
  norm_num

/-- **A promoted repair.**  Every field is discharged: the measurement-model
repair fits the data that refuted the original family, stays refutable, forbids
an outcome at a time it never saw, and survives the reading taken there. -/
def offsetValidated : ValidatedRepair ℝ where
  klass := RepairClass.measurementModel
  family := offsetRead
  data := offsetData
  restoresFit := offsetRead_fits
  isRefutable := offsetRead_refutable
  heldOut := heldOutReading
  notUsed := by
    intro r hr
    fin_cases hr <;> · show (_ : ℝ) ≠ 3; norm_num
  risked := offsetRead_risks_at_three
  confirmed := offsetRead_survives_heldOut

/-- The promotion, stated: the repair has the stronger status, and the weaker
status is a different thing. -/
theorem offset_repair_is_promoted :
    statusOfValidated offsetValidated = RepairStatus.supported ∧
      RepairStatus.fitRestored ≠ RepairStatus.supported :=
  ⟨rfl, fitRestored_ne_supported⟩

/-! ## §7 The search step -/

/-- A nonempty list has an element of minimal cost. -/
theorem exists_min_by_cost {α : Type*} (f : α → ℝ) :
    ∀ (a : α) (l : List α), ∃ b ∈ a :: l, ∀ c ∈ a :: l, f b ≤ f c := by
  intro a l
  induction l generalizing a with
  | nil =>
      refine ⟨a, List.mem_cons_self .., ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_refl _
      · simp at hc
  | cons d ds ih =>
      obtain ⟨b, hb, hmin⟩ := ih d
      by_cases h : f a ≤ f b
      · refine ⟨a, List.mem_cons_self .., ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_refl _
        · exact h.trans (hmin c hc)
      · refine ⟨b, List.mem_cons_of_mem _ hb, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_of_not_ge h
        · exact hmin c hc

/-- **A cost-minimal validated repair exists.**  This is the only sense in which
this corpus "searches": given finitely many candidates that have *already*
discharged the validation obligations, a cheapest one can be selected. -/
theorem exists_cheapest_validated_repair (v₀ : ValidatedRepair Θ) (vs : List (ValidatedRepair Θ))
    (cost : ValidatedRepair Θ → ℝ) :
    ∃ v ∈ v₀ :: vs, ∀ w ∈ v₀ :: vs, cost v ≤ cost w :=
  exists_min_by_cost cost v₀ vs

/-- **Selection cannot smuggle in an unvalidated repair.**  Whatever the cost
function, the selected candidate carries all four obligations, because they are
fields of its type. -/
theorem cheapest_is_still_validated (v : ValidatedRepair Θ) :
    (Compatible v.family v.data).Nonempty ∧
      Refutable v.family ∧
      RisksSomethingAt v.family v.data v.heldOut.time ∧
      (Compatible v.family (v.heldOut :: v.data)).Nonempty :=
  ⟨v.restoresFit, v.isRefutable, v.risked, v.confirmed⟩

end Integration.Experiment.RepairSearch
