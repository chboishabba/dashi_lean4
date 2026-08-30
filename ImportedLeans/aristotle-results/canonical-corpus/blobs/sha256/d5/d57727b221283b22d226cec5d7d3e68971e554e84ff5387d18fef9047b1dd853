import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 6, lane 6 — repair obligations, before any repair search

`TOE_STAGE5_INFERENCE.md` frontier item 8 records that repairs are *classified,
not searched*.  Before automating a search, the obligation a repair must
discharge has to be sharp — otherwise a repair engine is an unrestricted patch
generator.  This file states the obligation and proves the scientific rule that
constrains it:

```
repair restores fit   ⇏   repair gains support.
```

## The objects

* `RepairClass` — the six kinds of missing capability a refutation can indicate:
  parameter extension, latent state, new interaction term, new dynamics,
  measurement-model change, source-assumption revision.  A finite, decidable
  enumeration, so a proposal must name its class;
* `Functional E` — a dataset that is consistent as a function of time (two
  readings at the same time report the same value); the honest precondition for
  anything at all to fit;
* `freeFamily` — the *unrestricted* repair: an arbitrary function of time as the
  "parameter".  This is what an unconstrained patch generator would produce;
* `Refutable F` — there exists a functional dataset that the family cannot fit;
* `RepairProposal` — a class, a repaired family, the data, a proof that the
  repair **restores fit**, and a proof that the repair **is refutable**.  The
  second field is the one that makes fit into evidence.

## What is proved

* `interpolant_mem_compatible`, `freeFamily_fits_everything` — the unrestricted
  repair fits *every* functionally consistent dataset;
* `freeFamily_not_refutable` — hence it is not refutable by any data;
* `freeFamily_predicts_nothing` — and at any time not already measured its
  prediction envelope is the whole line: restoring fit has bought no
  prediction.  Together these three are the formal content of
  `repair restores fit ⇏ repair gains support`;
* `saturated_repair_is_no_proposal` — consequently the unrestricted repair
  **cannot** inhabit `RepairProposal`: the record's refutability field rejects
  it.  This is the gate a repair search must pass;
* `proportional_family_cannot_fit_the_offset_data` and `offsetProposal` — the
  classes are not interchangeable: a dataset exists that no member of the
  proportional family fits and that a measurement-model repair fits, and that
  repair is itself refutable, so it is a genuine proposal.

## What is *not* claimed

No repair is *searched* here, and no ranking among admissible proposals is
given: `RepairProposal` is a soundness gate, not a generator, and refutability
is a necessary condition for earning support, not a sufficient one.  Nothing
here says a refuted family's true defect is in the class a proposal names.
-/

namespace Integration.Experiment.RepairObligations

open Set
open Integration.Experiment.ParameterRegion

/-! ## §1 The classification of missing capabilities -/

/-- **The repair classes**: what kind of capability the refuted family lacked.
A repair proposal must name one, so that a search is organised by class rather
than being an unrestricted patch generator. -/
inductive RepairClass
  /-- The family needs another parameter. -/
  | parameterExtension
  /-- The family needs an unobserved state variable. -/
  | latentState
  /-- The family needs an interaction between existing variables. -/
  | interactionTerm
  /-- The family needs different dynamics. -/
  | newDynamics
  /-- The map from state to observation is wrong. -/
  | measurementModel
  /-- An assumption about the data source is wrong. -/
  | sourceAssumption
  deriving DecidableEq, Fintype, Repr

/-- The enumeration is the six classes and nothing else. -/
theorem repairClass_card : Fintype.card RepairClass = 6 := by decide

/-! ## §2 Functional data and the unrestricted repair -/

/-- A dataset is **functional** when readings at the same time agree.  Without
this, no function of time fits, and the failure says nothing about the model. -/
def Functional (E : List Reading) : Prop :=
  ∀ r ∈ E, ∀ r' ∈ E, r.time = r'.time → r.value = r'.value

/-- **The unrestricted repair**: the "parameter" is an arbitrary function of
time.  This is the family a patch generator with no discipline would reach. -/
def freeFamily : ParamFamily (ℝ → ℝ) where
  prior := univ
  predict := fun g t => g t

open scoped Classical in
/-- The function reading off the data at measured times and `0` elsewhere. -/
noncomputable def interpolant (E : List Reading) : ℝ → ℝ := fun t =>
  match E.find? (fun r => decide (r.time = t)) with
  | some r => r.value
  | none => 0

theorem interpolant_at_reading {E : List Reading} (hE : Functional E) {r : Reading} (hr : r ∈ E) :
    interpolant E r.time = r.value := by
  classical
  have hsome : (E.find? (fun r' => decide (r'.time = r.time))).isSome := by
    rw [List.find?_isSome]
    exact ⟨r, hr, by simp⟩
  obtain ⟨r'', hr''⟩ := Option.isSome_iff_exists.1 hsome
  have hmem : r'' ∈ E := List.mem_of_find?_eq_some hr''
  have hpred : r''.time = r.time := by
    have := List.find?_some hr''
    simpa using this
  simp only [interpolant, hr'']
  exact hE r'' hmem r hr hpred

/-- **The unrestricted repair fits every functionally consistent dataset.** -/
theorem interpolant_mem_compatible {E : List Reading} (hE : Functional E) :
    interpolant E ∈ Compatible freeFamily E := by
  refine ⟨mem_univ _, ?_⟩
  intro r hr
  show |r.value - freeFamily.predict (interpolant E) r.time| ≤ r.tol
  have : freeFamily.predict (interpolant E) r.time = r.value := interpolant_at_reading hE hr
  rw [this, sub_self, abs_zero]
  exact r.tol_nonneg

theorem freeFamily_fits_everything {E : List Reading} (hE : Functional E) :
    (Compatible freeFamily E).Nonempty :=
  ⟨interpolant E, interpolant_mem_compatible hE⟩

/-- A family is **refutable** when some functionally consistent dataset would
leave no surviving parameter.  Refutability is what a repair must retain in
order to be able to earn support. -/
def Refutable {Θ : Type*} (F : ParamFamily Θ) : Prop :=
  ∃ E, Functional E ∧ Compatible F E = ∅

/-- **The unrestricted repair is not refutable.** -/
theorem freeFamily_not_refutable : ¬ Refutable freeFamily := by
  rintro ⟨E, hE, hempty⟩
  obtain ⟨g, hg⟩ := freeFamily_fits_everything hE
  rw [hempty] at hg
  exact hg

/-- **And it predicts nothing.**  At any time not already measured, every value
is still attainable by a family member that fits all the data: restoring fit has
bought no discriminating prediction. -/
theorem freeFamily_predicts_nothing {E : List Reading} (hE : Functional E) {t : ℝ}
    (ht : ∀ r ∈ E, r.time ≠ t) (y : ℝ) :
    ∃ g ∈ Compatible freeFamily E, g t = y := by
  classical
  refine ⟨Function.update (interpolant E) t y, ⟨mem_univ _, ?_⟩, by simp⟩
  intro r hr
  show |r.value - freeFamily.predict (Function.update (interpolant E) t y) r.time| ≤ r.tol
  have hne : r.time ≠ t := ht r hr
  have : freeFamily.predict (Function.update (interpolant E) t y) r.time = r.value := by
    show Function.update (interpolant E) t y r.time = r.value
    rw [Function.update_of_ne hne]
    exact interpolant_at_reading hE hr
  rw [this, sub_self, abs_zero]
  exact r.tol_nonneg

/-! ## §3 The obligation a repair must discharge -/

/-- **A repair proposal**: a named class, the repaired family, the data it must
explain, a proof that it *restores fit*, and — the field that does the work — a
proof that it *remains refutable*.  A repair that cannot be refuted cannot earn
support, however well it fits. -/
structure RepairProposal (Θ : Type*) where
  /-- Which missing capability the repair supplies. -/
  klass : RepairClass
  /-- The repaired family. -/
  family : ParamFamily Θ
  /-- The data the original family failed on. -/
  data : List Reading
  /-- The repair restores fit. -/
  restoresFit : (Compatible family data).Nonempty
  /-- The repair remains refutable — it risks something. -/
  isRefutable : Refutable family

/-- **The gate.**  The unrestricted repair can never be a proposal, because it
is not refutable: fit alone does not qualify.  This is the formal statement of
`repair may restore fit ⇏ repair gains support`. -/
theorem saturated_repair_is_no_proposal :
    ¬ ∃ p : RepairProposal (ℝ → ℝ), p.family = freeFamily := by
  rintro ⟨p, hp⟩
  exact freeFamily_not_refutable (hp ▸ p.isRefutable)

/-! ## §4 The classes are not interchangeable -/

/-- The proportional family `y = θ t`: a pure parameter family. -/
def proportional : ParamFamily ℝ where
  prior := univ
  predict := fun θ t => θ * t

/-- The same dynamics read through a shifted instrument, `y = θ t + 5`: a
*measurement-model* repair, not a parameter extension. -/
def offsetRead : ParamFamily ℝ where
  prior := univ
  predict := fun θ t => θ * t + 5

/-- Two exact readings that a constant offset explains. -/
def offsetData : List Reading :=
  [⟨1, 5, 0, le_refl 0⟩, ⟨2, 5, 0, le_refl 0⟩]

theorem offsetData_functional : Functional offsetData := by
  intro r hr r' hr' h
  fin_cases hr <;> fin_cases hr' <;> simp_all

/-- **No parameter of the proportional family fits the data**: the defect is not
in the parameter, so a parameter extension of this family is the wrong class. -/
theorem proportional_family_cannot_fit_the_offset_data :
    Compatible proportional offsetData = ∅ := by
  ext θ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hfits⟩
  have h1 : |(5 : ℝ) - θ * 1| ≤ 0 := hfits ⟨1, 5, 0, le_refl 0⟩ (by simp [offsetData])
  have h2 : |(5 : ℝ) - θ * 2| ≤ 0 := hfits ⟨2, 5, 0, le_refl 0⟩ (by simp [offsetData])
  have e1 : (5 : ℝ) - θ * 1 = 0 := abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))
  have e2 : (5 : ℝ) - θ * 2 = 0 := abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
  have : θ = 5 := by linarith
  rw [this] at e2
  norm_num at e2

/-- The measurement-model repair does fit, with `θ = 0`. -/
theorem offsetRead_fits : (Compatible offsetRead offsetData).Nonempty := by
  refine ⟨0, mem_univ _, ?_⟩
  intro r hr
  fin_cases hr <;> · show |_ - (0 * _ + (5:ℝ))| ≤ (0:ℝ); norm_num

/-- And it is itself refutable: a reading of `0` at time `0` would leave no
parameter, so the repair risks something. -/
theorem offsetRead_refutable : Refutable offsetRead := by
  refine ⟨[⟨0, 0, 0, le_refl 0⟩], ?_, ?_⟩
  · intro r hr r' hr' _
    fin_cases hr; fin_cases hr'; rfl
  · ext θ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hfits⟩
    have h := hfits ⟨0, 0, 0, le_refl 0⟩ (by simp)
    have : |(0 : ℝ) - (θ * 0 + 5)| ≤ 0 := h
    rw [show (0 : ℝ) - (θ * 0 + 5) = -5 by ring] at this
    norm_num at this

/-- **A genuine repair proposal**, in the measurement-model class: it restores
fit and remains refutable.  Contrast `saturated_repair_is_no_proposal`. -/
def offsetProposal : RepairProposal ℝ where
  klass := RepairClass.measurementModel
  family := offsetRead
  data := offsetData
  restoresFit := offsetRead_fits
  isRefutable := offsetRead_refutable

end Integration.Experiment.RepairObligations
