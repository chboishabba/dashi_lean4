import Integration.Kernel.Loop
import Integration.Experiment.ParameterRegion

/-!
# The parameter-region lane is a thin instance of the kernel

`Integration.Experiment.ParameterRegion` develops the surviving parameter region
`Compatible F E` and proves monotonicity, soundness and envelope antitonicity
for it directly.  This file shows that *all of that is the residual-fibre
calculus*, with no new content:

* `fitEvent F r` — the set of parameters compatible with one reading, and
  `fitEvent_eq_preimage`: it is the preimage, under the prediction channel
  `predChannel F r`, of the reading's tolerance interval.  An imperfect
  measurement is a preimage of a *set*, not of a point.
* `compatible_eq_refineAll` — **the lane's surviving region is literally the
  kernel's iterated backward refinement** of the prior by those events.

From that identification the lane's theorems are re-derived as instances:

* `compatible_refines_prior` (`refineAll_refines`),
* `evidence_refines` (`refineAll_append_refines`),
* `truth_survives_kernel` (`mem_refineAll_of_forall`),
* `envelope_subsingleton_of_determines` — the kernel's consumer closure
  `Determines` is exactly "the prediction envelope has collapsed to a point";
  `determines_of_envelope_subsingleton` is the converse, so the two notions
  agree.

The honest limit is recorded too: `region_narrowing_is_not_identification`
instantiates the kernel refusal `narrower_not_mechanism` in this lane —
a strictly smaller surviving region need not pin the parameter down.
-/

namespace Integration.Kernel.Instances.ParameterRegionBridge

open Set Integration.Kernel.ResidualFibre Integration.Experiment.ParameterRegion

variable {Θ : Type*}

/-! ## §1 A reading as a kernel event -/

/-- The channel that reports a family's prediction at the reading's time. -/
def predChannel (F : ParamFamily Θ) (r : Reading) : Channel Θ ℝ :=
  ⟨fun θ => F.predict θ r.time⟩

/-- The parameters compatible with one reading. -/
def fitEvent (F : ParamFamily Θ) (r : Reading) : Set Θ := {θ | Fits F θ r}

/-- An imperfect reading is the preimage of an interval, not of a point. -/
theorem fitEvent_eq_preimage (F : ParamFamily Θ) (r : Reading) :
    fitEvent F r = (predChannel F r).read ⁻¹' Icc (r.value - r.tol) (r.value + r.tol) := by
  ext θ
  simp only [fitEvent, mem_setOf_eq, Fits, mem_preimage, mem_Icc, predChannel,
    abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩; constructor <;> linarith
  · rintro ⟨h₁, h₂⟩; constructor <;> linarith

/-! ## §2 The identification -/

theorem refineAll_fitEvents (F : ParamFamily Θ) (P : Set Θ) (E : List Reading) :
    refineAll P (E.map (fitEvent F)) = {θ | θ ∈ P ∧ ∀ r ∈ E, Fits F θ r} := by
  induction E generalizing P with
  | nil => ext θ; simp
  | cons r E ih =>
      ext θ
      simp only [List.map_cons, refineAll_cons, ih, mem_setOf_eq, refineBy, mem_inter_iff,
        fitEvent, List.mem_cons]
      constructor
      · rintro ⟨⟨hP, hr⟩, hE⟩
        exact ⟨hP, by rintro r' (rfl | hr') ; exacts [hr, hE r' hr']⟩
      · rintro ⟨hP, hall⟩
        exact ⟨⟨hP, hall r (Or.inl rfl)⟩, fun r' hr' => hall r' (Or.inr hr')⟩

/-- **The surviving parameter region is the kernel's iterated refinement.** -/
theorem compatible_eq_refineAll (F : ParamFamily Θ) (E : List Reading) :
    Compatible F E = refineAll F.prior (E.map (fitEvent F)) := by
  rw [refineAll_fitEvents]
  rfl

/-! ## §3 The lane's theorems, as kernel instances -/

theorem compatible_refines_prior (F : ParamFamily Θ) (E : List Reading) :
    Refines (Compatible F E) F.prior := by
  rw [compatible_eq_refineAll]; exact refineAll_refines _ _

theorem evidence_refines (F : ParamFamily Θ) (E E' : List Reading) :
    Refines (Compatible F (E ++ E')) (Compatible F E) := by
  rw [compatible_eq_refineAll, compatible_eq_refineAll, List.map_append]
  exact refineAll_append_refines _ _ _

theorem truth_survives_kernel (F : ParamFamily Θ) (E : List Reading) {θ : Θ}
    (hp : θ ∈ F.prior) (hf : ∀ r ∈ E, Fits F θ r) : θ ∈ Compatible F E := by
  rw [compatible_eq_refineAll]
  refine mem_refineAll_of_forall hp ?_
  intro E' hE'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hE'
  exact hf r hr

/-! ## §4 Consumer closure is envelope collapse -/

theorem envelope_subsingleton_of_determines {F : ParamFamily Θ} {E : List Reading} {C : Θ → ℝ}
    (h : Determines (Compatible F E) C) : ∃ v, envelope F E C ⊆ {v} := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, ?_⟩
  rintro x ⟨θ, hθ, rfl⟩
  exact hv θ hθ

theorem determines_of_envelope_subsingleton {F : ParamFamily Θ} {E : List Reading} {C : Θ → ℝ}
    {v : ℝ} (h : envelope F E C ⊆ {v}) : Determines (Compatible F E) C :=
  ⟨v, fun θ hθ => h ⟨θ, hθ, rfl⟩⟩

/-! ## §5 The lane inherits the kernel's refusal -/

/-- **A strictly smaller surviving region need not identify the parameter.**
The instance: a two-parameter family whose prediction ignores the second
coordinate; one reading removes half the prior and leaves the second coordinate
entirely open. -/
theorem region_narrowing_is_not_identification :
    ∃ (F : ParamFamily (ℝ × ℝ)) (E : List Reading),
      Compatible F E ⊂ F.prior ∧ (Compatible F E).Nonempty ∧
        ¬ Determines (Compatible F E) Prod.snd := by
  refine ⟨⟨univ, fun θ _ => θ.1⟩, [⟨0, 0, 0, le_rfl⟩], ⟨?_, ?_⟩, ⟨(0, 0), ?_⟩, ?_⟩
  · exact compatible_refines_prior _ _
  · intro h
    have : ((1 : ℝ), (0 : ℝ)) ∈ Compatible (⟨univ, fun θ _ => θ.1⟩ : ParamFamily (ℝ × ℝ))
        [⟨0, 0, 0, le_rfl⟩] := h (mem_univ _)
    have hf := this.2 ⟨0, 0, 0, le_rfl⟩ (List.mem_singleton_self _)
    simp [Fits] at hf
    linarith
  · exact ⟨mem_univ _, by intro r hr; simp [Fits, List.mem_singleton.1 hr]⟩
  · rintro ⟨v, hv⟩
    have h1 : ((0 : ℝ), (0 : ℝ)).2 = v :=
      hv _ ⟨mem_univ _, by intro r hr; simp [Fits, List.mem_singleton.1 hr]⟩
    have h2 : ((0 : ℝ), (1 : ℝ)).2 = v :=
      hv _ ⟨mem_univ _, by intro r hr; simp [Fits, List.mem_singleton.1 hr]⟩
    rw [← h2] at h1
    exact zero_ne_one h1

end Integration.Kernel.Instances.ParameterRegionBridge
