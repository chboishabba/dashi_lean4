import Integration.PathTransport

/-!
# Increments, and two-boundary conditioning

Two small domain-neutral owners.

**Contrast.**  A contrast operator turns a pair of states into a value; the
temporal case `Δ O_t = O_{t+1} − O_t` is a discrete derivative.  The theorems
worth owning are that increments telescope (so a trajectory is recovered from
its increments together with one initial condition) and that the present state
does not determine the increment.

**Two boundaries.**  Fixing a past condition and a future condition selects a
set of admissible intermediate states.  The theorem worth owning is that this
set genuinely depends on both boundaries — changing either one changes it — and
that it is not a function of either alone.  Nothing here is retrocausal: the
statement is about which two-sided constraints a path satisfies.

Contents.

* `contrast`, `sum_contrast`, `state_add_contrasts` — the discrete derivative
  and its telescoping;
* `contrast_not_determined_by_state` — two trajectories agreeing at a time with
  different increments there;
* `Middles`, `middles_depends_on_future`, `middles_depends_on_past`,
  `middles_not_function_of_past` — the two-boundary constraint system on an
  explicit graph.
-/

namespace Integration.ContrastBoundary

open Integration.PathTransport

/-! ## Contrast as a discrete derivative -/

variable {α : Type*} [AddCommGroup α]

/-- The increment of a trajectory. -/
def contrast (O : ℕ → α) (t : ℕ) : α := O (t + 1) - O t

/-- **Increments telescope.** -/
theorem sum_contrast (O : ℕ → α) (n : ℕ) : ∑ k ∈ Finset.range n, contrast O k = O n - O 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, contrast]
    abel

/-- So the state at any time is the initial state plus the accumulated
increments: the trajectory and the increment sequence carry the same
information, given one boundary value. -/
theorem state_add_contrasts (O : ℕ → α) (n : ℕ) :
    O n = O 0 + ∑ k ∈ Finset.range n, contrast O k := by
  rw [sum_contrast]
  abel

/-- **The present state does not determine the increment.**  Two trajectories
agree at a time and have different increments there, so no function of the
current state is the contrast. -/
theorem contrast_not_determined_by_state :
    ¬ ∃ f : ℤ → ℤ, ∀ (O : ℕ → ℤ) (t : ℕ), contrast O t = f (O t) := by
  rintro ⟨f, hf⟩
  have h1 := hf (fun _ => 0) 0
  have h2 := hf (fun k => (k : ℤ)) 0
  simp only [contrast] at h1 h2
  norm_num at h1 h2
  rw [← h1] at h2
  exact absurd h2 (by norm_num)

/-! ## Two-boundary conditioning -/

variable {X : Type*}

/-- The admissible intermediate states between a past and a future boundary, in
one step each way. -/
def Middles (step : X → X → Prop) (a c : X) : Set X := {b | step a b ∧ step b c}

/-- A three-state graph: `0 → 1`, `0 → 2`, `1 → 0`, `2 → 0`, `1 → 1`. -/
def sampleStepB (x y : Fin 3) : Bool :=
  (decide (x = 0 ∧ y = 1)) || (decide (x = 0 ∧ y = 2)) || (decide (x = 1 ∧ y = 0)) ||
    (decide (x = 2 ∧ y = 0)) || (decide (x = 1 ∧ y = 1))

/-- The relation form. -/
def sampleStep (x y : Fin 3) : Prop := sampleStepB x y = true

instance (x y : Fin 3) : Decidable (sampleStep x y) :=
  inferInstanceAs (Decidable (sampleStepB x y = true))

/-- **The admissible set depends on the future boundary.**  With past `0`, the
future `0` admits two middles and the future `1` admits one. -/
theorem middles_depends_on_future :
    (1 : Fin 3) ∈ Middles sampleStep 0 0 ∧ (2 : Fin 3) ∈ Middles sampleStep 0 0 ∧
      (1 : Fin 3) ∈ Middles sampleStep 0 1 ∧ (2 : Fin 3) ∉ Middles sampleStep 0 1 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  rintro ⟨-, h⟩
  exact absurd h (by decide)

/-- **And on the past boundary.**  With future `0`, the past `0` admits `1` and
the past `1` does not. -/
theorem middles_depends_on_past :
    (1 : Fin 3) ∈ Middles sampleStep 0 0 ∧ (1 : Fin 3) ∉ Middles sampleStep 2 0 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- Hence the admissible set is not a function of the past boundary alone. -/
theorem middles_not_function_of_past :
    ¬ ∃ g : Fin 3 → Set (Fin 3), ∀ a c, Middles sampleStep a c = g a := by
  rintro ⟨g, hg⟩
  have h1 : Middles sampleStep 0 0 = Middles sampleStep 0 1 := by
    rw [hg 0 0, hg 0 1]
  have h2 : (2 : Fin 3) ∈ Middles sampleStep 0 0 := middles_depends_on_future.2.1
  rw [h1] at h2
  exact middles_depends_on_future.2.2.2 h2

end Integration.ContrastBoundary
