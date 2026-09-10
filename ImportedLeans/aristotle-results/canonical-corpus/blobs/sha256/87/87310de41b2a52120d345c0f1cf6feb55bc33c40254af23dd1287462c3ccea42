import Integration.Kernel.Loop

/-!
# Four distributions, and why a cost function cannot rank experiments

An instance of the kernel's *probe selection* layer.  The loop of
`Integration.Kernel.Loop` chooses which probe to run; a cost function is the
usual way to choose.  This file proves what a scalar summary of a programme
cannot see.

A `Programme` over a finite party type carries four independent distributions:
who contributes, who benefits, who bears the burden, who has a voice.

* `aggregate_hides_distribution` — two programmes with the *same* aggregate in
  all four coordinates and different distributions in every one of them: an
  aggregate-success surface does not recover the four distributions.
* `equal_cost_not_equal_burden`, `equal_cost_not_equal_benefit`,
  `equal_cost_not_equal_voice` — **equal declared experiment cost ⇏ equal
  external burden** (or benefit, or affected-party voice).
* `cheapest_is_not_least_burdensome` — the strictly cheaper of two experiments
  can be the one with the strictly more concentrated burden, so "cheapest" must
  not be promoted to "best admissible".
* `cost_is_not_a_function_of_burden` — no function of the burden distribution
  returns the declared cost, and `burden_is_not_a_function_of_cost` conversely;
  the two are independent coordinates, so neither can stand in for the other.

**Claim boundary.** Parties are two labels, and each distribution is a pair of
rationals.  Nothing is claimed about any real programme, community or
experiment; the content is exactly the independence of the four coordinates and
of cost from burden.
-/

namespace Integration.Kernel.Instances.Distribution

/-- Two parties. -/
abbrev Party := Bool

/-- A programme, seen through its four distributions. -/
structure Programme where
  /-- Who puts work in. -/
  contributes : Party → ℚ
  /-- Who gains. -/
  benefits : Party → ℚ
  /-- Who carries the risk or burden. -/
  bears : Party → ℚ
  /-- Who has a say. -/
  voice : Party → ℚ

/-- The aggregate of a distribution over the two parties. -/
def aggregate (f : Party → ℚ) : ℚ := f true + f false

/-- The programme's aggregate-success surface: the four totals. -/
def surface (P : Programme) : ℚ × ℚ × ℚ × ℚ :=
  (aggregate P.contributes, aggregate P.benefits, aggregate P.bears, aggregate P.voice)

private def even : Programme :=
  { contributes := fun _ => 1, benefits := fun _ => 1, bears := fun _ => 1, voice := fun _ => 1 }

private def skewed : Programme :=
  { contributes := fun p => if p then 2 else 0
    benefits := fun p => if p then 0 else 2
    bears := fun p => if p then 2 else 0
    voice := fun p => if p then 0 else 2 }

/-- **An aggregate-success surface does not recover the four distributions.** -/
theorem aggregate_hides_distribution :
    surface even = surface skewed ∧
      even.contributes ≠ skewed.contributes ∧ even.benefits ≠ skewed.benefits ∧
        even.bears ≠ skewed.bears ∧ even.voice ≠ skewed.voice := by
  refine ⟨by norm_num [surface, aggregate, even, skewed], ?_, ?_, ?_, ?_⟩ <;>
    · intro h
      have := congrFun h true
      simp [even, skewed] at this

/-! ## Cost does not rank experiments -/

/-- A declared experiment: its cost, and the four distributions it induces. -/
structure Experiment where
  /-- The declared cost of running it. -/
  cost : ℚ
  /-- Its programme. -/
  programme : Programme

private def cheapConcentrated : Experiment :=
  { cost := 1
    programme :=
      { contributes := fun _ => 1
        benefits := fun p => if p then 2 else 0
        bears := fun p => if p then 0 else 2
        voice := fun p => if p then 1 else 0 } }

private def dearShared : Experiment :=
  { cost := 3
    programme :=
      { contributes := fun _ => 1, benefits := fun _ => 1, bears := fun _ => 1
        voice := fun _ => 1 } }

private def cheapShared : Experiment :=
  { cost := 1
    programme :=
      { contributes := fun _ => 1, benefits := fun _ => 1, bears := fun _ => 1
        voice := fun _ => 1 } }

/-- **Equal declared cost ⇏ equal external burden.** -/
theorem equal_cost_not_equal_burden :
    cheapConcentrated.cost = cheapShared.cost ∧
      cheapConcentrated.programme.bears ≠ cheapShared.programme.bears := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrFun h true
  simp [cheapConcentrated, cheapShared] at this

/-- Equal declared cost ⇏ equal benefit distribution. -/
theorem equal_cost_not_equal_benefit :
    cheapConcentrated.cost = cheapShared.cost ∧
      cheapConcentrated.programme.benefits ≠ cheapShared.programme.benefits := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrFun h true
  simp [cheapConcentrated, cheapShared] at this

/-- Equal declared cost ⇏ equal affected-party voice. -/
theorem equal_cost_not_equal_voice :
    cheapConcentrated.cost = cheapShared.cost ∧
      cheapConcentrated.programme.voice ≠ cheapShared.programme.voice := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrFun h false
  simp [cheapConcentrated, cheapShared] at this

/-- The burden is *concentrated* when one party bears everything. -/
def Concentrated (f : Party → ℚ) : Prop := f true = 0 ∨ f false = 0

/-- **Cheapest is not least burdensome.**  The strictly cheaper experiment here
is the one whose burden falls entirely on one party. -/
theorem cheapest_is_not_least_burdensome :
    cheapConcentrated.cost < dearShared.cost ∧
      Concentrated cheapConcentrated.programme.bears ∧
        ¬ Concentrated dearShared.programme.bears := by
  refine ⟨by norm_num [cheapConcentrated, dearShared], Or.inl rfl, ?_⟩
  rintro (h | h) <;> simp [dearShared] at h

/-- No rule reading the burden distribution returns the declared cost. -/
theorem cost_is_not_a_function_of_burden :
    ¬ ∃ f : (Party → ℚ) → ℚ, ∀ E : Experiment, f E.programme.bears = E.cost := by
  rintro ⟨f, hf⟩
  have h1 := hf dearShared
  have h2 := hf cheapShared
  rw [show dearShared.programme.bears = cheapShared.programme.bears from rfl, h2] at h1
  norm_num [dearShared, cheapShared] at h1

/-- Nor does the cost determine the burden distribution. -/
theorem burden_is_not_a_function_of_cost :
    ¬ ∃ g : ℚ → (Party → ℚ), ∀ E : Experiment, g E.cost = E.programme.bears := by
  rintro ⟨g, hg⟩
  have h1 := hg cheapConcentrated
  have h2 := hg cheapShared
  rw [show cheapConcentrated.cost = cheapShared.cost from rfl, h2] at h1
  have := congrFun h1 true
  simp [cheapConcentrated, cheapShared] at this

end Integration.Kernel.Instances.Distribution
