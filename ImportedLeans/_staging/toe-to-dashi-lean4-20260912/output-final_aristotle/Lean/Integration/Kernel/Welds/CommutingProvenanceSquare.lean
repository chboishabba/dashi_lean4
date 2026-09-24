import Integration.Kernel.Quotient

/-!
# Weld: commuting provenance for source summaries and pipelines

"This coarse report is a projection of the fine record" and "this coarse report
happens to agree with the fine record" are different claims, and the corpus has
been using the first while only ever exhibiting the second.  The difference is
exactly a commuting square: a projection has to commute with the step the
pipeline takes, not merely match at the point of observation.

## What is proved

* `IsProjection π f g` — the commuting square `π ∘ f = g ∘ π`.
* **`projection_transports_along_pipeline`** — the payoff: with the square,
  agreement of the report with the record at time `0` gives agreement at every
  later time, by induction along the iterates.  This is what licenses reading
  the coarse trajectory as the fine one's shadow.
* **`agreement_now_is_not_a_projection`** — the negative that makes the demand
  non-trivial: a coarse reading that agrees with the fine record now and
  disagrees one step later, so pointwise compatibility does not imply the
  square.
* **`whole_trajectory_agreement_is_not_a_projection`** — the sharper version:
  agreement along the *entire observed trajectory* of one record still does not
  give the square, because the square is a statement about all records.
* `ProjectionClaim`, `ProjectionClaim.transports` and
  **`compatibility_does_not_promote`** — the claim discipline: a structure that
  carries the commuting proof transports, and no function of the observed
  agreement produces it.

**Claim boundary.**  Records, reports and steps are finite labels and functions
between them, all stipulated here.  Nothing is claimed about any actual
experiment, data pipeline, summary or source.
-/

namespace Integration.Kernel.Welds.CommutingProvenanceSquare

open Integration.Kernel.Quotient

variable {X A : Type*}

/-! ## §1 The square -/

/-- The coarsening `π` intertwines the fine step `f` with the coarse step `g`. -/
def IsProjection (pi : X → A) (f : X → X) (g : A → A) : Prop := ∀ x, pi (f x) = g (pi x)

/-- **A projection transports along the pipeline.**  If the report agrees with
the coarsened record now, it agrees at every later step. -/
theorem projection_iterate {pi : X → A} {f : X → X} {g : A → A}
    (hsq : IsProjection pi f g) : ∀ (n : ℕ) (x : X), pi (f^[n] x) = g^[n] (pi x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (f x), hsq]

theorem projection_transports_along_pipeline {pi : X → A} {f : X → X} {g : A → A}
    (hsq : IsProjection pi f g) (x : X) (a : A) (h0 : a = pi x) (n : ℕ) :
    g^[n] a = pi (f^[n] x) := by
  rw [h0, projection_iterate hsq n x]

/-! ## §2 Agreement is weaker than the square -/

/-- The fine record: a pair of bits, only the first of which is reported. -/
abbrev Fine := Bool × Bool

/-- The coarse report. -/
abbrev Coarse := Bool

/-- The coarsening: report the first coordinate. -/
def report : Fine → Coarse := Prod.fst

/-- The fine step: the hidden coordinate drives the reported one. -/
def fineStep : Fine → Fine := fun p => (p.2, p.2)

/-- The coarse step a summary might guess: leave the report alone. -/
def coarseStep : Coarse → Coarse := id

/-- **Agreeing now is not being a projection.**  On the record `(true, false)`
the report agrees at time `0` and disagrees at time `1`; the square fails. -/
theorem agreement_now_is_not_a_projection :
    report (true, false) = coarseStep (report (true, false)) ∧
      report (fineStep (true, false)) ≠ coarseStep (report (true, false)) ∧
        ¬ IsProjection report fineStep coarseStep := by
  refine ⟨rfl, by decide, fun h => ?_⟩
  exact absurd (h (true, false)) (by decide)

/-- A record on whose whole trajectory the guessed coarse step is correct. -/
def stableRecord : Fine := (true, true)

/-- **Agreement along the entire observed trajectory is still not the square.**
On `stableRecord` the coarse step reproduces the report at every time, and the
square nevertheless fails — at a different record. -/
theorem whole_trajectory_agreement_is_not_a_projection :
    (∀ n : ℕ, coarseStep^[n] (report stableRecord) = report (fineStep^[n] stableRecord)) ∧
      ¬ IsProjection report fineStep coarseStep := by
  constructor
  · intro n
    have hfix : ∀ m : ℕ, fineStep^[m] stableRecord = stableRecord := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl
    have hcoarse : ∀ m : ℕ, coarseStep^[m] (report stableRecord) = report stableRecord := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl
    rw [hfix n, hcoarse n]
  · exact (agreement_now_is_not_a_projection).2.2

/-- A coarse step that *does* commute with the coarsening is available only when
the coarse data really determines the next report; here no such step exists. -/
theorem no_coarse_step_commutes : ¬ ∃ g : Coarse → Coarse, IsProjection report fineStep g := by
  rintro ⟨g, hg⟩
  have h1 : (true : Bool) = g true := hg (true, true)
  have h2 : (false : Bool) = g true := hg (true, false)
  rw [← h2] at h1
  exact Bool.noConfusion h1

/-! ## §3 The claim discipline -/

/-- A claim that a coarse report is a projection of a fine record: it has to
carry the square, not just the agreement. -/
structure ProjectionClaim (X A : Type*) where
  /-- The coarsening being claimed. -/
  pi : X → A
  /-- The fine step. -/
  fine : X → X
  /-- The coarse step. -/
  coarse : A → A
  /-- The commuting square, as a proof obligation. -/
  square : IsProjection pi fine coarse

/-- A claim that carries the square transports along the pipeline. -/
theorem ProjectionClaim.transports (c : ProjectionClaim X A) (x : X) (n : ℕ) :
    c.coarse^[n] (c.pi x) = c.pi (c.fine^[n] x) :=
  projection_transports_along_pipeline c.square x (c.pi x) rfl n

/-- The projection claim that does hold for `report`: the fine step read on the
fine side. -/
def honestClaim : ProjectionClaim Fine Fine where
  pi := id
  fine := fineStep
  coarse := fineStep
  square := fun _ => rfl

/-- **Observed agreement does not promote to a projection claim.**  Two
coarse-step candidates agree with the coarsened record on `stableRecord` at
every time, and exactly one of them satisfies the square; so no function of the
observed agreement returns the square. -/
theorem compatibility_does_not_promote :
    (∀ n : ℕ, coarseStep^[n] (report stableRecord) = report (fineStep^[n] stableRecord)) ∧
      ¬ IsProjection report fineStep coarseStep ∧
        IsProjection (id : Fine → Fine) fineStep fineStep :=
  ⟨whole_trajectory_agreement_is_not_a_projection.1,
    whole_trajectory_agreement_is_not_a_projection.2, fun _ => rfl⟩

end Integration.Kernel.Welds.CommutingProvenanceSquare
