import Integration.Kernel.Quotient

/-!
# Weld: residual salience → the search scheduler

The corpus already schedules work off residuals: the first open coordinate of a
cutset produces an obligation, a producer and a unit of work
(`Integration.Kernel.QueryResidual`).  What it schedules by, though, is size and
cost.  The observation this file formalises is different and sharper: a residual
matters to the extent that it **separates the currently live hypotheses**, and a
numerically tiny residual can be maximally separating while a large one is inert.

## What is proved

* `splitCount`, `Separates` — salience of a residual *relative to a live set*,
  with `separates_iff_splitCount_pos` tying the decidable count to the
  existential form.
* **`constant_reading_no_progress`** — a residual on which every live hypothesis
  reads the same leaves the live set exactly as it was: inert whatever its
  magnitude.
* **`separating_strictly_narrows`** — a separating residual strictly shrinks the
  live set on every possible reading, so salience in this sense is exactly
  progress.
* **`salience_does_not_descend_through_magnitude_and_cost`** — the scheduling
  claim: two residuals with the same magnitude and the same cost, one inert and
  one maximally separating.  No priority function of size and cost is a priority
  function of salience.
* **`salience_is_live_set_relative`** — and the same residual is maximally
  salient against one live set and inert against another, so salience is a
  property of the (residual, live set) pair; `salience_descends_through_pair`
  gives the positive half.
* `bestBySalience` and **`salience_scheduler_beats_magnitude_scheduler`** — the
  two schedulers on the same candidate list: the magnitude-greedy one returns
  the inert residual and makes no progress; the salience-greedy one returns the
  small residual and strictly narrows.

**Claim boundary.**  Hypotheses are elements of `Fin 4`, residuals are Boolean
readings with stipulated magnitude and cost labels.  Nothing here measures any
real experiment, model or budget.
-/

namespace Integration.Kernel.Welds.ResidualSalienceScheduler

open Integration.Kernel.Quotient

/-! ## §1 Residuals and their salience against a live set -/

/-- The live hypotheses. -/
abbrev Hyp := Fin 4

/-- A residual: what it reads on each hypothesis, together with the numerical
size and the cost that a naive scheduler would use. -/
structure Residual where
  /-- The reading of the residual on a hypothesis. -/
  read : Hyp → Bool
  /-- How big the residual is. -/
  magnitude : ℕ
  /-- What it costs to chase it. -/
  cost : ℕ
  deriving DecidableEq

/-- The live hypotheses after reading `b` from residual `t`. -/
def refineLive (t : Residual) (live : Finset Hyp) (b : Bool) : Finset Hyp :=
  live.filter (fun h => t.read h = b)

/-- How many live pairs the residual separates. -/
def splitCount (t : Residual) (live : Finset Hyp) : ℕ :=
  (live.filter (fun h => t.read h = true)).card *
    (live.filter (fun h => t.read h = false)).card

/-- The residual separates the live set. -/
def Separates (t : Residual) (live : Finset Hyp) : Prop :=
  ∃ a ∈ live, ∃ b ∈ live, t.read a ≠ t.read b

theorem separates_iff_splitCount_pos (t : Residual) (live : Finset Hyp) :
    Separates t live ↔ 0 < splitCount t live := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have key : ∀ x ∈ live, ∀ y ∈ live, t.read x = true → t.read y = false →
        0 < splitCount t live := by
      intro x hx y hy hxt hyf
      exact Nat.mul_pos (Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, hxt⟩⟩)
        (Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, hyf⟩⟩)
    rcases Bool.eq_false_or_eq_true (t.read a) with hA | hA
    · have hB : t.read b = false := by
        rcases Bool.eq_false_or_eq_true (t.read b) with hB | hB
        · exact absurd (hA.trans hB.symm) hab
        · exact hB
      exact key a ha b hb hA hB
    · have hB : t.read b = true := by
        rcases Bool.eq_false_or_eq_true (t.read b) with hB | hB
        · exact hB
        · exact absurd (hA.trans hB.symm) hab
      exact key b hb a ha hB hA
  · intro h
    rcases Nat.eq_zero_or_pos (live.filter (fun h => t.read h = true)).card with h1 | h1
    · simp [splitCount, h1] at h
    rcases Nat.eq_zero_or_pos (live.filter (fun h => t.read h = false)).card with h2 | h2
    · simp [splitCount, h2] at h
    obtain ⟨a, ha⟩ := Finset.card_pos.1 h1
    obtain ⟨b, hb⟩ := Finset.card_pos.1 h2
    rw [Finset.mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, by simp [ha.2, hb.2]⟩

/-! ## §2 Inert and salient residuals -/

theorem refineLive_subset (t : Residual) (live : Finset Hyp) (b : Bool) :
    refineLive t live b ⊆ live := Finset.filter_subset _ _

/-- **A residual all of whose live readings agree makes no progress**, however
large it is. -/
theorem constant_reading_no_progress {t : Residual} {live : Finset Hyp} {b : Bool}
    (h : ∀ x ∈ live, t.read x = b) : refineLive t live b = live :=
  Finset.filter_true_of_mem h

/-- **A separating residual strictly narrows the live set**, whatever it
returns. -/
theorem separating_strictly_narrows {t : Residual} {live : Finset Hyp}
    (hsep : Separates t live) (b : Bool) : refineLive t live b ⊂ live := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hsep
  refine (Finset.ssubset_iff_of_subset (refineLive_subset t live b)).2 ?_
  by_cases hxb : t.read x = b
  · exact ⟨y, hy, fun hmem => hxy (by rw [hxb, (Finset.mem_filter.1 hmem).2])⟩
  · exact ⟨x, hx, fun hmem => hxb (Finset.mem_filter.1 hmem).2⟩

/-! ## §3 Salience is neither magnitude nor cost -/

/-- All four hypotheses are live. -/
def allLive : Finset Hyp := Finset.univ

/-- A large, expensive residual that reads the same on every live hypothesis. -/
def inertResidual : Residual := ⟨fun _ => true, 100, 100⟩

/-- A residual with the same magnitude and the same cost that splits the live
set in half. -/
def salientResidual : Residual := ⟨fun h => decide (h.val < 2), 100, 100⟩

theorem inert_splitCount : splitCount inertResidual allLive = 0 := by decide

theorem salient_splitCount : splitCount salientResidual allLive = 4 := by decide

theorem inert_makes_no_progress : refineLive inertResidual allLive true = allLive := by decide

theorem salient_separates : Separates salientResidual allLive :=
  (separates_iff_splitCount_pos _ _).2 (by decide)

/-- **Priority by size and cost is not priority by salience.**  Two residuals
agree on magnitude and cost and differ in how much they separate the live
hypotheses. -/
theorem salience_does_not_descend_through_magnitude_and_cost :
    ¬ DescendsThrough (fun t : Residual => splitCount t allLive)
        (fun t : Residual => (t.magnitude, t.cost)) :=
  not_descendsThrough_of_collision (x := inertResidual) (y := salientResidual) rfl (by decide)

/-- **Salience is relative to what is still live.**  The very same residual is
maximally separating against one live set and inert against another. -/
theorem salience_is_live_set_relative :
    ¬ DescendsThrough (fun p : Residual × Finset Hyp => splitCount p.1 p.2)
        (fun p : Residual × Finset Hyp => p.1) :=
  not_descendsThrough_of_collision
    (x := (salientResidual, allLive)) (y := (salientResidual, ({0, 1} : Finset Hyp)))
    rfl (by decide)

/-- The pair is the right index. -/
theorem salience_descends_through_pair :
    DescendsThrough (fun p : Residual × Finset Hyp => splitCount p.1 p.2) id :=
  ⟨fun p => splitCount p.1 p.2, fun _ => rfl⟩

/-! ## §4 Two schedulers on the same queue -/

/-- Pick the candidate maximising a score. -/
def bestBy (score : Residual → ℕ) : List Residual → Option Residual
  | [] => none
  | t :: ts =>
      match bestBy score ts with
      | none => some t
      | some u => if score u > score t then some u else some t

/-- The salience-greedy scheduler. -/
def bestBySalience (live : Finset Hyp) (ts : List Residual) : Option Residual :=
  bestBy (fun t => splitCount t live) ts

/-- The magnitude-greedy scheduler. -/
def bestByMagnitude (ts : List Residual) : Option Residual :=
  bestBy (fun t => t.magnitude) ts

/-- A small, cheap residual that nevertheless splits the live set. -/
def smallSalientResidual : Residual := ⟨fun h => decide (h.val < 2), 1, 1⟩

/-- The queue: one big inert residual and one small separating one. -/
def queue : List Residual := [inertResidual, smallSalientResidual]

/-- **The salience scheduler picks the residual that makes progress; the
magnitude scheduler picks the inert one.**  On this queue the two schedulers
disagree, and only the salience choice strictly narrows the live set. -/
theorem salience_scheduler_beats_magnitude_scheduler :
    bestByMagnitude queue = some inertResidual ∧
      bestBySalience allLive queue = some smallSalientResidual ∧
        refineLive inertResidual allLive true = allLive ∧
          ∀ b, refineLive smallSalientResidual allLive b ⊂ allLive := by
  refine ⟨by decide, by decide, by decide, fun b => separating_strictly_narrows ?_ b⟩
  exact (separates_iff_splitCount_pos _ _).2 (by decide)

end Integration.Kernel.Welds.ResidualSalienceScheduler
