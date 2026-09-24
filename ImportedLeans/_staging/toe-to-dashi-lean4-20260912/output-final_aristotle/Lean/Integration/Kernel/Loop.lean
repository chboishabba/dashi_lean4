import Integration.Kernel.Reopen

/-!
# The closed loop: probe, refine, merge — and why it terminates

Sixth component of the shared kernel.  The previous files supply the pieces;
this one runs them as a dynamical system and proves the two things a search
loop has to guarantee: it never loses the truth, and it stops.

## The loop

A `Policy` chooses, for the current residual fibre, which channel to probe.
Against the actual world `w`:

```
step P w F = refine F (P.choose F) ((P.choose F).read w),      run P w F (n+1) = step P w (run P w F n).
```

* `step_refines`, `run_antitone`, `run_refines` — the fibre is monotone
  decreasing along the run: **narrowing is never undone**.
* `truth_mem_run` — an honest loop never discards the actual world, at any
  depth.
* `step_strict_of_discriminates` — a probe that discriminates on the current
  fibre strictly narrows it, whatever it happens to return.

## Termination

`Responsive P c` : whenever the fibre still carries a consumer collision, the
policy picks a channel that discriminates on it.  Then, over a finite
possibility space:

* `responsive_run_card` — `ncard (run n) + n ≤ ncard F` for as long as
  collisions persist;
* `responsive_policy_closes` — **within `ncard F` turns the consumer's question
  is determined, on a fibre that still contains the truth.**

The two negatives that keep this honest:

* `closure_is_consumer_relative` — the loop closes the *consumer's* coordinate,
  and can halt with another coordinate wide open;
* `unresponsive_policy_never_closes` — with a policy that keeps choosing a
  constant channel, the loop runs for ever without progress, so responsiveness
  is load-bearing rather than decorative.

## The outcome-adaptive strategy (`§4`)

The branch rule *global-sensitive → refine; local & inherited → merge;
local & introduced → refine* is encoded as `strategy` and characterised:
`strategy_merges_iff` — a merge is admitted exactly on a local probe with
inherited provenance.

## Composition with the merge layer (`§5`)

`branches_merge_refines` and `merge_preserves_truth_of_runs`: two runs from the
same base, reconciled three-way, still refine the base and still contain the
truth.

**Claim boundary.** A "policy" is an arbitrary function from fibres to
channels; nothing here says a policy is computable, cheap or admissible — cost
and admissibility are separate obligations.
-/

namespace Integration.Kernel.Loop

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Probe

variable {Ω Y C : Type*}

/-! ## §1 The loop -/

/-- A search policy: which channel to probe at the current residual fibre. -/
structure Policy (Ω Y : Type*) where
  /-- The channel chosen at a fibre. -/
  choose : Set Ω → Channel Ω Y

/-- One turn of the loop against the actual world `w`. -/
def step (P : Policy Ω Y) (w : Ω) (F : Set Ω) : Set Ω :=
  refine F (P.choose F) ((P.choose F).read w)

/-- `n` turns of the loop. -/
def run (P : Policy Ω Y) (w : Ω) (F : Set Ω) : ℕ → Set Ω
  | 0 => F
  | n + 1 => step P w (run P w F n)

@[simp] theorem run_zero (P : Policy Ω Y) (w : Ω) (F : Set Ω) : run P w F 0 = F := rfl

@[simp] theorem run_succ (P : Policy Ω Y) (w : Ω) (F : Set Ω) (n : ℕ) :
    run P w F (n + 1) = step P w (run P w F n) := rfl

theorem step_refines (P : Policy Ω Y) (w : Ω) (F : Set Ω) : Refines (step P w F) F :=
  refine_refines _ _ _

theorem run_succ_refines (P : Policy Ω Y) (w : Ω) (F : Set Ω) (n : ℕ) :
    Refines (run P w F (n + 1)) (run P w F n) := step_refines _ _ _

theorem run_antitone (P : Policy Ω Y) (w : Ω) (F : Set Ω) {m n : ℕ} (h : m ≤ n) :
    Refines (run P w F n) (run P w F m) := by
  induction n with
  | zero => obtain rfl : m = 0 := Nat.le_zero.1 h; exact refines_refl _
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hlt | rfl
      · exact refines_trans (run_succ_refines P w F n) (ih (Nat.lt_succ_iff.1 hlt))
      · exact refines_refl _

theorem run_refines (P : Policy Ω Y) (w : Ω) (F : Set Ω) (n : ℕ) :
    Refines (run P w F n) F := run_antitone P w F (Nat.zero_le n)

/-- An honest loop never discards the actual world. -/
theorem truth_mem_run {P : Policy Ω Y} {w : Ω} {F : Set Ω} (hw : w ∈ F) (n : ℕ) :
    w ∈ run P w F n := by
  induction n with
  | zero => exact hw
  | succ n ih => exact ⟨ih, rfl⟩

theorem run_nonempty {P : Policy Ω Y} {w : Ω} {F : Set Ω} (hw : w ∈ F) (n : ℕ) :
    (run P w F n).Nonempty := ⟨w, truth_mem_run hw n⟩

/-- A discriminating probe strictly narrows the fibre, whatever it returns. -/
theorem step_strict_of_discriminates {P : Policy Ω Y} {w : Ω} {F : Set Ω}
    (hd : Discriminates (P.choose F) F) : step P w F ⊂ F := by
  obtain ⟨a, ha, b, hb, hab⟩ := hd
  refine ⟨step_refines P w F, fun hsub => ?_⟩
  rcases eq_or_ne ((P.choose F).read a) ((P.choose F).read w) with hA | hA
  · exact hab (hA.trans (hsub hb).2.symm)
  · exact hA (hsub ha).2

/-! ## §2 Termination for a responsive policy -/

/-- The policy always answers a live consumer collision with a discriminating probe. -/
def Responsive (P : Policy Ω Y) (c : Ω → C) : Prop :=
  ∀ F : Set Ω, Collision F c → Discriminates (P.choose F) F

section Finite

variable [Finite Ω]

theorem responsive_run_card {P : Policy Ω Y} {c : Ω → C} (hP : Responsive P c) (w : Ω)
    (F : Set Ω) :
    ∀ n : ℕ, (∀ k < n, Collision (run P w F k) c) → (run P w F n).ncard + n ≤ F.ncard := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hcol
      have hprev : (run P w F n).ncard + n ≤ F.ncard :=
        ih fun k hk => hcol k (Nat.lt_succ_of_lt hk)
      have hd : Discriminates (P.choose (run P w F n)) (run P w F n) :=
        hP _ (hcol n (Nat.lt_succ_self n))
      have hstrict : run P w F (n + 1) ⊂ run P w F n := step_strict_of_discriminates hd
      have hlt : (run P w F (n + 1)).ncard < (run P w F n).ncard :=
        Set.ncard_lt_ncard hstrict (Set.toFinite _)
      omega

/-- **The loop closes.**  A responsive policy determines the consumer coordinate
within `ncard F` turns, on a fibre that still contains the actual world. -/
theorem responsive_policy_closes {P : Policy Ω Y} {c : Ω → C} (hP : Responsive P c) {w : Ω}
    {F : Set Ω} (hw : w ∈ F) :
    ∃ n ≤ F.ncard, Determines (run P w F n) c ∧ w ∈ run P w F n := by
  by_contra hcon
  push_neg at hcon
  have hcol : ∀ k ≤ F.ncard, Collision (run P w F k) c := by
    intro k hk
    by_contra hno
    exact absurd (truth_mem_run hw k)
      (hcon k hk ((determines_iff_not_collision (run_nonempty hw k)).2 hno))
  have hcard := responsive_run_card hP w F F.ncard fun k hk => hcol k (le_of_lt hk)
  have hpos : 0 < (run P w F F.ncard).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 (run_nonempty hw _)
  omega

end Finite

/-! ## §3 The two negatives -/

/-- Closure is **consumer-relative**: the loop can determine what the consumer
asked for while another coordinate stays wide open. -/
theorem closure_is_consumer_relative :
    ∃ (F : Set (Bool × Bool)) (c d : Bool × Bool → Bool),
      Determines F c ∧ ¬ Determines F d := by
  refine ⟨{w | w.1 = true}, Prod.fst, Prod.snd, ⟨true, fun w hw => hw⟩, ?_⟩
  rintro ⟨v, hv⟩
  have h1 : ((true, true) : Bool × Bool).2 = v := hv _ rfl
  have h2 : ((true, false) : Bool × Bool).2 = v := hv _ rfl
  rw [← h2] at h1
  exact Bool.noConfusion h1

/-- **Responsiveness is load-bearing.**  A policy that always picks a constant
channel leaves the fibre — and the collision — untouched for ever. -/
theorem unresponsive_policy_never_closes :
    ∃ (P : Policy (Bool × Bool) Unit) (w : Bool × Bool) (F : Set (Bool × Bool))
      (c : Bool × Bool → Bool),
      ∀ n, run P w F n = F ∧ Collision (run P w F n) c := by
  refine ⟨⟨fun _ => ⟨fun _ => ()⟩⟩, (true, true), univ, Prod.fst, fun n => ?_⟩
  have hrun : ∀ n, run (⟨fun _ => ⟨fun _ => ()⟩⟩ : Policy (Bool × Bool) Unit) (true, true)
      univ n = univ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ext x; simp [step, refine, refineBy, event, ih]
  exact ⟨hrun n, by
    rw [hrun n]
    exact ⟨(true, true), mem_univ _, (false, true), mem_univ _, by simp⟩⟩

/-! ## §4 The outcome-adaptive branch rule -/

/-- How far a probe's dependency reaches. -/
inductive Sensitivity
  /-- The probe's dependency is global. -/
  | globalSensitive
  /-- The probe's dependency is local. -/
  | localOnly
  deriving DecidableEq, Repr

/-- What the loop does next. -/
inductive Move
  /-- Narrow the hypothesis fibre further. -/
  | refineMove
  /-- Merge the discovery. -/
  | mergeMove
  deriving DecidableEq, Repr

open Integration.Kernel.Reopen (Origin)

/-- The adaptive rule: global-sensitive ⇒ refine; local & inherited ⇒ merge;
local & introduced ⇒ refine. -/
def strategy : Sensitivity → Origin → Move
  | .globalSensitive, _ => .refineMove
  | .localOnly, .inherited => .mergeMove
  | .localOnly, .introduced => .refineMove

/-- A merge is admitted exactly on a local probe with inherited provenance. -/
theorem strategy_merges_iff (s : Sensitivity) (o : Origin) :
    strategy s o = .mergeMove ↔ s = .localOnly ∧ o = .inherited := by
  cases s <;> cases o <;> simp [strategy]

/-- Provenance alone does not decide the move: with a global-sensitive probe an
inherited coordinate is still refined rather than merged. -/
theorem strategy_needs_both_coordinates :
    strategy .globalSensitive .inherited ≠ strategy .localOnly .inherited := by decide

/-! ## §5 Composition with the merge layer -/

theorem branches_merge_refines (P₁ P₂ : Policy Ω Y) (w : Ω) (F : Set Ω) (n₁ n₂ : ℕ) :
    Refines (Integration.Kernel.Merge.threeWay (run P₁ w F n₁) (run P₂ w F n₂)) F :=
  Integration.Kernel.Merge.threeWay_refines_base (run_refines P₁ w F n₁)

theorem merge_preserves_truth_of_runs {P₁ P₂ : Policy Ω Y} {w : Ω} {F : Set Ω} (hw : w ∈ F)
    (n₁ n₂ : ℕ) :
    w ∈ Integration.Kernel.Merge.threeWay (run P₁ w F n₁) (run P₂ w F n₂) :=
  ⟨truth_mem_run hw n₁, truth_mem_run hw n₂⟩

end Integration.Kernel.Loop
