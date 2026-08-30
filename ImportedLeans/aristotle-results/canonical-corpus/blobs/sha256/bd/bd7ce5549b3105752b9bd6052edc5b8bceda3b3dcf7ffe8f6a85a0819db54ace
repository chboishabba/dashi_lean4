import Integration.StructureMorphism
import Integration.DescentLevel

/-!
# Multiscale law descent

A tower of successively coarser descriptions

```
X₀ ──π₀──▶ X₁ ──π₁──▶ X₂ ──▶ ⋯
```

carries not only states but *laws*: an operator `F_k` on each level.  The
question this file owns is whether the fine law has an effective counterpart at
each level, i.e. whether

```
π_k ∘ F_k = F_{k+1} ∘ π_k
```

holds exactly, only to within a stated error, or not at all.  The three answers
are exactly the three tiers of `Integration.StructureMorphism`, applied level by
level.

Contents.

* `LawTower` — carriers, coarsenings, and a law on each level;
* `DescendsAt`, `descendsAt_iff_exact` — descent at one level *is* the exact
  commuting square, so all of the transport theory applies;
* `descends_projTo` — descent at every level below `k` composes: the fine law is
  then intertwined with the level-`k` law along the whole composite, and finite
  trajectories transport (`trajectory_descends`);
* `ApproxDescendsAt` and `approx_descends_two` — the certified-approximate tier,
  with the errors adding along the tower (via
  `Integration.ApproximateIntertwiner.approx_comp`);
* `NoEffectiveLaw` — the strongest negative: not merely that a *chosen* coarse
  operator fails, but that **no** operator on the coarse level makes the square
  commute.  This is the honest statement of "the law does not descend";
* `defectTower`, `defect_descends_at_zero`, `defect_no_effective_law_at_one` —
  a three-level instance where the law descends exactly at the first coarsening
  and provably has no effective counterpart at the second;
* `defect_lower_bound` — and the quantitative version: at that level *every*
  candidate effective law has commuting defect at least `1/2` somewhere, so the
  failure is not repairable by a better choice, only by keeping more resolution.

No physical system is claimed to realise this tower; the instance is four
states, two coarsenings and a real-valued readout.
-/

namespace Integration.MultiscaleDescent

open Integration.StructureMorphism
open Integration.ApproximateIntertwiner

/-! ## Towers with laws -/

/-- A tower of successively coarser carriers, each carrying its own law. -/
structure LawTower where
  /-- The carrier at each level; level `0` is the finest. -/
  Layer : ℕ → Type
  /-- The coarsening from one level to the next. -/
  step : ∀ k, Layer k → Layer (k + 1)
  /-- The law at each level. -/
  law : ∀ k, Layer k → Layer k

namespace LawTower

/-- The composite coarsening from the finest level to level `k`. -/
def projTo (T : LawTower) : (k : ℕ) → (T.Layer 0 → T.Layer k)
  | 0 => id
  | k + 1 => fun x => T.step k (projTo T k x)

@[simp] theorem projTo_zero (T : LawTower) (x : T.Layer 0) : T.projTo 0 x = x := rfl

@[simp] theorem projTo_succ (T : LawTower) (k : ℕ) (x : T.Layer 0) :
    T.projTo (k + 1) x = T.step k (T.projTo k x) := rfl

/-- **The law descends at level `k`** when the coarsening intertwines the two
laws. -/
def DescendsAt (T : LawTower) (k : ℕ) : Prop :=
  ∀ x, T.step k (T.law k x) = T.law (k + 1) (T.step k x)

/-- Descent at a level is exactly the exact commuting square. -/
theorem descendsAt_iff_exact (T : LawTower) (k : ℕ) :
    T.DescendsAt k ↔ Exact (T.step k) (T.law k) (T.law (k + 1)) := Iff.rfl

/-- **Descent composes.**  If the law descends at every level below `k` then the
fine law is intertwined with the level-`k` law along the whole composite. -/
theorem descends_projTo (T : LawTower) {k : ℕ} (h : ∀ j, j < k → T.DescendsAt j) :
    Exact (T.projTo k) (T.law 0) (T.law k) := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    have hk : ∀ j, j < k → T.DescendsAt j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    intro x
    show T.step k (T.projTo k (T.law 0 x)) = T.law (k + 1) (T.step k (T.projTo k x))
    rw [ih hk x, h k (Nat.lt_succ_self k) (T.projTo k x)]

/-- And then finite trajectories transport to every such level. -/
theorem trajectory_descends (T : LawTower) {k : ℕ} (h : ∀ j, j < k → T.DescendsAt j)
    (n : ℕ) (x : T.Layer 0) :
    T.projTo k ((T.law 0)^[n] x) = (T.law k)^[n] (T.projTo k x) :=
  exact_iterate (T.descends_projTo h) n x

/-- The certified-approximate tier at one level. -/
def ApproxDescendsAt (T : LawTower) (k : ℕ) [PseudoMetricSpace (T.Layer (k + 1))]
    (ε : ℝ) : Prop :=
  IsApproxIntertwiner (T.step k) (T.law k) (T.law (k + 1)) ε

/-- **The strongest negative.**  No operator at all on the coarse level makes the
square commute: the failure is a property of the coarsening, not of a bad
choice. -/
def NoEffectiveLaw (T : LawTower) (k : ℕ) : Prop :=
  ¬ ∃ F : T.Layer (k + 1) → T.Layer (k + 1), ∀ x, T.step k (T.law k x) = F (T.step k x)

end LawTower

/-! ## Errors add along the tower -/

open LawTower

/-- Two approximate levels compose with additive error, provided the second
coarsening is nonexpansive.  This is the tower form of
`Integration.ApproximateIntertwiner.approx_comp`. -/
theorem approx_descends_two (T : LawTower) [PseudoMetricSpace (T.Layer 1)]
    [PseudoMetricSpace (T.Layer 2)] {ε₀ ε₁ : ℝ}
    (h₀ : T.ApproxDescendsAt 0 ε₀) (h₁ : T.ApproxDescendsAt 1 ε₁)
    (hne : ∀ a b : T.Layer 1, dist (T.step 1 a) (T.step 1 b) ≤ dist a b) :
    IsApproxIntertwiner (T.step 1 ∘ T.step 0) (T.law 0) (T.law 2) (ε₀ + ε₁) :=
  approx_comp h₀ h₁ hne

/-! ## A three-level instance -/

/-- The exchange of the two coordinates: the law at levels zero and one. -/
def swap2 (p : Bool × Bool) : Bool × Bool := (p.2, p.1)

/-- The second coarsening: a real readout of the first coordinate only. -/
def coarse (p : Bool × Bool) : ℝ := if p.1 then 1 else 0

/-- Level 0 and level 1 are the four-state carrier; level 2 is the real readout
of its first coordinate. -/
def defectTower : LawTower where
  Layer
    | 0 => Bool × Bool
    | 1 => Bool × Bool
    | 2 => ℝ
    | _ + 3 => PUnit
  step
    | 0 => id
    | 1 => coarse
    | 2 => fun _ => PUnit.unit
    | _ + 3 => fun _ => PUnit.unit
  law
    | 0 => swap2
    | 1 => swap2
    | 2 => id
    | _ + 3 => id

/-- **The law descends exactly at the first coarsening.** -/
theorem defect_descends_at_zero : defectTower.DescendsAt 0 := fun _ => rfl

/-- **And has no effective counterpart at the second.**  No function of the
first-coordinate readout can reproduce the exchange of coordinates. -/
theorem defect_no_effective_law_at_one : defectTower.NoEffectiveLaw 1 := by
  rintro ⟨F, hF⟩
  have h1 : coarse (swap2 (false, true)) = F (coarse (false, true)) := hF (false, true)
  have h2 : coarse (swap2 (false, false)) = F (coarse (false, false)) := hF (false, false)
  simp only [coarse, swap2] at h1 h2
  norm_num at h1 h2
  exact absurd (h1.trans h2.symm) (by norm_num)

/-- **The quantitative version.**  Every candidate effective law at that level
has commuting defect at least `1/2` somewhere: keeping less resolution cannot be
repaired by choosing a better coarse operator. -/
theorem defect_lower_bound (F : ℝ → ℝ) :
    ∃ x : Bool × Bool, (1 : ℝ) / 2 ≤ |coarse (swap2 x) - F (coarse x)| := by
  by_contra hcon
  push_neg at hcon
  have h1 := hcon (false, true)
  have h2 := hcon (false, false)
  simp only [coarse, swap2] at h1 h2
  norm_num [abs_lt] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

end Integration.MultiscaleDescent
