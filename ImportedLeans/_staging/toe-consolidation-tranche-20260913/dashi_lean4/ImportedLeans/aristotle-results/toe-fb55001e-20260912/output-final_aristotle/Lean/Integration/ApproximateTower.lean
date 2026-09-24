import Integration.MultiscaleDescent

/-!
# Approximate naturality along a whole tower

`Agda/DASHI/Core/ApproximateMultiscaleNaturality.agda` carries, for a multiscale
carrier: a metric at every level (`TowerMetric`, with `self-zero` and
`triangle`), an approximate kernel tower with a pointwise commutation error, an
embedding of exact towers as zero-error approximate ones, a **two-stage** error
accumulation, and a `ControlledErrorFamily` bounding the pointwise errors by a
per-level global bound.

That is the direct ancestor of the Lean owners `Integration.StructureMorphism`
and `Integration.MultiscaleDescent`, which were developed independently.  This
file records the genealogy by *re-proving the Agda content against the Lean
owners*, and generalising it:

* `towerMetric_axioms` — the two obligations of the Agda `TowerMetric` record
  hold for free in a pseudometric space, so the record is a specialisation of
  the Lean owner's hypotheses rather than new data;
* `commutationDefect`, `approxDescendsAt_iff_defect_le` — the Agda
  `commutationError` field is the defect of the Lean square;
* `exact_as_approximate` — the Agda `exact-as-approximate`, with the Lean
  proof: exact descent at every level is approximate descent at error zero;
* `accumulate_two_errors` — the Agda `accumulate-two-errors`, which in the Lean
  setting is the pseudometric triangle inequality;
* `approx_descends_projTo` — **the generalisation**: the Agda file accumulates
  two stages, and this accumulates all `n`, giving
  `dist (π_n (F₀ x)) (F_n (π_n x)) ≤ ∑_{k<n} ε k` along the whole tower;
* `approx_descends_of_globalBound` — the Agda `ControlledErrorFamily`
  conclusion: a uniform per-level bound `B` gives a total error `n · B`;
* `approx_descends_zero_of_exact` — the two extremes agree: zero total error at
  every level is exactly the exact tower.

Finally the honest boundary, on the existing `defectTower`:

* `defect_approx_at_one` — the level where the law provably has **no** effective
  counterpart nevertheless admits an approximate square at error `1`;
* `approximate_is_strictly_weaker` — so approximate descent at a finite error
  does not imply exact descent, and on this tower the error cannot be pushed
  below `1/2` by any choice of coarse law.

No physical system is claimed to realise any tower here.
-/

namespace Integration.ApproximateTower

open Integration.MultiscaleDescent
open Integration.MultiscaleDescent.LawTower
open Integration.ApproximateIntertwiner
open Integration.StructureMorphism

/-! ## The Agda `TowerMetric` obligations -/

/-- The two fields the Agda `TowerMetric` record must supply — `self-zero` and
`triangle` — are theorems in a pseudometric space.  The Agda record is therefore
a hand-rolled instance of the structure the Lean owner already assumes. -/
theorem towerMetric_axioms (L : Type*) [PseudoMetricSpace L] :
    (∀ x : L, dist x x = 0) ∧ ∀ x y z : L, dist x z ≤ dist x y + dist y z :=
  ⟨dist_self, dist_triangle⟩

/-! ## The commutation defect -/

variable (T : LawTower)

/-- The Agda `commutationError` at a point: how far the square at level `k`
fails to commute. -/
def commutationDefect (k : ℕ) [PseudoMetricSpace (T.Layer (k + 1))] (x : T.Layer k) : ℝ :=
  dist (T.step k (T.law k x)) (T.law (k + 1) (T.step k x))

/-- Approximate descent is exactly a bound on the defect. -/
theorem approxDescendsAt_iff_defect_le (k : ℕ) [PseudoMetricSpace (T.Layer (k + 1))]
    (ε : ℝ) : T.ApproxDescendsAt k ε ↔ ∀ x, commutationDefect T k x ≤ ε := Iff.rfl

/-- Zero defect at a point is commutation at that point. -/
theorem defect_eq_zero_iff (k : ℕ) [MetricSpace (T.Layer (k + 1))] (x : T.Layer k) :
    commutationDefect T k x = 0 ↔ T.step k (T.law k x) = T.law (k + 1) (T.step k x) :=
  dist_eq_zero

/-- **`exact-as-approximate`.**  Exact descent at a level is approximate descent
at error zero. -/
theorem exact_as_approximate (k : ℕ) [PseudoMetricSpace (T.Layer (k + 1))]
    (h : T.DescendsAt k) : T.ApproxDescendsAt k 0 :=
  approx_of_exact h

/-- **`accumulate-two-errors`.**  In the Lean setting the Agda lemma is the
triangle inequality; it is recorded here under its Agda name so the genealogy is
explicit. -/
theorem accumulate_two_errors {L : Type*} [PseudoMetricSpace L] (x y z : L) {e₁ e₂ : ℝ}
    (hxy : dist x y ≤ e₁) (hyz : dist y z ≤ e₂) : dist x z ≤ e₁ + e₂ :=
  le_trans (dist_triangle x y z) (add_le_add hxy hyz)

/-! ## The generalisation: all `n` stages -/

variable [inst : ∀ k, PseudoMetricSpace (T.Layer k)]

/-- **Errors accumulate along the whole tower.**  If the law descends at each
level up to `ε k`, and every coarsening is nonexpansive, then the composite
coarsening to level `n` intertwines the fine law with the level-`n` law up to
the sum of the errors below `n`.  The Agda ancestor proves the case `n = 2`. -/
theorem approx_descends_projTo
    (hne : ∀ k, ∀ a b : T.Layer k, dist (T.step k a) (T.step k b) ≤ dist a b)
    (ε : ℕ → ℝ) (hε : ∀ k, T.ApproxDescendsAt k (ε k)) (n : ℕ) :
    IsApproxIntertwiner (T.projTo n) (T.law 0) (T.law n) (∑ k ∈ Finset.range n, ε k) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    have hcomp := approx_comp (Φ₁ := T.projTo n) (Φ₂ := T.step n) ih (hε n) (hne n)
    rw [Finset.sum_range_succ]
    exact hcomp

/-- **The `ControlledErrorFamily` conclusion.**  A uniform per-level bound gives
a linear total bound. -/
theorem approx_descends_of_globalBound
    (hne : ∀ k, ∀ a b : T.Layer k, dist (T.step k a) (T.step k b) ≤ dist a b)
    (ε : ℕ → ℝ) (hε : ∀ k, T.ApproxDescendsAt k (ε k)) (B : ℝ) (hB : ∀ k, ε k ≤ B) (n : ℕ) :
    IsApproxIntertwiner (T.projTo n) (T.law 0) (T.law n) (n * B) := by
  intro x
  refine le_trans (approx_descends_projTo T hne ε hε n x) ?_
  calc ∑ k ∈ Finset.range n, ε k ≤ ∑ _k ∈ Finset.range n, B :=
        Finset.sum_le_sum fun k _ => hB k
    _ = n * B := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **The two extremes agree.**  Exact descent at every level below `n` gives
total error zero, which is the exact square again. -/
theorem approx_descends_zero_of_exact
    (hne : ∀ k, ∀ a b : T.Layer k, dist (T.step k a) (T.step k b) ≤ dist a b)
    (h : ∀ k, T.DescendsAt k) (n : ℕ) :
    IsApproxIntertwiner (T.projTo n) (T.law 0) (T.law n) 0 ∧
      Exact (T.projTo n) (T.law 0) (T.law n) := by
  have hex : Exact (T.projTo n) (T.law 0) (T.law n) :=
    T.descends_projTo fun j _ => h j
  refine ⟨?_, hex⟩
  have := approx_descends_projTo T hne (fun _ => 0) (fun k => exact_as_approximate T k (h k)) n
  simpa using this

/-! ## The boundary: approximate is strictly weaker than exact -/

/-- On the tower where the law provably has no effective coarse counterpart,
there is nevertheless an approximate square at error `1`: the readout takes only
the values `0` and `1`, so the identity is a coarse law with defect at most
one. -/
theorem defect_approx_at_one : IsApproxIntertwiner coarse swap2 id 1 := by
  intro x
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> simp [coarse, swap2, Real.dist_eq]

/-- **Approximate descent is strictly weaker than exact descent.**  At the same
level: an approximate square at error `1` exists, no exact effective law exists
at all, and every candidate coarse law has defect at least `1/2` somewhere.  So
the approximate tier is a genuine intermediate certificate, and its error here
cannot be improved past `1/2`. -/
theorem approximate_is_strictly_weaker :
    IsApproxIntertwiner coarse swap2 id 1 ∧
      defectTower.NoEffectiveLaw 1 ∧
      ∀ F : ℝ → ℝ, ∃ x : Bool × Bool, (1 : ℝ) / 2 ≤ |coarse (swap2 x) - F (coarse x)| :=
  ⟨defect_approx_at_one, defect_no_effective_law_at_one, defect_lower_bound⟩

end Integration.ApproximateTower
