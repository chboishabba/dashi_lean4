import Integration.StructuredObserver

/-!
# Exact, approximate, and unverified intertwiners

A recurring shape in this corpus is a commuting square

```
      X --R--> X
      |        |
      Φ        Φ
      v        v
      Y --T--> Y
```

with `Φ ∘ R = T ∘ Φ`.  Exact squares are the strong statement; but between an
exact square and a mere analogy there is a useful middle tier: a **certified
approximate** square, where the two composites are within a stated distance of
each other.  This file owns that tier.

* `IsIntertwiner Φ R T` — the exact square;
* `IsApproxIntertwiner Φ R T ε` — `dist (Φ (R x)) (T (Φ x)) ≤ ε` at every point;
* `approx_of_exact`, `exact_of_approx_zero` — the exact tier sits inside the
  approximate one, at error zero, and conversely error zero is exactness;
* `approx_comp` — **composition with additive error**: two approximate squares
  stacked, with a nonexpansive downstream comparison map, give an approximate
  square with error `ε₁ + ε₂`;
* `approx_iterate` — iterating one approximate square `n` times, with a
  nonexpansive `T`, gives error `n · ε`;
* `certificate_intertwiner` — the welded observer supplies an exact instance: its
  transverse certificate is an exact intertwiner between the symmetry action
  upstairs and the identity on `ℝ`, hence a certified approximate one at every
  error.

The point of the file is bookkeeping honesty: a claim of the form "these two
structures are related by a square" can now be filed as exact, as approximate
with an explicit bound, or as neither.
-/

namespace Integration.ApproximateIntertwiner

variable {X Y Z : Type*}

/-- The exact commuting square `Φ ∘ R = T ∘ Φ`. -/
def IsIntertwiner (Φ : X → Y) (R : X → X) (T : Y → Y) : Prop := ∀ x, Φ (R x) = T (Φ x)

variable [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- The square commutes up to `ε`. -/
def IsApproxIntertwiner (Φ : X → Y) (R : X → X) (T : Y → Y) (ε : ℝ) : Prop :=
  ∀ x, dist (Φ (R x)) (T (Φ x)) ≤ ε

/-- **Exact implies certified approximate**, at error zero. -/
theorem approx_of_exact {Φ : X → Y} {R : X → X} {T : Y → Y} (h : IsIntertwiner Φ R T) :
    IsApproxIntertwiner Φ R T 0 := fun x => by rw [h x, dist_self]

/-- Every exact square is approximate at any nonnegative error. -/
theorem approx_of_exact_le {Φ : X → Y} {R : X → X} {T : Y → Y} {ε : ℝ} (hε : 0 ≤ ε)
    (h : IsIntertwiner Φ R T) : IsApproxIntertwiner Φ R T ε := fun x => by rw [h x, dist_self]; exact hε

/-- In a metric space, error zero is exactness. -/
theorem exact_of_approx_zero {Y' : Type*} [MetricSpace Y'] {Φ : X → Y'} {R : X → X}
    {T : Y' → Y'} (h : IsApproxIntertwiner Φ R T 0) : IsIntertwiner Φ R T := fun x =>
  dist_le_zero.mp (h x)

/-- **Composition with additive error.**  If `Φ₁` intertwines `R` with `S` up to
`ε₁`, `Φ₂` intertwines `S` with `T` up to `ε₂`, and `Φ₂` is nonexpansive, then
`Φ₂ ∘ Φ₁` intertwines `R` with `T` up to `ε₁ + ε₂`. -/
theorem approx_comp {Φ₁ : X → Y} {Φ₂ : Y → Z} {R : X → X} {S : Y → Y} {T : Z → Z}
    {ε₁ ε₂ : ℝ} (h₁ : IsApproxIntertwiner Φ₁ R S ε₁) (h₂ : IsApproxIntertwiner Φ₂ S T ε₂)
    (hne : ∀ a b : Y, dist (Φ₂ a) (Φ₂ b) ≤ dist a b) :
    IsApproxIntertwiner (Φ₂ ∘ Φ₁) R T (ε₁ + ε₂) := by
  intro x
  have hstep : dist (Φ₂ (Φ₁ (R x))) (Φ₂ (S (Φ₁ x))) ≤ ε₁ :=
    le_trans (hne _ _) (h₁ x)
  have htail : dist (Φ₂ (S (Φ₁ x))) (T (Φ₂ (Φ₁ x))) ≤ ε₂ := h₂ (Φ₁ x)
  calc dist ((Φ₂ ∘ Φ₁) (R x)) (T ((Φ₂ ∘ Φ₁) x))
      ≤ dist (Φ₂ (Φ₁ (R x))) (Φ₂ (S (Φ₁ x))) + dist (Φ₂ (S (Φ₁ x))) (T (Φ₂ (Φ₁ x))) :=
        dist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hstep htail

/-- **Iteration with additive error.**  Running an approximate square `n` times,
with a nonexpansive `T`, accumulates at most `n · ε`. -/
theorem approx_iterate {Φ : X → Y} {R : X → X} {T : Y → Y} {ε : ℝ}
    (h : IsApproxIntertwiner Φ R T ε) (hne : ∀ a b : Y, dist (T a) (T b) ≤ dist a b) (n : ℕ)
    (x : X) : dist (Φ (R^[n] x)) (T^[n] (Φ x)) ≤ n * ε := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hR : R^[n + 1] x = R^[n] (R x) := Function.iterate_succ_apply R n x
    have hT : T^[n + 1] (Φ x) = T^[n] (T (Φ x)) := Function.iterate_succ_apply T n (Φ x)
    have hstep : dist (T^[n] (Φ (R x))) (T^[n] (T (Φ x))) ≤ ε := by
      have hIter : ∀ m : ℕ, ∀ a b : Y, dist (T^[m] a) (T^[m] b) ≤ dist a b := by
        intro m
        induction m with
        | zero => intro a b; simp
        | succ m ihm =>
          intro a b
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          exact le_trans (ihm (T a) (T b)) (hne a b)
      exact le_trans (hIter n (Φ (R x)) (T (Φ x))) (h x)
    rw [hR, hT]
    calc dist (Φ (R^[n] (R x))) (T^[n] (T (Φ x)))
        ≤ dist (Φ (R^[n] (R x))) (T^[n] (Φ (R x)))
            + dist (T^[n] (Φ (R x))) (T^[n] (T (Φ x))) := dist_triangle _ _ _
      _ ≤ n * ε + ε := add_le_add (ih (R x)) hstep
      _ = (n + 1 : ℕ) * ε := by push_cast; ring

/-! ## An exact instance from the weld -/

open Integration.StructuredObserver

/-- **The welded certificate is an exact intertwiner.**  For a symmetry-resolved
observer the square

```
   Rich --g·(-)--> Rich
     |               |
    cert            cert
     v               v
     ℝ  ---id--->    ℝ
```

commutes exactly, because the certificate is symmetry invariant. -/
theorem certificate_intertwiner {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    (O : SymmetryResolvedObserver G Rich Coarse Res n) (g : G) :
    IsIntertwiner O.nondegeneracy (O.reduction.actRich g) id :=
  fun x => O.nondegeneracy_invariant g x

/-- Hence it is a certified approximate intertwiner at error zero. -/
theorem certificate_approx {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    (O : SymmetryResolvedObserver G Rich Coarse Res n) (g : G) :
    IsApproxIntertwiner O.nondegeneracy (O.reduction.actRich g) id 0 :=
  approx_of_exact (certificate_intertwiner O g)

end Integration.ApproximateIntertwiner
