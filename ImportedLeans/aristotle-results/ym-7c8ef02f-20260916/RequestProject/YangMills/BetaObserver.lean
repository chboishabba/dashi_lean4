/-
# Row A1b — the literal beta-observer contraction package

The Row A1 history remainder is controlled by three data attached to the
renormalisation-group step `T` acting on the physical small-field tube:

* a *source observer* `O : K → X` which keeps only the coordinates the shell
  coefficient actually depends on, and which intertwines the full RG step `TK`
  with the observed step `T`:  `O ∘ TK = T ∘ O`  (the factorisation square);
* a contraction constant `κ` for `T` in the observer metric;
* a Lipschitz constant `L` for the shell coefficient `β : X → ℝ`.

This file proves, with no assumption beyond those three:

* `observer_square_iterate` — the factorisation square propagates to all
  iterates, so the observed history *is* the history of the observation (this is
  the "same object" audit, in theorem form rather than as a field match);
* `dist_iterate_fixedPoint_le` — geometric approach to the fixed point;
* `historyRemainder_bound` — the uniform history budget
  `|R_hist| ≤ L · γ · B` with `γ = 1/(1−κ)`, uniformly in the number of shells,
  hence cutoff-, volume- and scale-independent;
* `historyRemainder_bound_of_products` — the fallback when pointwise `κ < 1`
  fails but the response products `∏_{r<n} κ_r` are summable;
* `kappa_one_no_finite_budget` — the adversarial test at `κ = 1`: for the
  isometry `x ↦ x+1` on `ℝ` with `β = id` (Lipschitz with `L = 1`, `κ = 1`
  exactly) the history sums are unbounded, so at `κ = 1` the geometric budget
  genuinely fails rather than producing a fake finite `B`.
-/
import Mathlib

namespace YangMills

open Finset

variable {X : Type*} [PseudoMetricSpace X]

/-! ## 1. The three data -/

/-- `T` contracts the observer metric with factor `κ`. -/
def IsObserverContraction (T : X → X) (κ : ℝ) : Prop :=
  ∀ x y, dist (T x) (T y) ≤ κ * dist x y

/-- The shell coefficient `β` is Lipschitz on the observer coordinates. -/
def IsBetaLipschitz (β : X → ℝ) (L : ℝ) : Prop :=
  ∀ x y, |β x - β y| ≤ L * dist x y

/-- The observer factorisation square: the observed step is the observation of
the step. -/
def IsObserverSquare {K : Type*} (O : K → X) (TK : K → K) (T : X → X) : Prop :=
  ∀ k, O (TK k) = T (O k)

/-! ## 2. Same-object audit: the square propagates to all iterates -/

omit [PseudoMetricSpace X] in
theorem observer_square_iterate {K : Type*} {O : K → X} {TK : K → K} {T : X → X}
    (h : IsObserverSquare O TK T) (k : K) : ∀ n : ℕ, O (TK^[n] k) = T^[n] (O k) := by
  intro n
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (TK k), h k]

/-! ## 3. Geometric approach to the fixed point -/

theorem dist_iterate_fixedPoint_le {T : X → X} {κ : ℝ} (hκ : 0 ≤ κ)
    (hT : IsObserverContraction T κ) {xs : X} (hfix : T xs = xs) (x : X) :
    ∀ n : ℕ, dist (T^[n] x) xs ≤ κ ^ n * dist x xs := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : dist (T^[n+1] x) xs = dist (T (T^[n] x)) (T xs) := by
        rw [Function.iterate_succ_apply', hfix]
      have h2 : dist (T (T^[n] x)) (T xs) ≤ κ * dist (T^[n] x) xs := hT _ _
      have h3 : κ * dist (T^[n] x) xs ≤ κ * (κ ^ n * dist x xs) :=
        mul_le_mul_of_nonneg_left ih hκ
      calc dist (T^[n+1] x) xs = dist (T (T^[n] x)) (T xs) := h1
        _ ≤ κ * (κ ^ n * dist x xs) := le_trans h2 h3
        _ = κ ^ (n+1) * dist x xs := by ring

/-! ## 4. The uniform history budget -/

/-- The history remainder after `m` shells: the discounted deviation of the
shell coefficient along the RG orbit from its fixed-point value. -/
noncomputable def historyRemainder (β : X → ℝ) (T : X → X) (x xs : X) (m : ℕ) : ℝ :=
  ∑ n ∈ range m, (β (T^[n] x) - β xs)

/-- Geometric series bound, in the form used below. -/
lemma geom_sum_le_inv_one_sub {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (m : ℕ) :
    ∑ n ∈ range m, κ ^ n ≤ 1 / (1 - κ) := by
  have hk : κ ≠ 1 := ne_of_lt h1
  have hpos : (0:ℝ) < 1 - κ := by linarith
  have he : ∑ n ∈ range m, κ ^ n = (1 - κ ^ m) / (1 - κ) := by
    rw [geom_sum_eq hk,
      div_eq_div_iff (by intro h; apply hk; linarith [sub_eq_zero.mp h])
        (by intro h; apply hk; linarith)]
    ring
  rw [he, div_le_div_iff₀ hpos hpos]
  nlinarith [pow_nonneg h0 m]

/-- **Row A1b history budget.**  With a genuine contraction `κ < 1` on the
observer coordinates, a Lipschitz shell coefficient, and a tube radius `B`, the
history remainder is bounded by `L · γ · B` with `γ = 1/(1−κ)`, *uniformly in
the number of shells* `m`. -/
theorem historyRemainder_bound {β : X → ℝ} {T : X → X} {κ L B : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ < 1) (hL : 0 ≤ L)
    (hT : IsObserverContraction T κ) (hβ : IsBetaLipschitz β L)
    {x xs : X} (hfix : T xs = xs) (hB : dist x xs ≤ B) (m : ℕ) :
    |historyRemainder β T x xs m| ≤ L * (1 / (1 - κ)) * B := by
  have hBnn : 0 ≤ B := le_trans dist_nonneg hB
  have hterm : ∀ n ∈ range m, |β (T^[n] x) - β xs| ≤ L * B * κ ^ n := by
    intro n _
    have h2 : |β (T^[n] x) - β xs| ≤ L * dist (T^[n] x) xs := hβ _ _
    have h3 : dist (T^[n] x) xs ≤ κ ^ n * dist x xs :=
      dist_iterate_fixedPoint_le h0 hT hfix x n
    have h4 : κ ^ n * dist x xs ≤ κ ^ n * B :=
      mul_le_mul_of_nonneg_left hB (pow_nonneg h0 n)
    calc |β (T^[n] x) - β xs| ≤ L * dist (T^[n] x) xs := h2
      _ ≤ L * (κ ^ n * B) := mul_le_mul_of_nonneg_left (le_trans h3 h4) hL
      _ = L * B * κ ^ n := by ring
  have hsum : |historyRemainder β T x xs m| ≤ ∑ n ∈ range m, L * B * κ ^ n :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hfactor : ∑ n ∈ range m, L * B * κ ^ n = L * B * ∑ n ∈ range m, κ ^ n := by
    rw [Finset.mul_sum]
  have hgeom : ∑ n ∈ range m, κ ^ n ≤ 1 / (1 - κ) := geom_sum_le_inv_one_sub h0 h1 m
  have hLB : 0 ≤ L * B := mul_nonneg hL hBnn
  calc |historyRemainder β T x xs m| ≤ ∑ n ∈ range m, L * B * κ ^ n := hsum
    _ = L * B * ∑ n ∈ range m, κ ^ n := hfactor
    _ ≤ L * B * (1 / (1 - κ)) := mul_le_mul_of_nonneg_left hgeom hLB
    _ = L * (1 / (1 - κ)) * B := by ring

/-! ## 5. Fallback: only the response products are summable -/

/-- Scale-dependent contraction factors: `x (n+1)` is the RG image of `x n`, and
each step contracts the distance to the fixed point by `κ n`. -/
theorem dist_le_prod_of_stepwise {xs : X} {x : ℕ → X} {κ : ℕ → ℝ}
    (hκ : ∀ n, 0 ≤ κ n) (hstep : ∀ n, dist (x (n+1)) xs ≤ κ n * dist (x n) xs) :
    ∀ n, dist (x n) xs ≤ (∏ i ∈ range n, κ i) * dist (x 0) xs := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : dist (x (n+1)) xs ≤ κ n * dist (x n) xs := hstep n
      have h2 : κ n * dist (x n) xs ≤ κ n * ((∏ i ∈ range n, κ i) * dist (x 0) xs) :=
        mul_le_mul_of_nonneg_left ih (hκ n)
      calc dist (x (n+1)) xs ≤ κ n * ((∏ i ∈ range n, κ i) * dist (x 0) xs) :=
            le_trans h1 h2
        _ = (∏ i ∈ range (n+1), κ i) * dist (x 0) xs := by
            rw [Finset.prod_range_succ]; ring

/-- **History budget from summable response products.**  If pointwise `κ < 1`
fails, a bound `S` on the partial sums of the products `∏_{i<n} κ i` still
delivers a uniform history budget `L · S · B`. -/
theorem historyRemainder_bound_of_products {β : X → ℝ} {L B S : ℝ}
    {xs : X} {x : ℕ → X} {κ : ℕ → ℝ}
    (hL : 0 ≤ L) (hκ : ∀ n, 0 ≤ κ n)
    (hβ : IsBetaLipschitz β L)
    (hstep : ∀ n, dist (x (n+1)) xs ≤ κ n * dist (x n) xs)
    (hB : dist (x 0) xs ≤ B)
    (hS : ∀ m, ∑ n ∈ range m, (∏ i ∈ range n, κ i) ≤ S) (m : ℕ) :
    |∑ n ∈ range m, (β (x n) - β xs)| ≤ L * S * B := by
  have hBnn : 0 ≤ B := le_trans dist_nonneg hB
  have hprodnn : ∀ n, 0 ≤ ∏ i ∈ range n, κ i := fun n =>
    Finset.prod_nonneg fun i _ => hκ i
  have hterm : ∀ n ∈ range m,
      |β (x n) - β xs| ≤ L * B * (∏ i ∈ range n, κ i) := by
    intro n _
    have h2 : |β (x n) - β xs| ≤ L * dist (x n) xs := hβ _ _
    have h3 : dist (x n) xs ≤ (∏ i ∈ range n, κ i) * dist (x 0) xs :=
      dist_le_prod_of_stepwise hκ hstep n
    have h4 : (∏ i ∈ range n, κ i) * dist (x 0) xs
        ≤ (∏ i ∈ range n, κ i) * B := mul_le_mul_of_nonneg_left hB (hprodnn n)
    calc |β (x n) - β xs| ≤ L * dist (x n) xs := h2
      _ ≤ L * ((∏ i ∈ range n, κ i) * B) :=
          mul_le_mul_of_nonneg_left (le_trans h3 h4) hL
      _ = L * B * (∏ i ∈ range n, κ i) := by ring
  have hsum : |∑ n ∈ range m, (β (x n) - β xs)|
      ≤ ∑ n ∈ range m, L * B * (∏ i ∈ range n, κ i) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hfactor : ∑ n ∈ range m, L * B * (∏ i ∈ range n, κ i)
      = L * B * ∑ n ∈ range m, (∏ i ∈ range n, κ i) := by rw [Finset.mul_sum]
  have hLB : 0 ≤ L * B := mul_nonneg hL hBnn
  calc |∑ n ∈ range m, (β (x n) - β xs)|
      ≤ ∑ n ∈ range m, L * B * (∏ i ∈ range n, κ i) := hsum
    _ = L * B * ∑ n ∈ range m, (∏ i ∈ range n, κ i) := hfactor
    _ ≤ L * B * S := mul_le_mul_of_nonneg_left (hS m) hLB
    _ = L * S * B := by ring

/-! ## 6. The fixed point need not be assumed -/

section Complete

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [Nonempty Y]

/-- On a complete observer space the fixed point of the RG step is not an extra
hypothesis: a genuine contraction has one. -/
theorem exists_fixedPoint_of_contraction {T : Y → Y} {κ : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ < 1) (hT : IsObserverContraction T κ) : ∃ xs, T xs = xs := by
  have hlip : LipschitzWith (Real.toNNReal κ) T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.coe_toNNReal _ h0] using hT x y
  have hc : ContractingWith (Real.toNNReal κ) T :=
    ⟨by rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ h0]; exact h1, hlip⟩
  exact ⟨_, hc.fixedPoint_isFixedPt⟩

/-- The history budget on a complete observer space, with the fixed point
produced rather than assumed. -/
theorem historyRemainder_bound_complete {β : Y → ℝ} {T : Y → Y} {κ L : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ < 1) (hL : 0 ≤ L)
    (hT : IsObserverContraction T κ) (hβ : IsBetaLipschitz β L) (x : Y) :
    ∃ xs, T xs = xs ∧ ∀ m : ℕ,
      |historyRemainder β T x xs m| ≤ L * (1 / (1 - κ)) * dist x xs := by
  obtain ⟨xs, hfix⟩ := exists_fixedPoint_of_contraction h0 h1 hT
  exact ⟨xs, hfix, fun m =>
    historyRemainder_bound h0 h1 hL hT hβ hfix le_rfl m⟩

end Complete

/-! ## 7. The adversarial test at `κ = 1` -/

/-- The unit shift on `ℝ` is an isometry: it satisfies the contraction estimate
with `κ = 1` and with no smaller constant. -/
theorem shift_isObserverContraction_one :
    IsObserverContraction (fun x : ℝ => x + 1) 1 := by
  intro x y
  simp [Real.dist_eq]

/-- The identity coefficient is `1`-Lipschitz. -/
theorem id_isBetaLipschitz_one : IsBetaLipschitz (fun x : ℝ => x) 1 := by
  intro x y
  simp [Real.dist_eq]

/-- **At `κ = 1` the geometric budget genuinely fails.**  For the unit shift and
`β = id` — an exact `κ = 1`, `L = 1` pair, with the initial point at distance
`0` from itself — the history sums grow without bound, so no finite budget `B`
can exist.  This rules out a "fake finite `B`" at the boundary `κ ↑ 1`. -/
theorem kappa_one_no_finite_budget (C : ℝ) :
    ∃ m : ℕ, C < ∑ n ∈ range m, |((fun x : ℝ => x + 1)^[n] 0) - 0| := by
  have hiter : ∀ n : ℕ, ((fun x : ℝ => x + 1)^[n] 0) = (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; push_cast; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 0)
  refine ⟨N + 1, ?_⟩
  have hterm : ∀ n ∈ range (N + 1), |((fun x : ℝ => x + 1)^[n] 0) - 0| = (n : ℝ) := by
    intro n _
    rw [hiter n, sub_zero, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [Finset.sum_congr rfl hterm]
  have hlast : (N : ℝ) ≤ ∑ n ∈ range (N + 1), (n : ℝ) := by
    have : ((N : ℝ)) = ∑ n ∈ ({N} : Finset ℕ), (n : ℝ) := by simp
    rw [this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro a ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · intro i _ _
      exact Nat.cast_nonneg i
  have : C < (N : ℝ) := lt_of_le_of_lt (le_max_left C 0) hN
  linarith

end YangMills
