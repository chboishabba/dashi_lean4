/-
# Row C (spatial half) — weighted influence rows, all-order powers, and
# quasi-local propagation

The spatial half of the Row-C obligation is an *exponential clustering* estimate
for the dynamical (Heat/Doob) generator of the stochastic relaxation used to
produce the continuum objects: the influence of a site `z` on a site `x` must
decay exponentially in the lattice distance, uniformly in the volume and to all
orders of the Dyson/semigroup expansion.

This file supplies the finite algebra that turns **one** weighted row estimate
into all of that, so that the only remaining input is the row estimate itself.

* `weighted_iter_row_le` — if the weight `w` is `≥ 1` and submultiplicative,
  `w(x,z) ≤ w(x,y)·w(y,z)`, the kernel `M` is entrywise nonnegative and its
  weighted row is bounded, `Σ_y w(x,y)M(x,y) ≤ C`, then **every** iterate obeys
  the same estimate with constant `Cⁿ`:

      Σ_y w(x,y)·Mⁿ(x,y) ≤ Cⁿ.

  No positivity of the powers and no separate all-order Dyson estimate is
  needed; they are consequences.
* `weighted_row_of_split` — the covariance correction is additive: an entrywise
  splitting `M_dyn ≤ M_static + M_cov` with two weighted row bounds gives the
  weighted row bound `C_H + C_cov` for the dynamical kernel.  This is the honest
  form of the "same-object" reduction: the static (RG) estimate does *not* by
  itself control the dynamical generator, but it controls it up to the
  covariance row.
* `metricWeight` section — for the repository's weight `w(x,y) = (3/2)^{d(x,y)}`
  built on an ordinary `ℕ`-valued lattice metric, `w ≥ 1` and submultiplicativity
  are **theorems**, from `d x x = 0` and the triangle inequality alone.
* `metric_iter_entry_le` — hence the entrywise all-order bound
  `Mⁿ(x,y) ≤ Cⁿ·(2/3)^{d(x,y)}`.
* `exp_series_summable`, `exp_series_cluster` — hence *quasi-locality of the
  semigroup*: for `t ≥ 0` the exponential series converges entrywise and

      Σ_n (tⁿ/n!)·Mⁿ(x,y) ≤ (2/3)^{d(x,y)}·e^{Ct},

  i.e. exponential clustering in the distance with an exponentially growing
  time factor, uniformly in the (finite) volume.  This replaces the older
  strict nearest-neighbour finite-speed route.

**Honest status.**  The physical inputs are the two weighted row bounds
(`hrow`), which are exactly the differentiated-locality estimate of the RG side
and the covariance response of the stochastic side.  Neither is proved here.
Row C is **not** closed by this file and the frozen research count is unchanged.
-/
import Mathlib

namespace YangMills

open Finset

open scoped Nat

section Weighted

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The `n`-fold composition of a finite kernel, `M⁰ = δ`, `M^{n+1} = M·Mⁿ`. -/
def iterKernel (M : S → S → ℝ) : ℕ → S → S → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | (n + 1) => fun x y => ∑ z, M x z * iterKernel M n z y

@[simp] theorem iterKernel_zero (M : S → S → ℝ) (x y : S) :
    iterKernel M 0 x y = if x = y then 1 else 0 := rfl

theorem iterKernel_succ (M : S → S → ℝ) (n : ℕ) (x y : S) :
    iterKernel M (n + 1) x y = ∑ z, M x z * iterKernel M n z y := rfl

@[simp] theorem iterKernel_one (M : S → S → ℝ) (x y : S) :
    iterKernel M 1 x y = M x y := by
  simp [iterKernel_succ]

theorem iterKernel_nonneg {M : S → S → ℝ} (hM : ∀ x y, 0 ≤ M x y) :
    ∀ (n : ℕ) (x y : S), 0 ≤ iterKernel M n x y := by
  intro n
  induction n with
  | zero => intro x y; by_cases h : x = y <;> simp [h]
  | succ n ih =>
      intro x y
      rw [iterKernel_succ]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (hM x z) (ih z y)

/-- **All-order weighted row estimate.**  One weighted row bound for `M`
propagates to every power of `M`, with constant `Cⁿ`. -/
theorem weighted_iter_row_le [Nonempty S] {M w : S → S → ℝ} {C : ℝ}
    (hw1 : ∀ x y, 1 ≤ w x y) (hsub : ∀ x y z, w x z ≤ w x y * w y z)
    (hM : ∀ x y, 0 ≤ M x y) (hrow : ∀ x, ∑ y, w x y * M x y ≤ C) :
    ∀ (n : ℕ) (x : S), ∑ y, w x y * iterKernel M (n + 1) x y ≤ C ^ (n + 1) := by
  have hwpos : ∀ x y, (0:ℝ) < w x y := fun x y => lt_of_lt_of_le zero_lt_one (hw1 x y)
  have hC : 0 ≤ C := by
    obtain ⟨x⟩ := ‹Nonempty S›
    refine le_trans ?_ (hrow x)
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hwpos x y).le (hM x y)
  intro n
  induction n with
  | zero => intro x; simpa using hrow x
  | succ n ih =>
      intro x
      have hPnn : ∀ z y, 0 ≤ iterKernel M (n + 1) z y :=
        fun z y => iterKernel_nonneg hM (n + 1) z y
      have hinner : ∀ z, ∑ y, w x y * iterKernel M (n + 1) z y
          ≤ w x z * C ^ (n + 1) := by
        intro z
        calc ∑ y, w x y * iterKernel M (n + 1) z y
            ≤ ∑ y, (w x z * w z y) * iterKernel M (n + 1) z y :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_right (hsub x z y) (hPnn z y)
          _ = w x z * ∑ y, w z y * iterKernel M (n + 1) z y := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ => by ring
          _ ≤ w x z * C ^ (n + 1) :=
              mul_le_mul_of_nonneg_left (ih z) (hwpos x z).le
      calc ∑ y, w x y * iterKernel M (n + 2) x y
          = ∑ y, ∑ z, w x y * (M x z * iterKernel M (n + 1) z y) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [iterKernel_succ, Finset.mul_sum]
        _ = ∑ z, ∑ y, M x z * (w x y * iterKernel M (n + 1) z y) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun z _ =>
              Finset.sum_congr rfl fun y _ => by ring
        _ ≤ ∑ z, M x z * (w x z * C ^ (n + 1)) := by
            refine Finset.sum_le_sum fun z _ => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hinner z) (hM x z)
        _ = (∑ z, w x z * M x z) * C ^ (n + 1) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun z _ => by ring
        _ ≤ C * C ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (hrow x) (pow_nonneg hC _)
        _ = C ^ (n + 2) := by ring

omit [DecidableEq S] in
/-- **The covariance correction is additive.**  An entrywise splitting of the
dynamical kernel into a static part and a covariance part turns two weighted row
bounds into one. -/
theorem weighted_row_of_split {M M₁ M₂ w : S → S → ℝ} {C₁ C₂ : ℝ}
    (hw : ∀ x y, 0 ≤ w x y) (hsplit : ∀ x y, M x y ≤ M₁ x y + M₂ x y)
    (hrow₁ : ∀ x, ∑ y, w x y * M₁ x y ≤ C₁) (hrow₂ : ∀ x, ∑ y, w x y * M₂ x y ≤ C₂)
    (x : S) : ∑ y, w x y * M x y ≤ C₁ + C₂ := by
  have h1 : ∑ y, w x y * M x y ≤ ∑ y, (w x y * M₁ x y + w x y * M₂ x y) := by
    refine Finset.sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (hsplit x y) (hw x y)
    linarith [this]
  have h2 : ∑ y, (w x y * M₁ x y + w x y * M₂ x y)
      = (∑ y, w x y * M₁ x y) + ∑ y, w x y * M₂ x y := Finset.sum_add_distrib
  linarith [h1, h2.le, h2.ge, hrow₁ x, hrow₂ x]

/-- **Entrywise all-order bound.**  A single weighted term is at most the whole
(nonnegative) weighted row. -/
theorem weighted_iter_entry_le [Nonempty S] {M w : S → S → ℝ} {C : ℝ}
    (hw1 : ∀ x y, 1 ≤ w x y) (hsub : ∀ x y z, w x z ≤ w x y * w y z)
    (hM : ∀ x y, 0 ≤ M x y) (hrow : ∀ x, ∑ y, w x y * M x y ≤ C)
    (n : ℕ) (x y : S) :
    w x y * iterKernel M (n + 1) x y ≤ C ^ (n + 1) := by
  have hwpos : ∀ a b, (0:ℝ) < w a b := fun a b => lt_of_lt_of_le zero_lt_one (hw1 a b)
  have hsingle : w x y * iterKernel M (n + 1) x y
      ≤ ∑ z, w x z * iterKernel M (n + 1) x z := by
    refine Finset.single_le_sum (f := fun z => w x z * iterKernel M (n + 1) x z)
      (fun z _ => mul_nonneg (hwpos x z).le (iterKernel_nonneg hM (n + 1) x z))
      (Finset.mem_univ y)
  exact hsingle.trans (weighted_iter_row_le hw1 hsub hM hrow n x)

end Weighted

/-! ## The repository weight `(3/2)^{d(x,y)}` -/

section MetricWeight

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exponential weight attached to an `ℕ`-valued lattice metric. -/
noncomputable def metricWeight (d : S → S → ℕ) (x y : S) : ℝ := (3 / 2 : ℝ) ^ d x y

omit [Fintype S] [DecidableEq S] in
theorem one_le_metricWeight (d : S → S → ℕ) (x y : S) : 1 ≤ metricWeight d x y :=
  one_le_pow₀ (by norm_num)

omit [Fintype S] [DecidableEq S] in
theorem metricWeight_pos (d : S → S → ℕ) (x y : S) : 0 < metricWeight d x y :=
  lt_of_lt_of_le zero_lt_one (one_le_metricWeight d x y)

omit [Fintype S] [DecidableEq S] in
/-- **Submultiplicativity of the weight is the triangle inequality.** -/
theorem metricWeight_submul {d : S → S → ℕ}
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (x y z : S) :
    metricWeight d x z ≤ metricWeight d x y * metricWeight d y z := by
  have h : (3 / 2 : ℝ) ^ d x z ≤ (3 / 2 : ℝ) ^ (d x y + d y z) :=
    pow_le_pow_right₀ (by norm_num) (htri x y z)
  simpa [metricWeight, pow_add] using h

/-- **All-order quasi-locality.**  One `(3/2)^d`-weighted row bound gives the
entrywise exponential decay `Mⁿ(x,y) ≤ Cⁿ·(2/3)^{d(x,y)}` for every `n`. -/
theorem metric_iter_entry_le [Nonempty S] {d : S → S → ℕ} {M : S → S → ℝ} {C : ℝ}
    (hd0 : ∀ x, d x x = 0) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hM : ∀ x y, 0 ≤ M x y) (hrow : ∀ x, ∑ y, metricWeight d x y * M x y ≤ C)
    (n : ℕ) (x y : S) :
    iterKernel M n x y ≤ C ^ n * (2 / 3 : ℝ) ^ d x y := by
  have hwpos := metricWeight_pos (d := d)
  cases n with
  | zero =>
      by_cases h : x = y
      · subst h
        simp [hd0 x]
      · have : (0:ℝ) ≤ (2 / 3 : ℝ) ^ d x y := by positivity
        simpa [h] using this
  | succ n =>
      have hentry := weighted_iter_entry_le (w := metricWeight d)
        (one_le_metricWeight d) (metricWeight_submul htri) hM hrow n x y
      have hw : metricWeight d x y = (3 / 2 : ℝ) ^ d x y := rfl
      have hinv : ((3 / 2 : ℝ) ^ d x y)⁻¹ = (2 / 3 : ℝ) ^ d x y := by
        rw [← inv_pow]
        norm_num
      have hpos : (0:ℝ) < (3 / 2 : ℝ) ^ d x y := by positivity
      have hkey : iterKernel M (n + 1) x y ≤ C ^ (n + 1) / (3 / 2 : ℝ) ^ d x y := by
        rw [le_div_iff₀ hpos]
        calc iterKernel M (n + 1) x y * (3 / 2 : ℝ) ^ d x y
            = metricWeight d x y * iterKernel M (n + 1) x y := by rw [hw]; ring
          _ ≤ C ^ (n + 1) := hentry
      calc iterKernel M (n + 1) x y ≤ C ^ (n + 1) / (3 / 2 : ℝ) ^ d x y := hkey
        _ = C ^ (n + 1) * (2 / 3 : ℝ) ^ d x y := by
            rw [div_eq_mul_inv, hinv]

/-- The exponential series of a quasi-local kernel converges entrywise. -/
theorem exp_series_summable [Nonempty S] {d : S → S → ℕ} {M : S → S → ℝ} {C t : ℝ}
    (hd0 : ∀ x, d x x = 0) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hM : ∀ x y, 0 ≤ M x y) (hrow : ∀ x, ∑ y, metricWeight d x y * M x y ≤ C)
    (ht : 0 ≤ t) (x y : S) :
    Summable (fun n : ℕ => t ^ n / n ! * iterKernel M n x y) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (((Real.summable_pow_div_factorial (C * t)).mul_left ((2 / 3 : ℝ) ^ d x y)))
  · exact mul_nonneg (by positivity) (iterKernel_nonneg hM n x y)
  · have hb := metric_iter_entry_le hd0 htri hM hrow n x y
    have hfac : (0:ℝ) ≤ t ^ n / n ! := by positivity
    calc t ^ n / n ! * iterKernel M n x y
        ≤ t ^ n / n ! * (C ^ n * (2 / 3 : ℝ) ^ d x y) :=
          mul_le_mul_of_nonneg_left hb hfac
      _ = (2 / 3 : ℝ) ^ d x y * ((C * t) ^ n / n !) := by
          rw [mul_pow]; ring

/-- **Exponential clustering of the semigroup.**  A single `(3/2)^d`-weighted row
bound gives, uniformly in the finite volume,

    Σ_n (tⁿ/n!)·Mⁿ(x,y) ≤ (2/3)^{d(x,y)}·e^{Ct}      (t ≥ 0). -/
theorem exp_series_cluster [Nonempty S] {d : S → S → ℕ} {M : S → S → ℝ} {C t : ℝ}
    (hd0 : ∀ x, d x x = 0) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hM : ∀ x y, 0 ≤ M x y) (hrow : ∀ x, ∑ y, metricWeight d x y * M x y ≤ C)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (x y : S) :
    ∑' n : ℕ, t ^ n / n ! * iterKernel M n x y
      ≤ (2 / 3 : ℝ) ^ d x y * Real.exp (C * t) := by
  refine Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (by positivity) (iterKernel_nonneg hM n x y)) fun N => ?_
  have hterm : ∀ n ∈ range N, t ^ n / n ! * iterKernel M n x y
      ≤ (2 / 3 : ℝ) ^ d x y * ((C * t) ^ n / n !) := by
    intro n _
    have hb := metric_iter_entry_le hd0 htri hM hrow n x y
    have hfac : (0:ℝ) ≤ t ^ n / n ! := by positivity
    calc t ^ n / n ! * iterKernel M n x y
        ≤ t ^ n / n ! * (C ^ n * (2 / 3 : ℝ) ^ d x y) :=
          mul_le_mul_of_nonneg_left hb hfac
      _ = (2 / 3 : ℝ) ^ d x y * ((C * t) ^ n / n !) := by
          rw [mul_pow]; ring
  calc ∑ n ∈ range N, t ^ n / n ! * iterKernel M n x y
      ≤ ∑ n ∈ range N, (2 / 3 : ℝ) ^ d x y * ((C * t) ^ n / n !) :=
        Finset.sum_le_sum hterm
    _ = (2 / 3 : ℝ) ^ d x y * ∑ n ∈ range N, (C * t) ^ n / n ! := by
        rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) ^ d x y * Real.exp (C * t) := by
        refine mul_le_mul_of_nonneg_left
          (Real.sum_le_exp_of_nonneg (by positivity) N) (by positivity)

end MetricWeight

end YangMills
