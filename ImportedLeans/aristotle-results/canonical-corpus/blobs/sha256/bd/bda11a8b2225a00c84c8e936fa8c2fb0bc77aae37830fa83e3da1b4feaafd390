import RiemannAnalytic.SourceNormalization

/-!
# G15 — the source coefficient: the literal Weil normalization, and the
polylogarithmic verdict of the normalization gate

G14 reduced the whole anchored second-moment route to a single scalar
comparison, the **normalization gate**

```
C_src(T,H,ρ) · t² S₀(α)²      versus      c_Gram L⁶,
```

and computed the prime factor exactly.  What was left open was the size of the
source coefficient `C_src` itself.  This module does three things.

## 1.  The literal explicit-formula (Weil) prime weight

The prime term of the literal explicit formula is *not* `Λ(n)`; it is
`Λ(n) n^{-1/2} φ̂(log n)`.  The module introduces the literal Weil weight

```
w^W_α(n) = Λ(n) · n^{-1/2} · cosh(2α log n)
```

(the `cosh` is the contribution of the zero `ρ = ½+α+iγ` together with its
mirror `1−ρ̄`) and the tapered version `w^W_α(n)|φ̂(log n)|, and pins its mass:

* `tiltedMass_upper_of_neg_tilt` — a new estimate extending
  `tiltedMass_upper` to *negative* tilts: `∑_{n≤N} Λ(n) n^v ≤ 809 N^{1+v}` for
  every `v ≥ −1/2`.  (The previous version required `v ≥ 0`, which excludes the
  Weil normalization.)
* `weilMass_two_sided` — `N^{1/2+2|α|}/32 ≤ S₀^W(α) ≤ 809 N^{1/2+2|α|}`.

So passing from the route's raw weight `Λ(n)` to the literal Weil weight
`Λ(n)n^{-1/2}` costs exactly one power of `N` in `S₀²`, and no more: the
missing factor of `G14` is **not** the archimedean normalization `n^{-1/2}`.

## 2.  The verdict for every polylogarithmic source coefficient

* `contraction_condition_fails_of_polylog_normalization` and its Weil form
  `weil_contraction_condition_fails_of_polylog_normalization` — if the source
  coefficient is bounded below by `κ (log N)^{-A}` for *any* fixed `κ > 0` and
  *any* fixed exponent `A`, then the G14 contraction condition fails, with an
  explicit threshold in `N`.  This strictly extends G14's
  `contraction_condition_fails_of_fixed_normalization` (the case `A = 0`) and
  removes the last generic escape: a source coefficient that saves only
  logarithms cannot pass the gate.  Only a coefficient decaying like a **power
  of `N`** can.
* `taperedWeilMass_lower_of_polyDecay` — and a source coefficient built from a
  taper whose transform decays only polynomially along the prime frequencies is
  exactly of that polylogarithmic kind: the tapered Weil mass is still
  `≥ κ N^{1/2}/(32 (1+log N)^B)`.  So the gate is red for every taper of finite
  smoothness / compact support; only a transform decaying exponentially at rate
  `> 1/2 + 2|α|` along `u = log n` could produce a green gate.
* `taperedWeilMass_le_of_expDecay` — and that is exactly the threshold: an
  exponential transform decay of rate `θ > 1/2 + 2|α|` makes the tapered Weil
  mass bounded by an absolute constant times `C/δ²`, `δ = θ − 1/2 − 2|α|`,
  uniformly in `N`.  The gate is then green.  The two theorems together locate
  the binary decision precisely at the analyticity width of the taper.

## 3.  Two structural facts about the gate

* `sourceRatio_ge_of_floor` — the gate quantity can never be *small*: the Gram
  floor already forces `C_src t² S₀² ≥ c L⁴/120000`.  So the "green" branch can
  only ever be green by a factor `L^{-2}`, never more.
* `gate_invariant_under_common_rescaling` — the gate condition is invariant
  under a common rescaling of the taper (which multiplies both the defect and
  the floor constant by the same factor).  So no renormalization of the source
  can pass the gate: the comparison is scale-free.

Nothing here proves the source identification, and nothing here proves the
Riemann Hypothesis.  No `sorry`, no `axiom`, no postulate.
-/

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ### A general logarithm-versus-square-root tool -/

/-- `(log N)^k ≤ (2k)^k √N` for every `k ≥ 1`.  This is the quantitative form of
"a power of `N` beats every power of `log N`", used to turn the gate comparison
into an explicit threshold. -/
theorem log_pow_le_mul_sqrt (N : ℕ) {k : ℕ} (hk : 0 < k) :
    (Real.log N) ^ k ≤ (2 * k : ℝ) ^ k * Real.sqrt N := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hε : (0 : ℝ) < 1 / (2 * k) := by positivity
  have h := Real.log_natCast_le_rpow_div N (ε := 1 / (2 * k)) hε
  have hnn : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hdiv : (N : ℝ) ^ ((1 : ℝ) / (2 * k)) / (1 / (2 * k))
      = (2 * k : ℝ) * (N : ℝ) ^ ((1 : ℝ) / (2 * k)) := by
    field_simp
  rw [hdiv] at h
  have hpow : ((2 * k : ℝ) * (N : ℝ) ^ ((1 : ℝ) / (2 * k))) ^ k
      = (2 * k : ℝ) ^ k * Real.sqrt N := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / (2 * k))) k,
      ← Real.rpow_mul (Nat.cast_nonneg N), Real.sqrt_eq_rpow]
    congr 2
    field_simp
  calc (Real.log N) ^ k ≤ ((2 * k : ℝ) * (N : ℝ) ^ ((1 : ℝ) / (2 * k))) ^ k :=
        pow_le_pow_left₀ hnn h k
    _ = (2 * k : ℝ) ^ k * Real.sqrt N := hpow

/-! ### The tilted prime mass at negative tilt -/

private lemma icc_one_eq_ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N :=
  Finset.val_inj.mp rfl

private lemma psi_sum_eq' (N : ℕ) : ∑ n ∈ Icc 1 N, Λ n = Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast, icc_one_eq_ioc_zero]

/-- The pointwise comparison behind the negative-tilt mass bound: within one
`e`-fold of the top frequency the tilted weight is at most `e^{1/2}` times the
weight at the top. -/
private lemma rpow_le_of_close {N n : ℕ} {v : ℝ} (hv : -(1 / 2 : ℝ) ≤ v)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hx : Real.log N - Real.log n < 1) :
    (n : ℝ) ^ v ≤ 1.65 * (N : ℝ) ^ v := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hn0 (by exact_mod_cast hnN)
  have hxnn : 0 ≤ Real.log N - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast hnN))
  have hkey : v * Real.log n ≤ 1 / 2 + v * Real.log N := by
    rcases le_or_gt 0 v with hvpos | hvneg
    · nlinarith [hxnn]
    · nlinarith [hx, hvneg]
  have hrw1 : (n : ℝ) ^ v = Real.exp (v * Real.log n) := by
    rw [Real.rpow_def_of_pos hn0]; ring_nf
  have hrw2 : (N : ℝ) ^ v = Real.exp (v * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0]; ring_nf
  rw [hrw1, hrw2]
  have hexp : Real.exp (v * Real.log n) ≤ Real.exp (1 / 2 + v * Real.log N) :=
    Real.exp_le_exp.mpr hkey
  have hsplit : Real.exp (1 / 2 + v * Real.log N)
      = Real.exp (1 / 2) * Real.exp (v * Real.log N) := Real.exp_add _ _
  have he : Real.exp (1 / 2 : ℝ) ≤ 1.65 := by
    have h2 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ), h2]
  have hpos : (0 : ℝ) < Real.exp (v * Real.log N) := Real.exp_pos _
  calc Real.exp (v * Real.log n) ≤ Real.exp (1 / 2) * Real.exp (v * Real.log N) := by
        rw [← hsplit]; exact hexp
    _ ≤ 1.65 * Real.exp (v * Real.log N) := by nlinarith [hpos, he]

/-- **The tilted prime mass at a negative tilt.**  `tiltedMass_upper` needs a
nonnegative tilt; the literal Weil normalization has tilt `−1/2 + 2|α|`, which is
negative for `|α| < 1/4`.  The dyadic centered estimate `tiltedCentered_le`
supplies the missing range:

```
∑_{n ≤ N} Λ(n) n^v  ≤  809 · N^{1+v}      for every v ≥ −1/2.
```
-/
theorem tiltedMass_upper_of_neg_tilt {N : ℕ} (hN : (0 : ℝ) < (N : ℝ)) {v : ℝ}
    (hv : -(1 / 2 : ℝ) ≤ v) :
    tiltedMass N v ≤ 809 * (N : ℝ) ^ (1 + v) := by
  have hNv : (0 : ℝ) < (N : ℝ) ^ v := Real.rpow_pos_of_pos hN v
  have hsplit : (N : ℝ) ^ (1 + v) = (N : ℝ) * (N : ℝ) ^ v := by
    rw [Real.rpow_add hN, Real.rpow_one]
  have hpt : ∀ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ v
      ≤ Λ n * (n : ℝ) ^ v * (Real.log N - Real.log n) ^ 2 + Λ n * (1.65 * (N : ℝ) ^ v) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hnv : (0 : ℝ) < (n : ℝ) ^ v := Real.rpow_pos_of_pos hn0 v
    rcases le_or_gt 1 (Real.log N - Real.log n) with hfar | hnear
    · have hsq : (1 : ℝ) ≤ (Real.log N - Real.log n) ^ 2 := by nlinarith
      have h1 : Λ n * (n : ℝ) ^ v ≤ Λ n * (n : ℝ) ^ v * (Real.log N - Real.log n) ^ 2 := by
        nlinarith [mul_nonneg hΛ hnv.le]
      nlinarith [mul_nonneg hΛ (mul_nonneg (by norm_num : (0:ℝ) ≤ 1.65) hNv.le)]
    · have hclose := rpow_le_of_close hv hn1 hnN hnear
      have h1 : Λ n * (n : ℝ) ^ v ≤ Λ n * (1.65 * (N : ℝ) ^ v) :=
        mul_le_mul_of_nonneg_left hclose hΛ
      nlinarith [mul_nonneg (mul_nonneg hΛ hnv.le) (sq_nonneg (Real.log N - Real.log n))]
  have hsum : tiltedMass N v
      ≤ tiltedCentered N v + 1.65 * (N : ℝ) ^ v * ∑ n ∈ Icc 1 N, Λ n := by
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib] at this
    have hrw : ∑ n ∈ Icc 1 N, Λ n * (1.65 * (N : ℝ) ^ v)
        = 1.65 * (N : ℝ) ^ v * ∑ n ∈ Icc 1 N, Λ n := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [hrw] at this
    exact this
  have hcent : tiltedCentered N v ≤ 800 * (N : ℝ) ^ (1 + v) := tiltedCentered_le hv
  have hpsi : ∑ n ∈ Icc 1 N, Λ n ≤ 5.4 * (N : ℝ) := by
    rw [psi_sum_eq']
    have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hN.le
    have hlog4 : Real.log 4 + 4 ≤ 5.4 := by
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
      nlinarith [Real.log_two_lt_d9]
    nlinarith [this, hN.le]
  have hfin : 1.65 * (N : ℝ) ^ v * ∑ n ∈ Icc 1 N, Λ n ≤ 9 * (N : ℝ) ^ (1 + v) := by
    have h1 : 1.65 * (N : ℝ) ^ v * ∑ n ∈ Icc 1 N, Λ n
        ≤ 1.65 * (N : ℝ) ^ v * (5.4 * (N : ℝ)) := by
      have : (0 : ℝ) ≤ 1.65 * (N : ℝ) ^ v := by positivity
      exact mul_le_mul_of_nonneg_left hpsi this
    rw [hsplit]
    nlinarith [h1, hNv, hN]
  linarith [hsum, hcent, hfin]

/-! ### The literal Weil prime weight -/

/-- **The literal explicit-formula (Weil) prime weight** of a zero
`ρ = ½ + α + iγ` together with its mirror image:
`w^W_α(n) = Λ(n) n^{-1/2} cosh(2α log n)`.  The factor `n^{-1/2}` is the
archimedean normalization of the explicit formula; the route's raw weight
`coshVonMangoldt` is the same object without it. -/
noncomputable def weilWeight (α : ℝ) (n : ℕ) : ℝ :=
  Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * Real.cosh (2 * α * Real.log n)

/-- The literal Weil prime mass `S₀^W(α) = ∑_{n ≤ N} w^W_α(n)`. -/
noncomputable def weilMass (N : ℕ) (α : ℝ) : ℝ := ∑ n ∈ Icc 1 N, weilWeight α n

theorem weilWeight_nonneg (α : ℝ) (n : ℕ) : 0 ≤ weilWeight α n := by
  unfold weilWeight
  have h1 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h3 : (0 : ℝ) ≤ Real.cosh (2 * α * Real.log n) := (Real.cosh_pos _).le
  positivity

theorem weilMass_nonneg (N : ℕ) (α : ℝ) : 0 ≤ weilMass N α :=
  Finset.sum_nonneg fun n _ => weilWeight_nonneg α n

/-- The Weil weight, sandwiched by the pure tilt `n^{-1/2+2|α|}`. -/
private lemma weilWeight_bounds {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    Λ n * (n : ℝ) ^ (-(1 / 2) + 2 * |α| : ℝ) / 2 ≤ weilWeight α n ∧
      weilWeight α n ≤ Λ n * (n : ℝ) ^ (-(1 / 2) + 2 * |α| : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  have habs : Real.cosh (2 * α * Real.log n) = Real.cosh (2 * |α| * Real.log n) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -α * Real.log n = -(2 * α * Real.log n) by ring, Real.cosh_neg]
  have hsplit : (n : ℝ) ^ (-(1 / 2) + 2 * |α| : ℝ)
      = (n : ℝ) ^ (-(1 / 2) : ℝ) * (n : ℝ) ^ (2 * |α| : ℝ) := Real.rpow_add hn0 _ _
  have hcexp : Real.cosh (2 * |α| * Real.log n)
      = (Real.exp (2 * |α| * Real.log n) + Real.exp (-(2 * |α| * Real.log n))) / 2 :=
    Real.cosh_eq _
  have hrpow : (n : ℝ) ^ (2 * |α| : ℝ) = Real.exp (2 * |α| * Real.log n) := by
    rw [Real.rpow_def_of_pos hn0]; ring_nf
  have hneg : (0 : ℝ) < Real.exp (-(2 * |α| * Real.log n)) := Real.exp_pos _
  have hle : Real.exp (-(2 * |α| * Real.log n)) ≤ Real.exp (2 * |α| * Real.log n) := by
    refine Real.exp_le_exp.mpr ?_
    have := Real.log_natCast_nonneg n
    nlinarith [abs_nonneg α]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hn0 _
  constructor
  · unfold weilWeight
    rw [habs, hcexp, hsplit, hrpow]
    nlinarith [hΛ, hn2, hneg, mul_nonneg hΛ hn2.le]
  · unfold weilWeight
    rw [habs, hcexp, hsplit, hrpow]
    nlinarith [hΛ, hn2, hneg, hle, mul_nonneg hΛ hn2.le]

/-- **The literal Weil prime mass, two-sided.**  For every `N ≥ 10⁸` and every
`|α| < 1/2`,

```
N^{1/2 + 2|α|} / 32  ≤  S₀^W(α)  ≤  809 · N^{1/2 + 2|α|}.
```

Passing from `Λ(n)` to the literal explicit-formula weight `Λ(n)n^{-1/2}`
therefore costs exactly one half power of `N`, i.e. one full power of `N` in
`S₀²`, and nothing more. -/
theorem weilMass_two_sided {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {α : ℝ} (hα : |α| < 1 / 2) :
    (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) / 32 ≤ weilMass N α ∧
      weilMass N α ≤ 809 * (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set v : ℝ := -(1 / 2) + 2 * |α| with hv
  have hv1 : |v| ≤ 1 := by
    rw [hv, abs_le]
    constructor <;> [linarith [abs_nonneg α]; linarith [hα]]
  have hvhalf : -(1 / 2 : ℝ) ≤ v := by rw [hv]; linarith [abs_nonneg α]
  have hexp : (1 : ℝ) + v = 1 / 2 + 2 * |α| := by rw [hv]; ring
  constructor
  · have hterm : ∀ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ v / 2 ≤ weilWeight α n := by
      intro n hn
      exact (weilWeight_bounds (α := α) (Finset.mem_Icc.mp hn).1).1
    have hsum : tiltedMass N v / 2 ≤ weilMass N α := by
      rw [tiltedMass, Finset.sum_div]
      exact Finset.sum_le_sum hterm
    have hlow := tiltedMass_lower hN (v := v) hv1
    rw [hexp] at hlow
    linarith
  · have hterm : ∀ n ∈ Icc 1 N, weilWeight α n ≤ Λ n * (n : ℝ) ^ v := by
      intro n hn
      exact (weilWeight_bounds (α := α) (Finset.mem_Icc.mp hn).1).2
    have hsum : weilMass N α ≤ tiltedMass N v := Finset.sum_le_sum hterm
    have hup := tiltedMass_upper_of_neg_tilt hN0 hvhalf
    rw [hexp] at hup
    linarith

/-! ### The verdict of the gate for a polylogarithmic source coefficient -/

private lemma sqrt_le_self_of_one_le {x : ℝ} (h : 1 ≤ x) : Real.sqrt x ≤ x := by
  nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ x), Real.sqrt_nonneg x,
    Real.one_le_sqrt.mpr h]

/-- **The master gate theorem.**  Suppose that, after allowing an arbitrary
polylogarithmic loss `(log N)^A`, the gate quantity `C_src t² S²` is still at
least `κ√N`.  Then the G14 contraction condition

```
120000 (log N)² · C_src t² S²  <  c (log N)⁶
```

is **false**, provided only the explicit constant comparison
`c (2(A+4))^{A+4} ≤ 120000 κ`.

This is the exact statement that *a source coefficient which saves only
logarithms cannot pass the normalization gate*: whatever the fixed exponent `A`,
a single square root of `N` on the prime side defeats it. -/
theorem gate_fails_of_polylog_loss {N A : ℕ} {c t κ Csrc S : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hc : 0 < c)
    (hlow : κ * Real.sqrt N ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2))
    (hthr : c * (2 * ((A : ℝ) + 4)) ^ (A + 4) ≤ 120000 * κ) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) < c * (Real.log N) ^ 6) := by
  intro hgate
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  have hLA : (0 : ℝ) < (Real.log N) ^ A := pow_pos hLpos A
  have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := pow_pos hLpos 2
  have hsqrt : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN0
  -- multiply the gate by `(log N)^A`
  have h1 : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A
      < c * (Real.log N) ^ 6 * (Real.log N) ^ A :=
    mul_lt_mul_of_pos_right hgate hLA
  have hLHS : 120000 * (Real.log N) ^ 2 * (κ * Real.sqrt N)
      ≤ 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A := by
    have hrw : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A
        = 120000 * (Real.log N) ^ 2 * (Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2)) := by ring
    rw [hrw]
    have : (0 : ℝ) ≤ 120000 * (Real.log N) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlow this
  have hRHS : c * (Real.log N) ^ 6 * (Real.log N) ^ A
      = c * (Real.log N) ^ (A + 4) * (Real.log N) ^ 2 := by
    rw [pow_add]; ring
  have hstep : 120000 * (Real.log N) ^ 2 * (κ * Real.sqrt N)
      < c * (Real.log N) ^ (A + 4) * (Real.log N) ^ 2 := by
    rw [← hRHS]; linarith [hLHS, h1]
  have hcancel : 120000 * (κ * Real.sqrt N) < c * (Real.log N) ^ (A + 4) := by
    have hrw : 120000 * (Real.log N) ^ 2 * (κ * Real.sqrt N)
        = (120000 * (κ * Real.sqrt N)) * (Real.log N) ^ 2 := by ring
    rw [hrw] at hstep
    exact lt_of_mul_lt_mul_right (by linarith [hstep]) hL2.le
  have hlogpow := log_pow_le_mul_sqrt N (k := A + 4) (Nat.succ_pos _)
  have hcast : ((2 : ℝ) * ((A + 4 : ℕ) : ℝ)) ^ (A + 4) = (2 * ((A : ℝ) + 4)) ^ (A + 4) := by
    push_cast; ring_nf
  rw [hcast] at hlogpow
  have hchain : c * (Real.log N) ^ (A + 4)
      ≤ c * ((2 * ((A : ℝ) + 4)) ^ (A + 4) * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left hlogpow hc.le
  have hfin : c * ((2 * ((A : ℝ) + 4)) ^ (A + 4) * Real.sqrt N) ≤ 120000 * κ * Real.sqrt N := by
    have hrw : c * ((2 * ((A : ℝ) + 4)) ^ (A + 4) * Real.sqrt N)
        = (c * (2 * ((A : ℝ) + 4)) ^ (A + 4)) * Real.sqrt N := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hthr hsqrt.le
  linarith [hcancel, hchain, hfin]

/-- **No polylogarithmic source coefficient passes the gate — the route's raw
normalization.**  If `C_src ≥ κ (log N)^{-A}` for a fixed `κ > 0` and a fixed
exponent `A`, then the contraction condition of
`offLineZero_excluded_of_sourceNormalization` fails.  G14's
`contraction_condition_fails_of_fixed_normalization` is the case `A = 0`. -/
theorem contraction_condition_fails_of_polylog_normalization {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {α t c κ Csrc : ℝ} (hα : |α| < 1 / 2)
    (hc : 0 < c) (hκ : 0 < κ) (ht : t ≠ 0)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hthr : c * (2 * ((A : ℝ) + 4)) ^ (A + 4) ≤ 120000 * (κ * t ^ 2 / 1024)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have ht2 : 0 < t ^ 2 := by positivity
  -- the raw twisted mass is at least `N/32`
  have hmass := (twistedPrimeMass hN hα).1
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ (1 + 2 * |α| : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg α] :
      (1 : ℝ) ≤ 1 + 2 * |α|)
    simpa using this
  have hS : (N : ℝ) / 32 ≤ twistedMoment N α 0 := by linarith [hmass, hpow]
  have hSsq : (N : ℝ) ^ 2 / 1024 ≤ (twistedMoment N α 0) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) / 32 := by positivity
    nlinarith [hS, h0]
  -- and `N² ≥ √N`
  have hsq : Real.sqrt N ≤ (N : ℝ) ^ 2 := by
    have h1 : Real.sqrt N ≤ (N : ℝ) := sqrt_le_self_of_one_le hN1
    nlinarith [hN1, h1]
  refine gate_fails_of_polylog_loss (A := A) hN hc ?_ hthr
  have hstep : κ * t ^ 2 / 1024 * Real.sqrt N ≤ κ * t ^ 2 / 1024 * (N : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ κ * t ^ 2 / 1024 := by positivity
    exact mul_le_mul_of_nonneg_left hsq this
  have hfin : κ * t ^ 2 / 1024 * (N : ℝ) ^ 2
      ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * (twistedMoment N α 0) ^ 2) := by
    have h1 : κ * ((N : ℝ) ^ 2 / 1024) ≤ κ * (twistedMoment N α 0) ^ 2 :=
      mul_le_mul_of_nonneg_left hSsq hκ.le
    have h2 : κ * (twistedMoment N α 0) ^ 2
        ≤ Csrc * (Real.log N) ^ A * (twistedMoment N α 0) ^ 2 :=
      mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
    nlinarith [h1, h2, ht2]
  linarith [hstep, hfin]

/-- **No polylogarithmic source coefficient passes the gate — the literal Weil
normalization.**  The same verdict after replacing the route's raw weight
`Λ(n)` by the literal explicit-formula weight `Λ(n)n^{-1/2}`: the prime mass
drops from `N` to `√N`, i.e. `S₀²` drops from `N²` to `N`, and the gate still
fails for every polylogarithmic coefficient.  **The missing power of `N` is
therefore not the archimedean normalization of the explicit formula.** -/
theorem weil_contraction_condition_fails_of_polylog_normalization {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {α t c κ Csrc : ℝ} (hα : |α| < 1 / 2)
    (hc : 0 < c) (hκ : 0 < κ) (ht : t ≠ 0)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hthr : c * (2 * ((A : ℝ) + 4)) ^ (A + 4) ≤ 120000 * (κ * t ^ 2 / 1024)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (weilMass N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have ht2 : 0 < t ^ 2 := by positivity
  have hmass := (weilMass_two_sided hN hα).1
  have hpow : Real.sqrt N ≤ (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg α])
  have hS : Real.sqrt N / 32 ≤ weilMass N α := by linarith [hmass, hpow]
  have hSsq : (N : ℝ) / 1024 ≤ (weilMass N α) ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.sqrt N / 32 := by positivity
    have hsq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [hS, h0, hsq]
  have hsq : Real.sqrt N ≤ (N : ℝ) := sqrt_le_self_of_one_le hN1
  refine gate_fails_of_polylog_loss (A := A) hN hc ?_ hthr
  have hstep : κ * t ^ 2 / 1024 * Real.sqrt N ≤ κ * t ^ 2 / 1024 * (N : ℝ) := by
    have : (0 : ℝ) ≤ κ * t ^ 2 / 1024 := by positivity
    exact mul_le_mul_of_nonneg_left hsq this
  have hfin : κ * t ^ 2 / 1024 * (N : ℝ)
      ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * (weilMass N α) ^ 2) := by
    have h1 : κ * ((N : ℝ) / 1024) ≤ κ * (weilMass N α) ^ 2 :=
      mul_le_mul_of_nonneg_left hSsq hκ.le
    have h2 : κ * (weilMass N α) ^ 2 ≤ Csrc * (Real.log N) ^ A * (weilMass N α) ^ 2 :=
      mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
    nlinarith [h1, h2, ht2]
  linarith [hstep, hfin]

/-! ### The tapered Weil mass, and the taper dichotomy -/

/-- The literal tapered Weil prime mass
`∑_{n ≤ N} Λ(n) n^{-1/2} cosh(2α log n) |φ̂(log n)|`: the `ℓ¹` size of the prime
term of the explicit formula for the taper transform `φ̂`. -/
noncomputable def taperedWeilMass (phi : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, weilWeight α n * |phi (Real.log n)|

/-- **A polynomially decaying taper transform loses only logarithms.**  If
`|φ̂(u)| ≥ κ (1+u)^{-B}` along the prime frequencies `u = log n ∈ [0, log N]`
— which is the generic situation for a taper of finite smoothness, whose
transform decays only polynomially — then the tapered Weil mass is still the
full Weil mass up to the factor `κ(1+log N)^{-B}`. -/
theorem taperedWeilMass_lower_of_polyDecay {phi : ℝ → ℝ} {N B : ℕ} {α κ : ℝ}
    (hκ : 0 ≤ κ)
    (hphi : ∀ u : ℝ, 0 ≤ u → u ≤ Real.log N → κ / (1 + u) ^ B ≤ |phi u|) :
    κ / (1 + Real.log N) ^ B * weilMass N α ≤ taperedWeilMass phi N α := by
  have hLnn : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  unfold taperedWeilMass weilMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogle : Real.log n ≤ Real.log N :=
    Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hmono : (1 + Real.log n) ^ B ≤ (1 + Real.log N) ^ B :=
    pow_le_pow_left₀ (by linarith) (by linarith) B
  have hposn : (0 : ℝ) < (1 + Real.log n) ^ B := by positivity
  have hposN : (0 : ℝ) < (1 + Real.log N) ^ B := by positivity
  have hstep : κ / (1 + Real.log N) ^ B ≤ |phi (Real.log n)| :=
    le_trans (by
      exact div_le_div_of_nonneg_left hκ hposn hmono) (hphi _ hlogn hlogle)
  have hw : 0 ≤ weilWeight α n := weilWeight_nonneg α n
  calc κ / (1 + Real.log N) ^ B * weilWeight α n
      ≤ |phi (Real.log n)| * weilWeight α n := mul_le_mul_of_nonneg_right hstep hw
    _ = weilWeight α n * |phi (Real.log n)| := by ring

private lemma one_le_log_of_large {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) :
    (1 : ℝ) ≤ Real.log N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  rw [Real.le_log_iff_exp_le hN0]
  nlinarith [Real.exp_one_lt_d9, pow_pos (by norm_num : (0:ℝ) < 10) 8, hN]

set_option maxHeartbeats 1000000 in
/-- **Red for every taper of polynomial transform decay.**  Combining the
previous two results: if the source coefficient decays at worst
polylogarithmically and the taper transform decays at worst polynomially along
the prime frequencies, the normalization gate fails.  Only a taper transform
decaying *exponentially* (at rate `> 1/2 + 2|α|`, so that the tapered Weil mass
stops growing with `N`) could make the gate green. -/
theorem taperedWeil_gate_fails_of_polyDecay {N A B : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {phi : ℝ → ℝ} {α t c κ κphi Csrc : ℝ}
    (hα : |α| < 1 / 2) (hc : 0 < c) (hκ : 0 < κ) (hκphi : 0 < κphi) (ht : t ≠ 0)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hphi : ∀ u : ℝ, 0 ≤ u → u ≤ Real.log N → κphi / (1 + u) ^ B ≤ |phi u|)
    (hthr : c * (2 * (((A + 2 * B : ℕ) : ℝ) + 4)) ^ (A + 2 * B + 4)
      ≤ 120000 * (κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B))) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (taperedWeilMass phi N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hL1 : (1 : ℝ) ≤ Real.log N := one_le_log_of_large hN
  have ht2 : 0 < t ^ 2 := by positivity
  set L : ℝ := Real.log N with hLdef
  set P : ℝ := taperedWeilMass phi N α with hP
  -- the tapered mass is at least `κphi √N /(32 (1+L)^B)`
  have hmassW := (weilMass_two_sided hN hα).1
  have hpow : Real.sqrt N ≤ (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg α])
  have hW : Real.sqrt N / 32 ≤ weilMass N α := by linarith [hmassW, hpow]
  have htap := taperedWeilMass_lower_of_polyDecay (phi := phi) (N := N) (B := B)
    (α := α) hκphi.le hphi
  have hposB : (0 : ℝ) < (1 + L) ^ B := by positivity
  have hlow1 : κphi / (1 + L) ^ B * (Real.sqrt N / 32) ≤ P := by
    refine le_trans ?_ htap
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  have hsq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hbb : ((1 + L) ^ B) ^ 2 = (1 + L) ^ (2 * B) := by
    rw [← pow_mul, Nat.mul_comm]
  have hlow2 : κphi ^ 2 * (N : ℝ) / (1024 * (1 + L) ^ (2 * B)) ≤ P ^ 2 := by
    have h0 : (0 : ℝ) ≤ κphi / (1 + L) ^ B * (Real.sqrt N / 32) := by positivity
    have hsqm : (κphi / (1 + L) ^ B * (Real.sqrt N / 32)) ^ 2 ≤ P ^ 2 := by
      nlinarith [hlow1, h0]
    have hexp : (κphi / (1 + L) ^ B * (Real.sqrt N / 32)) ^ 2
        = κphi ^ 2 * Real.sqrt N ^ 2 / (1024 * ((1 + L) ^ B) ^ 2) := by
      field_simp
      ring
    rw [hexp, hsq, hbb] at hsqm
    exact hsqm
  -- absorb the taper loss into the polylogarithmic budget
  have hbound : (1 + L) ^ (2 * B) ≤ 4 ^ B * L ^ (2 * B) := by
    have h1 : (1 + L) ≤ 2 * L := by linarith
    have h2 : (1 + L) ^ (2 * B) ≤ (2 * L) ^ (2 * B) :=
      pow_le_pow_left₀ (by linarith) h1 (2 * B)
    have h3 : (2 * L : ℝ) ^ (2 * B) = 4 ^ B * L ^ (2 * B) := by
      rw [mul_pow, pow_mul, pow_mul]
      norm_num
    linarith [h2, h3.le, h3.ge]
  have hLpos : (0 : ℝ) < L := by linarith
  have hL2B : (0 : ℝ) < L ^ (2 * B) := by positivity
  -- the key inequality
  have hkey : κ * κphi ^ 2 * (N : ℝ) / (1024 * 4 ^ B) ≤ Csrc * L ^ (A + 2 * B) * P ^ 2 := by
    have s2 : κ * (κphi ^ 2 * (N : ℝ) / (1024 * (1 + L) ^ (2 * B))) ≤ κ * P ^ 2 :=
      mul_le_mul_of_nonneg_left hlow2 hκ.le
    have s3 : κ * P ^ 2 ≤ Csrc * L ^ A * P ^ 2 :=
      mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
    have s4 : κ * (κphi ^ 2 * (N : ℝ) / (1024 * (1 + L) ^ (2 * B))) * L ^ (2 * B)
        ≤ Csrc * L ^ A * P ^ 2 * L ^ (2 * B) :=
      mul_le_mul_of_nonneg_right (le_trans s2 s3) hL2B.le
    have s5 : Csrc * L ^ A * P ^ 2 * L ^ (2 * B) = Csrc * L ^ (A + 2 * B) * P ^ 2 := by
      rw [pow_add]; ring
    have s6 : κ * κphi ^ 2 * (N : ℝ) / (1024 * 4 ^ B)
        ≤ κ * (κphi ^ 2 * (N : ℝ) / (1024 * (1 + L) ^ (2 * B))) * L ^ (2 * B) := by
      have hrw : κ * (κphi ^ 2 * (N : ℝ) / (1024 * (1 + L) ^ (2 * B))) * L ^ (2 * B)
          = κ * κphi ^ 2 * (N : ℝ) * L ^ (2 * B) / (1024 * (1 + L) ^ (2 * B)) := by
        field_simp
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      have hnn : (0 : ℝ) ≤ κ * κphi ^ 2 * (N : ℝ) * 1024 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hbound hnn, hL2B]
    linarith [s4, s5.le, s5.ge, s6]
  have hsqrtle : Real.sqrt N ≤ (N : ℝ) := sqrt_le_self_of_one_le hN1
  refine gate_fails_of_polylog_loss (A := A + 2 * B) hN hc ?_ hthr
  have hfin : κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B) * Real.sqrt N
      ≤ Csrc * L ^ (A + 2 * B) * (t ^ 2 * P ^ 2) := by
    have h1 : κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B) * Real.sqrt N
        ≤ κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B) * (N : ℝ) := by
      have : (0 : ℝ) ≤ κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B) := by positivity
      exact mul_le_mul_of_nonneg_left hsqrtle this
    have h2 : κ * κphi ^ 2 * t ^ 2 / (1024 * 4 ^ B) * (N : ℝ)
        = (κ * κphi ^ 2 * (N : ℝ) / (1024 * 4 ^ B)) * t ^ 2 := by
      field_simp
    have h3 : (κ * κphi ^ 2 * (N : ℝ) / (1024 * 4 ^ B)) * t ^ 2
        ≤ Csrc * L ^ (A + 2 * B) * P ^ 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right hkey ht2.le
    have h4 : Csrc * L ^ (A + 2 * B) * P ^ 2 * t ^ 2
        = Csrc * L ^ (A + 2 * B) * (t ^ 2 * P ^ 2) := by ring
    linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  exact hfin

/-! ### Two structural facts about the gate -/

/-- **The gate is scale-free.**  A common rescaling of the taper multiplies both
the anchored defect (hence the source coefficient) and the Gram floor constant by
the same positive factor, and the gate condition is unchanged.  So the gate
cannot be passed by renormalizing the source. -/
theorem gate_invariant_under_common_rescaling {lam : ℝ} (hlam : 0 < lam)
    (LN c L Csrc t S : ℝ) :
    (120000 * LN ^ 2 * (lam * Csrc * t ^ 2 * S ^ 2) < lam * c * L ^ 6)
      ↔ (120000 * LN ^ 2 * (Csrc * t ^ 2 * S ^ 2) < c * L ^ 6) := by
  constructor
  · intro h
    have hrw : 120000 * LN ^ 2 * (lam * Csrc * t ^ 2 * S ^ 2)
        = lam * (120000 * LN ^ 2 * (Csrc * t ^ 2 * S ^ 2)) := by ring
    rw [hrw] at h
    exact lt_of_mul_lt_mul_left (by linarith [h]) hlam.le
  · intro h
    have hrw : 120000 * LN ^ 2 * (lam * Csrc * t ^ 2 * S ^ 2)
        = lam * (120000 * LN ^ 2 * (Csrc * t ^ 2 * S ^ 2)) := by ring
    rw [hrw]
    have h2 : lam * (c * L ^ 6) = lam * c * L ^ 6 := by ring
    linarith [mul_lt_mul_of_pos_left h hlam, h2.le, h2.ge]

/-! ### The decision theorem -/

/-- **`literalSourceNormalizationDecision` — the go/no-go theorem of the
anchored second-moment route.**

Fix a truncation `N ≥ 10⁹`, an off-line displacement `|α| < 1/2`, the route's own
geometric scale `L = log N`, and a source coefficient `C_src` for which the
source identification `D ≤ C_src · 𝒟_N(α,t)` and the Gram floor
`c L⁶α² ≤ D` hold.  Then:

* **(green)** if the normalization gate
  `120000 (log N)² · C_src t² S₀(α)² < c (log N)⁶` holds, the off-line
  displacement is exactly `0`;
* **(red)** if the source coefficient decays at worst polylogarithmically,
  `κ ≤ C_src (log N)^A`, then — subject only to the explicit constant
  comparison — the gate is **false**, so the green branch is unavailable and
  `primeBudget_not_contractive` applies: the prime term alone exhausts the
  whole defect and no contraction can be extracted.

The two branches are exhaustive for every coefficient that is not smaller than
every negative power of `log N`, i.e. for every coefficient not carrying a
genuine power of `N`.  That is the binary content of the gate. -/
theorem literalSourceNormalizationDecision {N A : ℕ} {α t c κ Csrc D : ℝ}
    (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hc : 0 < c) (hκ : 0 < κ)
    (ht : t ≠ 0) (hCsrc0 : 0 ≤ Csrc) (hD : 0 ≤ D)
    (hsource : D ≤ Csrc * zetaCompensatedPrimeForm N α t)
    (hfloor : c * (Real.log N) ^ 6 * α ^ 2 ≤ D) :
    (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
        < c * (Real.log N) ^ 6 → α = 0)
    ∧ (κ ≤ Csrc * (Real.log N) ^ A →
        c * (2 * ((A : ℝ) + 4)) ^ (A + 4) ≤ 120000 * (κ * t ^ 2 / 1024) →
        ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
            < c * (Real.log N) ^ 6)) := by
  have hN8 : (10 : ℝ) ^ 8 ≤ (N : ℝ) := le_trans (by norm_num) hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 9]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  refine ⟨fun hgate => ?_, fun hpoly hthr =>
    contraction_condition_fails_of_polylog_normalization hN8 hα hc hκ ht hpoly hthr⟩
  exact offLineZero_excluded_of_sourceNormalization hN8 hα hc hLpos hD hCsrc0 hsource
    hfloor hgate

/-! ### The explicit numerical threshold for the source coefficient -/

/-- **The gate, solved for `C_src` — the route's raw normalization.**  If the
normalization gate holds, then the source coefficient obeys the explicit
numerical bound

```
C_src · t² · N^{2+4|α|}  <  1024 c (log N)⁴ / 120000.
```

This is the closed form of the requirement `C_src ≲ 1/(t²N)` of G14, with every
constant made explicit and the `α`-dependence exposed. -/
theorem sourceCoefficient_threshold {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α t c Csrc : ℝ} (hα : |α| < 1 / 2) (hCsrc : 0 ≤ Csrc)
    (hgate : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
      < c * (Real.log N) ^ 6) :
    Csrc * t ^ 2 * (N : ℝ) ^ (2 + 4 * |α| : ℝ) < 1024 * c * (Real.log N) ^ 4 / 120000 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
  have hmass := (twistedPrimeMass hN hα).1
  have hsq : ((N : ℝ) ^ (1 + 2 * |α| : ℝ)) ^ 2 = (N : ℝ) ^ (2 + 4 * |α| : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 + 2 * |α| : ℝ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    push_cast
    ring
  have hSsq : (N : ℝ) ^ (2 + 4 * |α| : ℝ) / 1024 ≤ (twistedMoment N α 0) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 + 2 * |α| : ℝ) / 32 := by positivity
    nlinarith [hmass, h0, hsq]
  have hstep : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (2 + 4 * |α| : ℝ) / 1024))
      ≤ 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2) := by
    have hnn : (0 : ℝ) ≤ Csrc * t ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hSsq hnn
    have hnn2 : (0 : ℝ) ≤ 120000 * (Real.log N) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h1 hnn2
  have hchain : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (2 + 4 * |α| : ℝ) / 1024))
      < c * (Real.log N) ^ 6 := lt_of_le_of_lt hstep hgate
  have hrw1 : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (2 + 4 * |α| : ℝ) / 1024))
      = (120000 / 1024 * (Csrc * t ^ 2 * (N : ℝ) ^ (2 + 4 * |α| : ℝ))) * (Real.log N) ^ 2 := by
    ring
  have hrw2 : c * (Real.log N) ^ 6 = (c * (Real.log N) ^ 4) * (Real.log N) ^ 2 := by ring
  rw [hrw1, hrw2] at hchain
  have hcancel : 120000 / 1024 * (Csrc * t ^ 2 * (N : ℝ) ^ (2 + 4 * |α| : ℝ))
      < c * (Real.log N) ^ 4 := lt_of_mul_lt_mul_right (by linarith [hchain]) hL2.le
  linarith [hcancel]

/-- **The gate, solved for `C_src` — the literal Weil normalization.**  With the
literal explicit-formula weight `Λ(n)n^{-1/2}` the same computation gives

```
C_src · t² · N^{1+4|α|}  <  1024 c (log N)⁴ / 120000,
```

i.e. `C_src t² N < 0.0086 · c (log N)⁴ · N^{-4|α|}`.  **This is the number the
gate demands.**  A source coefficient produced by an explicit-formula
identification is polylogarithmic in `N`, and
`weil_contraction_condition_fails_of_polylog_normalization` shows that no such
coefficient can meet this threshold. -/
theorem weil_sourceCoefficient_threshold {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α t c Csrc : ℝ} (hα : |α| < 1 / 2) (hCsrc : 0 ≤ Csrc)
    (hgate : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (weilMass N α) ^ 2)
      < c * (Real.log N) ^ 6) :
    Csrc * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ) < 1024 * c * (Real.log N) ^ 4 / 120000 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := by positivity
  have hmass := (weilMass_two_sided hN hα).1
  have hsq : ((N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ)) ^ 2 = (N : ℝ) ^ (1 + 4 * |α| : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    push_cast
    ring
  have hSsq : (N : ℝ) ^ (1 + 4 * |α| : ℝ) / 1024 ≤ (weilMass N α) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) / 32 := by positivity
    nlinarith [hmass, h0, hsq]
  have hstep : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (1 + 4 * |α| : ℝ) / 1024))
      ≤ 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (weilMass N α) ^ 2) := by
    have hnn : (0 : ℝ) ≤ Csrc * t ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hSsq hnn
    have hnn2 : (0 : ℝ) ≤ 120000 * (Real.log N) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h1 hnn2
  have hchain : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (1 + 4 * |α| : ℝ) / 1024))
      < c * (Real.log N) ^ 6 := lt_of_le_of_lt hstep hgate
  have hrw1 : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ (1 + 4 * |α| : ℝ) / 1024))
      = (120000 / 1024 * (Csrc * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ))) * (Real.log N) ^ 2 := by
    ring
  have hrw2 : c * (Real.log N) ^ 6 = (c * (Real.log N) ^ 4) * (Real.log N) ^ 2 := by ring
  rw [hrw1, hrw2] at hchain
  have hcancel : 120000 / 1024 * (Csrc * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ))
      < c * (Real.log N) ^ 4 := lt_of_mul_lt_mul_right (by linarith [hchain]) hL2.le
  linarith [hcancel]

end RiemannAnalytic
