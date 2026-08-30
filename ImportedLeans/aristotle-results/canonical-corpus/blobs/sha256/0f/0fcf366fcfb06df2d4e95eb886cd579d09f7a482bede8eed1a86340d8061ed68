/-
# G18 — the literal source identity, the closed source coefficient, and the
go/no-go verdict of the raw-anchor architecture

The previous cycles reduced the whole anchored second-moment route to a single
scalar comparison, the **normalization gate**

```
120000 (log N)² · C_src t² S₀(α)²   <   c (log N)⁶,
```

and left one thing unexposed: the source coefficient `C_src` itself.  This
module computes it, from the literal Weil normalization, and reads off the
verdict.

## 1.  The literal compensated-anchor explicit formula

`literalCompensatedAnchorExplicitFormula` isolates the anchor of one zero in the
literal Riemann–Weil explicit formula for the *grid* test family

```
g_x(u) = φ(u) e^{-i x u},      x = k h,   h = 2π/L,
```

whose complex Fourier transform (normalization `∫ g(u) e^{-izu} du`, no `2π` in
the exponent and no `(2π)^{-1/2}` in front) is the grid sample
`ĝ_x(z) = φ̂(z + x)`.  The conclusion is the exact identity

```
m_ρ · φ̂(z_ρ + x) = − P_N(φ, x) + R_EF − R_zero,
```

with

* `z_ρ = −i(ρ − ½)` the Weil coordinate of the zero (`zeroCoord`),
* `P_N(φ,x) = 2 ∑_{n ≤ N} Λ(n) n^{-1/2} φ(log n) cos(x log n)` the literal Weil
  prime term, **finite**: the taper's support `[-L, L]` truncates it at
  `N ≥ e^L` exactly (`weilPrimeTerm_gridTest_eq_finite`),
* `R_EF` the archimedean/pole functional of the same test function,
* `R_zero = ∑_{j ≠ j₀} m_j φ̂(z_j + x)` the contribution of all the other zeros.

Everything is literal: `Λ` is the von Mangoldt function, the zeros are genuine
zeros of Mathlib's `completedRiemannZeta` (carried in `ZeroData`), the taper is
an actual function and `φ̂` an actual integral.  The Riemann–Weil formula itself
is **not** proved here — Mathlib has no explicit formula — it is carried as the
explicit hypothesis `WeilExplicitFormula`, and every theorem that uses it says
so in its statement.  What is proved is everything else: the transform identity
for the grid family, the exact truncation of the prime series, and the
isolation of the anchor from the zero sum.

**The decisive feature of the identity is that the coefficient of the prime
term is the absolute constant `1`.**  No power of `N`, no `L^{-1}`, no
`X^{-1/2}`, no Fourier factor: the literal Weil normalization multiplies the
prime side by nothing at all.

## 2.  The closed source coefficient

`literalSourceCoefficient_eq`: for a taper that is `1` along the prime
frequencies `log n`, `n ≤ N` (the plateau the source-side Gram floor demands),

```
P_N(φ, 0) = 2 · S₀^W(0) = 2 ∑_{n ≤ N} Λ(n) n^{-1/2},
```

a closed elementary expression, and `N^{1/2}/16 ≤ P_N(φ,0) ≤ 1618 N^{1/2}`
(`literalSourceCoefficient_bounds`).  Consequently the coefficient the gate
consumes,

```
C_src = P_N(φ,0) / S₀^W(α)²,
```

satisfies `C_src · S₀^W(α)² = 2 S₀^W(0) ≍ N^{1/2}`: the literal identification
supplies the normalization `N^{-1/2-4|α|}`, whereas the gate needs
`N^{-1-4|α|} (log N)^4`.  **It is short by exactly `N^{1/2}/(log N)^4`** — the
square root of the required `1/N`.

## 3.  The verdict

`literalSourceRatioDecision`: with

```
Ξ(N,α) = 120000 · C_src · t² · N^{1+4|α|} / (1024 c (log N)^4)
```

one has `Ξ ≥ t² N^{1/4} / (10¹⁰ c)` for every `N ≥ 10⁸` and every `|α| < 1/2`,
so `Ξ → ∞`, **uniformly in `0 < |α| < 1/2`**
(`literalSourceRatioDecision_tendsto`).  The `α`-dependence cancels exactly.
This is the third of the three outcomes: `liminf Ξ ≥ 1`, indeed `Ξ → ∞`.

`literalRawAnchorGateFails` states the same verdict in the gate's own terms: the
contraction condition is **false** for the literal Weil normalization once
`c (log N)^4 ≤ 7500 t² N^{1/2}`, and `literalRawAnchorGateFails_of_large` turns
that into an explicit threshold in `N`.  So the raw-anchor architecture cannot
close, and the deficit is a full power `N^{1/2}`, not a matter of constants.

Nothing here proves the Riemann Hypothesis, nothing here is assumed elsewhere,
and no `sorry`, `axiom`, postulate or numerical receipt appears.
-/
import RiemannAnalytic.SubexponentialTaperGate
import RiemannAnalytic.PoissonExtension
import RiemannAnalytic.Detectability

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ### The complex-valued transform and the grid test family -/

/-- The Fourier transform used throughout, extended to complex-valued test
functions: `ĝ(z) = ∫ g(u) e^{-izu} du`.  On real test functions it is `PhiExt`.
There is no `2π` in the exponent and no normalizing prefactor; this is the
convention in which the Weil prime weight is `Λ(n) n^{-1/2}`. -/
noncomputable def PhiExtC (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, g t * Complex.exp (-(Complex.I * z * (t : ℂ)))

theorem PhiExtC_ofReal (φ : ℝ → ℝ) (z : ℂ) :
    PhiExtC (fun u => (φ u : ℂ)) z = PhiExt φ z := rfl

/-- The grid test family `g_x(u) = φ(u) e^{-ixu}`.  For `x = k h`, `h = 2π/L`,
these are exactly the test functions whose transforms are the grid samples of
the anchored window. -/
noncomputable def gridTest (φ : ℝ → ℝ) (x : ℝ) : ℝ → ℂ :=
  fun u => (φ u : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (u : ℂ)))

/-- **The grid sample is the transform of the grid test function**:
`ĝ_x(z) = φ̂(z + x)`. -/
theorem PhiExtC_gridTest (φ : ℝ → ℝ) (x : ℝ) (z : ℂ) :
    PhiExtC (gridTest φ x) z = PhiExt φ (z + (x : ℂ)) := by
  unfold PhiExtC PhiExt gridTest
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (φ u : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (u : ℂ)))
      * Complex.exp (-(Complex.I * z * (u : ℂ)))
    = (φ u : ℂ) * Complex.exp (-(Complex.I * (z + (x : ℂ)) * (u : ℂ)))
  have harg : -(Complex.I * (x : ℂ) * (u : ℂ)) + -(Complex.I * z * (u : ℂ))
      = -(Complex.I * (z + (x : ℂ)) * (u : ℂ)) := by ring
  rw [mul_assoc, ← Complex.exp_add, harg]

/-! ### The literal Weil prime term -/

/-- The literal prime side of the Riemann–Weil explicit formula for a test
function `g`:  `P(g) = ∑_{n} Λ(n) n^{-1/2} (g(log n) + g(−log n))`. -/
noncomputable def weilPrimeTerm (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))

/-- The literal Weil prime term of the grid test function, as a finite real
sum: `P_N(φ,x) = 2 ∑_{n ≤ N} Λ(n) n^{-1/2} φ(log n) cos(x log n)`. -/
noncomputable def weilGridPrimeSum (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * φ (Real.log n) * Real.cos (x * Real.log n)

/-- **Exact truncation of the prime series.**  For a real even taper supported
in `[-L, L]` and a truncation `N` with `e^L < N + 1`, the prime side of the
explicit formula for the grid test function is the finite sum
`P_N(φ,x)`; no tail is discarded. -/
theorem weilPrimeTerm_gridTest_eq_finite {φ : ℝ → ℝ} {L : ℝ} {N : ℕ} (x : ℝ)
    (hev : ∀ u, φ (-u) = φ u) (hsupp : ∀ u, L < |u| → φ u = 0)
    (hN : Real.exp L < (N : ℝ) + 1) :
    weilPrimeTerm (gridTest φ x) = ((weilGridPrimeSum φ N x : ℝ) : ℂ) := by
  have key : ∀ w : ℂ, Complex.exp (-(Complex.I * w)) + Complex.exp (Complex.I * w)
      = 2 * Complex.cos w := by
    intro w
    have h1 : w * Complex.I = Complex.I * w := mul_comm _ _
    have h2 : -w * Complex.I = -(Complex.I * w) := by ring
    rw [Complex.two_cos, h1, h2, add_comm]
  have hzero : ∀ n ∉ Icc 1 N, ((Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
      * (gridTest φ x (Real.log n) + gridTest φ x (-Real.log n)) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hnN : N < n := by
        simp only [Finset.mem_Icc, not_and, not_le] at hn
        exact hn hpos
      have hnR : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnN
      have hlog : L < Real.log n := by
        rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos L])]
        linarith
      have hlognn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have h1 : φ (Real.log n) = 0 := hsupp _ (by rwa [abs_of_nonneg hlognn])
      have h2 : φ (-Real.log n) = 0 := by rw [hev]; exact h1
      simp [gridTest, h1, h2]
  rw [weilPrimeTerm, tsum_eq_sum hzero]
  unfold weilGridPrimeSum
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [gridTest]
  rw [hev]
  have hswap : -(Complex.I * (x : ℂ) * ((-Real.log n : ℝ) : ℂ))
      = Complex.I * ((x * Real.log n : ℝ) : ℂ) := by push_cast; ring
  have hswap2 : -(Complex.I * (x : ℂ) * ((Real.log n : ℝ) : ℂ))
      = -(Complex.I * ((x * Real.log n : ℝ) : ℂ)) := by push_cast; ring
  rw [hswap, hswap2, ← mul_add, key]
  push_cast
  ring

/-! ### The literal explicit formula as an explicit hypothesis -/

/-- Literal data for the nontrivial zeros: an enumeration `zeros` of genuine
zeros of Mathlib's `completedRiemannZeta`, with positive multiplicities. -/
structure ZeroData where
  /-- The enumerated zeros. -/
  zeros : ℕ → ℂ
  /-- Their multiplicities. -/
  mult : ℕ → ℝ
  /-- Every enumerated point is a genuine zero of the completed zeta function. -/
  hzero : ∀ j, completedRiemannZeta (zeros j) = 0
  /-- Multiplicities are positive. -/
  hmult : ∀ j, 0 < mult j

/-- **The literal Riemann–Weil explicit formula for one test function**, in the
transform normalization `ĝ(z) = ∫ g(u)e^{-izu} du`:

```
∑_j m_j ĝ(z_j)  =  A(g) − ∑_n Λ(n) n^{-1/2} (g(log n) + g(−log n)),
```

`z_j = −i(ρ_j − ½)` the Weil coordinates of the zeros and `A(g)` the
archimedean-plus-pole functional.  This statement is **not proved** anywhere in
this development; it is carried as an explicit hypothesis by every theorem
below that uses it. -/
def WeilExplicitFormula (Z : ZeroData) (arch : ℂ) (g : ℝ → ℂ) : Prop :=
  ∑' j : ℕ, (Z.mult j : ℂ) * PhiExtC g (zeroCoord (Z.zeros j)) = arch - weilPrimeTerm g

/-- The other-zeros remainder of the anchored identity:
`R_zero = ∑_{j ≠ j₀} m_j φ̂(z_j + x)`. -/
noncomputable def zeroRemainder (Z : ZeroData) (φ : ℝ → ℝ) (x : ℝ) (j₀ : ℕ) : ℂ :=
  ∑' j : ℕ, if j = j₀ then 0
    else (Z.mult j : ℂ) * PhiExt φ (zeroCoord (Z.zeros j) + (x : ℂ))

/-- **The hypotheses of the anchored identity are consistent.**  For any zero
data, any test function and any value of the zero sum, the archimedean/pole
value can be chosen so that the Weil-formula hypothesis holds.  So
`literalCompensatedAnchorExplicitFormula` below is not vacuous: its hypothesis
is a genuine constraint linking `arch` to the zero and prime sides, not an
inconsistent one. -/
theorem weilExplicitFormula_consistent (Z : ZeroData) (g : ℝ → ℂ) :
    ∃ arch : ℂ, WeilExplicitFormula Z arch g :=
  ⟨(∑' j : ℕ, (Z.mult j : ℂ) * PhiExtC g (zeroCoord (Z.zeros j))) + weilPrimeTerm g, by
    unfold WeilExplicitFormula; ring⟩

/-- **The literal compensated-anchor explicit formula.**

For a real even taper `φ` supported in `[-L, L]`, a truncation `N` with
`e^L < N + 1`, a grid frequency `x` and a distinguished zero `ρ = Z.zeros j₀`
of the completed zeta function, the literal Riemann–Weil formula for the grid
test function `g_x(u) = φ(u)e^{-ixu}` gives the exact identity

```
m_ρ · φ̂(z_ρ + x)  =  − P_N(φ, x)  +  R_EF  −  R_zero,
```

where `P_N(φ,x) = 2 ∑_{n ≤ N} Λ(n) n^{-1/2} φ(log n) cos(x log n)` is the
literal Weil prime term, `R_EF = arch` the archimedean/pole functional of the
same test function and `R_zero` the contribution of the other zeros.

**The coefficient of the prime term is `1`.**  Every occurrence of `L`,
`h = 2π/L`, `X = e^L`, `N`, `φ̂` and `m_ρ` in the identity is displayed: `L` and
`X` only through the truncation `N`, `h` only through `x = kh`, `φ̂` as the
anchor itself, and `m_ρ` as the linear factor on the left.  No power of `N` and
no Fourier normalization factor multiplies the prime side. -/
theorem literalCompensatedAnchorExplicitFormula {φ : ℝ → ℝ} {L : ℝ} {N : ℕ} {x : ℝ}
    (Z : ZeroData) (arch : ℂ) (j₀ : ℕ)
    (hev : ∀ u, φ (-u) = φ u) (hsupp : ∀ u, L < |u| → φ u = 0)
    (hN : Real.exp L < (N : ℝ) + 1)
    (hsummable : Summable fun j : ℕ =>
      (Z.mult j : ℂ) * PhiExtC (gridTest φ x) (zeroCoord (Z.zeros j)))
    (hEF : WeilExplicitFormula Z arch (gridTest φ x)) :
    (Z.mult j₀ : ℂ) * PhiExt φ (zeroCoord (Z.zeros j₀) + (x : ℂ))
      = -((weilGridPrimeSum φ N x : ℝ) : ℂ) + arch - zeroRemainder Z φ x j₀ := by
  have hsplit := hsummable.tsum_eq_add_tsum_ite j₀
  rw [WeilExplicitFormula, hsplit,
    weilPrimeTerm_gridTest_eq_finite (L := L) (N := N) x hev hsupp hN] at hEF
  simp only [PhiExtC_gridTest] at hEF
  unfold zeroRemainder
  linear_combination hEF

/-! ### The closed source coefficient -/

/-- **The literal source coefficient, in closed form.**  If the taper equals `1`
along the prime frequencies `log n`, `n ≤ N` — the plateau the source-side Gram
floor demands — the literal Weil prime term of the anchor `x = 0` is exactly
twice the literal Weil prime mass at `α = 0`:

```
P_N(φ, 0) = 2 ∑_{n ≤ N} Λ(n) n^{-1/2} = 2 S₀^W(0).
```

This is the closed elementary expression the gate's fate depends on. -/
theorem literalSourceCoefficient_eq {φ : ℝ → ℝ} {N : ℕ}
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    weilGridPrimeSum φ N 0 = 2 * weilMass N 0 := by
  unfold weilGridPrimeSum weilMass weilWeight
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hplat n hn]
  norm_num

/-- **The size of the literal prime term**: `N^{1/2}/16 ≤ P_N(φ,0) ≤ 1618 N^{1/2}`.
It carries a full half-power of `N` and no decay whatsoever. -/
theorem literalSourceCoefficient_bounds {φ : ℝ → ℝ} {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    (N : ℝ) ^ (1 / 2 : ℝ) / 16 ≤ weilGridPrimeSum φ N 0
      ∧ weilGridPrimeSum φ N 0 ≤ 1618 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hmass := weilMass_two_sided (α := 0) hN (by norm_num)
  rw [show (1 / 2 + 2 * |(0 : ℝ)| : ℝ) = 1 / 2 by norm_num] at hmass
  rw [literalSourceCoefficient_eq hplat]
  constructor <;> linarith [hmass.1, hmass.2]

/-- The source coefficient the normalization gate consumes: the literal Weil
prime term of the anchor, measured against the quadratic prime observable's
normalization `S₀^W(α)²`. -/
noncomputable def literalSourceCoefficient (φ : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℝ :=
  weilGridPrimeSum φ N 0 / weilMass N α ^ 2

/-- The defining relation of the source coefficient, cleared of denominators. -/
theorem literalSourceCoefficient_mul {φ : ℝ → ℝ} {N : ℕ} {α : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) :
    literalSourceCoefficient φ N α * weilMass N α ^ 2 = weilGridPrimeSum φ N 0 := by
  have hpos : 0 < weilMass N α := by
    have hmass := (weilMass_two_sided hN hα).1
    have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
    have : (0 : ℝ) < (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) := Real.rpow_pos_of_pos hN0 _
    linarith
  unfold literalSourceCoefficient
  field_simp

/-! ### The go/no-go decision -/

/-- The gate ratio `Ξ` of the contraction theorem:

```
Ξ(N,α) = 120000 · C_src · t² · N^{1+4|α|} / (1024 c (log N)^4).
```

The route survives iff `Ξ < 1`. -/
noncomputable def literalGateRatio (φ : ℝ → ℝ) (N : ℕ) (α t c : ℝ) : ℝ :=
  120000 * literalSourceCoefficient φ N α * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ)
    / (1024 * c * (Real.log N) ^ 4)

/-- **`literalSourceRatioDecision` — the exact go/no-go theorem.**

For every truncation `N ≥ 10⁸`, every off-line displacement `|α| < 1/2` and the
plateau taper of the source floor,

```
Ξ(N,α)  ≥  t² N^{1/4} / (10¹⁰ c).
```

The `α`-dependence cancels exactly: the literal normalization supplies
`N^{-1/2-4|α|}` where the gate needs `N^{-1-4|α|}(log N)^4`.  So the verdict is
the third of the three possible outcomes — `Ξ → ∞`, and the raw-anchor
architecture is dead by a full power `N^{1/2}`, not by constants. -/
theorem literalSourceRatioDecision {φ : ℝ → ℝ} {N : ℕ} {α t c : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hc : 0 < c)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) / (10 ^ 10 * c) ≤ literalGateRatio φ N α t c := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  have hden : (0 : ℝ) < 1024 * c * (Real.log N) ^ 4 := by positivity
  have hq : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hhalf : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hlog4 : (Real.log N) ^ 4 ≤ 65536 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := log_pow_le_mul_rpow N (k := 4) (by norm_num) (δ := 1 / 4) (by norm_num)
    norm_num at h
    linarith
  have hP := (literalSourceCoefficient_bounds hN hplat).1
  have hCnn : 0 ≤ literalSourceCoefficient φ N α := by
    unfold literalSourceCoefficient
    have : 0 ≤ weilGridPrimeSum φ N 0 := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 16 := by positivity
      linarith
    positivity
  have hmul := literalSourceCoefficient_mul (φ := φ) hN hα
  have hSupper := (weilMass_two_sided hN hα).2
  have hSnn : 0 ≤ weilMass N α := weilMass_nonneg N α
  have hsq : ((N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ)) ^ 2 = (N : ℝ) ^ (1 + 4 * |α| : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    push_cast
    ring
  have hSsq : (weilMass N α) ^ 2 ≤ 654481 * (N : ℝ) ^ (1 + 4 * |α| : ℝ) := by
    nlinarith [hSupper, hSnn, hsq, Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 + 2 * |α| : ℝ)]
  have hkey : weilGridPrimeSum φ N 0
      ≤ 654481 * (literalSourceCoefficient φ N α * (N : ℝ) ^ (1 + 4 * |α| : ℝ)) := by
    rw [← hmul]
    nlinarith [mul_le_mul_of_nonneg_left hSsq hCnn]
  have hCNP : (N : ℝ) ^ (1 / 2 : ℝ) / (16 * 654481)
      ≤ literalSourceCoefficient φ N α * (N : ℝ) ^ (1 + 4 * |α| : ℝ) := by
    linarith [hkey, hP]
  have hAlow : 120000 * t ^ 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / (16 * 654481))
      ≤ 120000 * literalSourceCoefficient φ N α * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ) := by
    have hnn : (0 : ℝ) ≤ 120000 * t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hCNP hnn]
  unfold literalGateRatio
  rw [div_le_div_iff₀ (by positivity) hden]
  have step1 : t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * (1024 * c * (Real.log N) ^ 4)
      ≤ t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * (1024 * c * (65536 * (N : ℝ) ^ (1 / 4 : ℝ))) := by
    have hnn : (0 : ℝ) ≤ t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * (1024 * c) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog4 hnn]
  have step2 : (120000 * t ^ 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / (16 * 654481))) * (10 ^ 10 * c)
      ≤ (120000 * literalSourceCoefficient φ N α * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ))
        * (10 ^ 10 * c) :=
    mul_le_mul_of_nonneg_right hAlow (by positivity)
  have step3 : t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * (1024 * c * (65536 * (N : ℝ) ^ (1 / 4 : ℝ)))
      ≤ (120000 * t ^ 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / (16 * 654481))) * (10 ^ 10 * c) := by
    rw [hhalf]
    nlinarith [mul_nonneg (mul_nonneg hc.le (sq_nonneg t)) (mul_pos hq hq).le]
  linarith

/-- **The verdict, in limit form and uniformly in `α`.**  For every target `M`
there is a threshold `N₀` beyond which the gate ratio exceeds `M` for *every*
off-line displacement `|α| < 1/2`. -/
theorem literalSourceRatioDecision_tendsto {t c : ℝ} (ht : t ≠ 0) (hc : 0 < c) (M : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ φ : ℝ → ℝ, (∀ n ∈ Icc 1 N, φ (Real.log n) = 1) →
      ∀ α : ℝ, |α| < 1 / 2 → M ≤ literalGateRatio φ N α t c := by
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  set K : ℝ := max 0 (M * (10 ^ 10 * c) / t ^ 2) with hK
  have hK0 : 0 ≤ K := le_max_left _ _
  refine ⟨10 ^ 8 + ⌈K ^ 4⌉₊, fun N hN₀ φ hplat α hα => ?_⟩
  have hNge : (10 : ℝ) ^ 8 + K ^ 4 ≤ (N : ℝ) := by
    have h1 : ((10 ^ 8 + ⌈K ^ 4⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀
    have h2 : K ^ 4 ≤ (⌈K ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    push_cast at h1
    linarith
  have hN : (10 : ℝ) ^ 8 ≤ (N : ℝ) := by nlinarith [pow_nonneg hK0 4]
  have hmain := literalSourceRatioDecision (t := t) hN hα hc hplat
  refine le_trans ?_ hmain
  rw [le_div_iff₀ (by positivity)]
  -- `M * (10^10 c) ≤ t² N^{1/4}`
  have hKle : K ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hle : K ^ 4 ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
    have h1 : (K ^ 4) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hle (by norm_num)
    have h2 : (K ^ 4) ^ (1 / 4 : ℝ) = K := by
      rw [← Real.rpow_natCast K 4, ← Real.rpow_mul hK0]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hMK : M * (10 ^ 10 * c) / t ^ 2 ≤ K := le_max_right _ _
  rw [div_le_iff₀ ht2] at hMK
  nlinarith [hKle, ht2, hMK]

/-- **The verdict in the gate's own terms: the contraction condition is false.**

For the literal Weil normalization the gate quantity is
`120000 (log N)² · C_src t² S₀^W(α)² = 240000 (log N)² t² S₀^W(0) ≍ t² N^{1/2}(log N)²`,
which exceeds `c (log N)^6` as soon as `c (log N)^4 ≤ 7500 t² N^{1/2}`.  So the
contraction condition of the anchored second-moment route **fails** for the
literal source coefficient. -/
theorem literalRawAnchorGateFails {φ : ℝ → ℝ} {N : ℕ} {α t c : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hbig : c * (Real.log N) ^ 4 ≤ 7500 * t ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ)) :
    ¬ (120000 * (Real.log N) ^ 2
        * (literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2)
      < c * (Real.log N) ^ 6) := by
  intro hgate
  have hmul := literalSourceCoefficient_mul (φ := φ) hN hα
  have hP := (literalSourceCoefficient_bounds hN hplat).1
  have hLHS : 120000 * (Real.log N) ^ 2
      * (literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2)
      = 120000 * (Real.log N) ^ 2 * t ^ 2 * weilGridPrimeSum φ N 0 := by
    rw [← hmul]; ring
  rw [hLHS] at hgate
  have hnn : (0 : ℝ) ≤ 120000 * (Real.log N) ^ 2 * t ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hP hnn
  have h2 := mul_le_mul_of_nonneg_right hbig (sq_nonneg (Real.log N))
  nlinarith [h1, h2]

/-- The same verdict with the threshold made explicit in `N`: the gate fails as
soon as `9 c / t² ≤ N^{1/4}`. -/
theorem literalRawAnchorGateFails_of_large {φ : ℝ → ℝ} {N : ℕ} {α t c : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hc : 0 < c) (ht : t ≠ 0)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hthr : 9 * c / t ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ)) :
    ¬ (120000 * (Real.log N) ^ 2
        * (literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2)
      < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hq : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hhalf : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hlog4 : (Real.log N) ^ 4 ≤ 65536 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := log_pow_le_mul_rpow N (k := 4) (by norm_num) (δ := 1 / 4) (by norm_num)
    norm_num at h
    linarith
  rw [div_le_iff₀ ht2] at hthr
  refine literalRawAnchorGateFails hN hα hplat ?_
  have h1 : c * (Real.log N) ^ 4 ≤ 65536 * c * (N : ℝ) ^ (1 / 4 : ℝ) := by
    nlinarith [hlog4, hc.le]
  have h2 : 65536 * c * (N : ℝ) ^ (1 / 4 : ℝ) ≤ 7500 * t ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    nlinarith [mul_le_mul_of_nonneg_right hthr hq.le]
  linarith

/-! ### The Schur-effective pivot inherits the verdict -/

/-- **`literalSchurSourceNormalizationDecision` — the Schur pivot cannot remove
the `N^{1/2}` deficit.**

Eliminating hidden directions replaces the geometric floor constant `c` by
`c/E` with `E ≥ 1` the energy of the eliminated block
(`SchurEliminationDefect.eliminationResidue_le_transverse`), which is the same
as replacing the source coefficient `C_src` by `E · C_src`.  The literal Weil
prime term is untouched by that pivot, so the Schur-effective gate ratio is at
least the raw one and still diverges:

```
E · Ξ(N,α)  ≥  t² N^{1/4} / (10¹⁰ c).
```

So `C_Schur t² N` is **not** `O(1)`: the Schur pivot is not the missing
normalization either, and the branch should not be pursued for that reason. -/
theorem literalSchurSourceNormalizationDecision {φ : ℝ → ℝ} {N : ℕ} {α t c E : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hc : 0 < c) (hE : 1 ≤ E)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) / (10 ^ 10 * c) ≤ E * literalGateRatio φ N α t c := by
  have hmain := literalSourceRatioDecision (φ := φ) (t := t) hN hα hc hplat
  have hnn : (0 : ℝ) ≤ t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) / (10 ^ 10 * c) := by positivity
  nlinarith [hmain, hnn, hE]

/-- The Schur-effective gate fails too: the contraction condition is false for
`E · C_src`, `E ≥ 1`, exactly as it is for `C_src`. -/
theorem literalSchurGateFails {φ : ℝ → ℝ} {N : ℕ} {α t c E : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hE : 1 ≤ E)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hbig : c * (Real.log N) ^ 4 ≤ 7500 * t ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ)) :
    ¬ (120000 * (Real.log N) ^ 2
        * (E * literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2)
      < c * (Real.log N) ^ 6) := by
  intro hgate
  refine literalRawAnchorGateFails hN hα hplat hbig ?_
  have hCnn : 0 ≤ literalSourceCoefficient φ N α := by
    unfold literalSourceCoefficient
    have hP := (literalSourceCoefficient_bounds hN hplat).1
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 16 := by positivity
    have : 0 ≤ weilGridPrimeSum φ N 0 := by linarith
    positivity
  have hnn : (0 : ℝ) ≤ 120000 * (Real.log N) ^ 2
      * (literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2) := by
    have := weilMass_nonneg N α
    positivity
  nlinarith [hgate, hnn, hE, hCnn, sq_nonneg (Real.log N), sq_nonneg t,
    sq_nonneg (weilMass N α)]

end RiemannAnalytic
