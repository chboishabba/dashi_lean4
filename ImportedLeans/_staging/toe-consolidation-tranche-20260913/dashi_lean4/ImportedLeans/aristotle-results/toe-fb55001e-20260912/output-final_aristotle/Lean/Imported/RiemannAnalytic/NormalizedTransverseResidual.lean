/-
# G19 — the normalized (Schur) quotient, the linear transverse residual, and the
phase audit of the literal prime transport

G18 (`LiteralSourceIdentity.lean`) proved that the literal Riemann–Weil
normalization supplies `N^{-1/2}` where the anchored second-moment gate needs
`N^{-1}`: the deficit is exactly one factor of the prime mass, because the
zero-side observable is *quadratic* in the prime data while the literal
explicit-formula transport is *linear* in it.

This module runs the three questions that decide the remaining Gram lane.

## 1.  A common positive normalization is invisible to a relative gate

`relativeGate_invariant_under_positive_normalization`: for `g > 0`,

```
P/g ≤ η·(D/g)   ↔   P ≤ η·D,        P/g < D/g   ↔   P < D,
(P/g)/(D/g) = P/D.
```

So replacing the raw anchored defect `D_raw = G₀₀ tr G − |G₀,*|²` by the
normalized transverse energy `D_tr = D_raw/G₀₀` while the prime side is obtained
by dividing the *same* transported bound by the *same* `G₀₀` changes nothing at
all: `literalNormalizedGateRatio_eq` and `literalNormalizedAnchorGateFails` carry
the G18 verdict verbatim to the normalized observable, with no asymptotics.
**That lane is closed exactly, not approximately.**

## 2.  The linear transverse amplitude does exist on the zero side

`transverseResidual_source_lowerBound`: the anchored defect is *identically*
`‖u‖²‖P_{u^⊥}v‖²` (`wedgeSq_eq_normSq_mul_transverseSq`, already in the
project), so the source floor `c L⁶α² ≤ D_raw` together with the anchor bound
`‖u‖² ≤ C_u L²` gives the **unsquared** bound

```
‖P_{u^⊥}v‖ ≥ √(c/C_u) · L² · |α|.
```

This is a linear off-line witness, matching the linear explicit-formula
transport in degree.

## 3.  The literal transport of the residual, and its coefficients

`literalTransverseResidualPrimeIdentity`: by linearity of the G18 identity in
the test function, the residual combination `v − β u` of two grid frequencies is
transported to the *linear* prime sum

```
P_N(φ,x_v) − β P_N(φ,x_u)
  = 2 ∑_{n ≤ N} Λ(n) n^{-1/2} φ(log n) (cos(x_v log n) − β cos(x_u log n)),
```

with no new explicit formula required.  `weilGridResidualPrimeSum_eq` is the
coefficient identity; the transport is exact.

## 4.  The phase audit — the literal interface is cosine-only

`weilPrimeTerm_gridTest_eq_cos_sub_sin` computes the literal Weil prime term of
the grid family `g_x(u) = φ(u)e^{-ixu}` for an arbitrary *real* taper supported
in `[-L,L]`:

```
P(g_x) = C_N(φ,x) − i·S_N(φ,x),
C_N(φ,x) = ∑ Λ(n)n^{-1/2}(φ(ℓ_n)+φ(−ℓ_n)) cos(x ℓ_n),
S_N(φ,x) = ∑ Λ(n)n^{-1/2}(φ(ℓ_n)−φ(−ℓ_n)) sin(x ℓ_n).
```

So the sine (phase) channel is carried **exactly by the odd part of the taper**
(`weilGridSinSum_eq_oddPart`), and for the real *even* taper the source-side
Gram floor demands it vanishes identically
(`weilGridSinSum_eq_zero_of_even`, `weilGridPrimeSum_neg`,
`weilGridPrimeSum_antisymmetric_part_eq_zero`).  The Weil symmetrization has
annihilated the transverse phase coordinate: an unsymmetrized/odd amplitude is
*not* available from the present interface without giving the taper an odd part.

## 5.  The decision

`linearTransverseGateDecision`: the linear lane is scored against the new floor
`c_r L²|α|`.  Whenever the residual coefficients
`c_n = cos(x_v ℓ_n) − β cos(x_u ℓ_n)` do **not** cancel — i.e. `c_n ≥ κ > 0` on
`n ≤ N`, which is exactly what happens at the degenerate anchor `x_u = x_v = 0`,
`β < 1` (`linearTransverseGate_fails_at_degenerate_anchor`) — the ratio

```
Ξ_lin = |P_N(φ,x_v) − β P_N(φ,x_u)| / (c_r L² |α|)   ≥   κ N^{1/4}/(1000 c_r)
```

diverges (`linearTransverseGateDecision_tendsto`).  Conversely, closing the gate
*forces* square-root cancellation in a literal von Mangoldt sum:
`linearTransverseGate_requires_sqrt_cancellation` shows the residual would have
to be smaller than its own trivial size by the factor `(log N)²/N^{1/2}`.
**Verdict: `Ξ_lin → ∞` for the uncancelled coefficients; the linear lane can
only be closed by an input of square-root-cancellation strength.**

Nothing here proves the Riemann Hypothesis, nothing here weakens
`RiemannHypothesisFor`, and no `sorry`, `axiom`, postulate, Boolean receipt or
numerical evidence appears.
-/
import RiemannAnalytic.LiteralSourceIdentity
import RiemannAnalytic.TransverseDerivative

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ## 1.  A common positive normalization is invisible to a relative gate -/

/-- **Relative gates are invariant under a common positive normalization.**
Dividing both the consumed quantity `P` and the geometric floor quantity `D` by
the same positive `g` changes neither the weak gate `P ≤ η D` nor the strict
gate `P < D`. -/
theorem relativeGate_invariant_under_positive_normalization {P D g η : ℝ} (hg : 0 < g) :
    (P / g ≤ η * (D / g) ↔ P ≤ η * D) ∧ (P / g < D / g ↔ P < D) := by
  constructor
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hg]
  · exact div_lt_div_iff_of_pos_right hg

/-- The contraction ratio itself is unchanged by a common positive
normalization: `(P/g)/(D/g) = P/D`. -/
theorem gateRatio_invariant_under_positive_normalization (P D : ℝ) {g : ℝ} (hg : 0 < g) :
    (P / g) / (D / g) = P / D := by
  rw [div_div_div_cancel_right₀]
  exact hg.ne'

/-- The G18 gate ratio, normalized by an arbitrary positive anchor energy `g`:
numerator and denominator of the contraction condition are both divided by `g`.
-/
noncomputable def literalNormalizedGateRatio (φ : ℝ → ℝ) (N : ℕ) (α t c g : ℝ) : ℝ :=
  (120000 * literalSourceCoefficient φ N α * t ^ 2 * (N : ℝ) ^ (1 + 4 * |α| : ℝ) / g)
    / (1024 * c * (Real.log N) ^ 4 / g)

/-- **The normalized-quotient lane is decided exactly.**  Normalizing the
anchored observable by the anchor energy `G₀₀ = g > 0` leaves the gate ratio
literally unchanged. -/
theorem literalNormalizedGateRatio_eq (φ : ℝ → ℝ) (N : ℕ) (α t c : ℝ) {g : ℝ} (hg : 0 < g) :
    literalNormalizedGateRatio φ N α t c g = literalGateRatio φ N α t c := by
  unfold literalNormalizedGateRatio literalGateRatio
  exact gateRatio_invariant_under_positive_normalization _ _ hg

/-- **The G18 divergence transports verbatim to the normalized observable.**
No asymptotics are involved: the ratio is the same number. -/
theorem literalNormalizedSourceRatioDecision {φ : ℝ → ℝ} {N : ℕ} {α t c g : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hc : 0 < c) (hg : 0 < g)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    t ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) / (10 ^ 10 * c) ≤ literalNormalizedGateRatio φ N α t c g := by
  rw [literalNormalizedGateRatio_eq _ _ _ _ _ hg]
  exact literalSourceRatioDecision hN hα hc hplat

/-- **The normalized anchored gate fails exactly as the raw one does.**  The
contraction condition of the anchored route, with *both* sides divided by the
anchor energy `g > 0` — i.e. the gate of the scalar Schur complement
`tr G − |G₀,*|²/G₀₀` — is false whenever the raw one is.  Pure normalization
cannot repair a failed relative gate. -/
theorem literalNormalizedAnchorGateFails {φ : ℝ → ℝ} {N : ℕ} {α t c g : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (hg : 0 < g)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hbig : c * (Real.log N) ^ 4 ≤ 7500 * t ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ)) :
    ¬ (120000 * (Real.log N) ^ 2
          * (literalSourceCoefficient φ N α * t ^ 2 * (weilMass N α) ^ 2) / g
        < c * (Real.log N) ^ 6 / g) := by
  intro hgate
  exact literalRawAnchorGateFails hN hα hplat hbig
    ((relativeGate_invariant_under_positive_normalization (η := 1) hg).2.1 hgate)

/-! ## 2.  The linear transverse amplitude on the zero side -/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The transverse residual carries the source floor, unsquared.**

The anchored defect is identically `‖x‖²‖P_{x^⊥}w‖²`, so a floor
`c L⁶ α² ≤ wedgeSq x w` together with the anchor energy bound `‖x‖² ≤ C_u L²`
gives a *linear* lower bound for the transverse residual itself:

```
√(c/C_u) · L² · |α|  ≤  ‖P_{x^⊥}w‖.
```

This is the off-line witness whose degree matches the linear explicit-formula
transport of the anchor. -/
theorem transverseResidual_source_lowerBound (x w : E) (hx : x ≠ 0)
    {c L alpha Cu : ℝ} (hc : 0 < c) (hCu : 0 < Cu)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ wedgeSq x w) (hanchor : ‖x‖ ^ 2 ≤ Cu * L ^ 2) :
    Real.sqrt (c / Cu) * L ^ 2 * |alpha| ≤ ‖transverseComp x w‖ := by
  have hid := wedgeSq_eq_normSq_mul_transverseSq x w hx
  have hr0 : (0 : ℝ) ≤ ‖transverseComp x w‖ := norm_nonneg _
  have hnn : (0 : ℝ) ≤ Real.sqrt (c / Cu) * L ^ 2 * |alpha| := by positivity
  have hsq : (Real.sqrt (c / Cu) * L ^ 2 * |alpha|) ^ 2 = c / Cu * (L ^ 2) ^ 2 * alpha ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
  rcases eq_or_ne L 0 with rfl | hL0
  · simp
  · have hL2 : (0 : ℝ) < L ^ 2 := by positivity
    have h1 : c * L ^ 6 * alpha ^ 2 ≤ ‖x‖ ^ 2 * ‖transverseComp x w‖ ^ 2 := by
      rw [← hid]; exact hfloor
    have h2 : ‖x‖ ^ 2 * ‖transverseComp x w‖ ^ 2
        ≤ Cu * L ^ 2 * ‖transverseComp x w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hanchor (sq_nonneg _)
    have hkey : c / Cu * (L ^ 2) ^ 2 * alpha ^ 2 ≤ ‖transverseComp x w‖ ^ 2 := by
      have hmul : (c / Cu * (L ^ 2) ^ 2 * alpha ^ 2) * (Cu * L ^ 2)
          ≤ ‖transverseComp x w‖ ^ 2 * (Cu * L ^ 2) := by
        have heq : (c / Cu * (L ^ 2) ^ 2 * alpha ^ 2) * (Cu * L ^ 2) = c * L ^ 6 * alpha ^ 2 := by
          field_simp
        rw [heq]
        nlinarith [h1, h2]
      exact le_of_mul_le_mul_right hmul (by positivity)
    refine (pow_le_pow_iff_left₀ hnn hr0 two_ne_zero).1 ?_
    rw [hsq]
    exact hkey

/-! ## 3.  The literal transport of the residual -/

/-- The literal residual prime sum: the prime side of the transported
combination `v − β u` of two grid frequencies,

```
2 ∑_{n ≤ N} Λ(n) n^{-1/2} φ(log n) (cos(x_v log n) − β cos(x_u log n)).
```
-/
noncomputable def weilGridResidualPrimeSum (φ : ℝ → ℝ) (N : ℕ) (β xu xv : ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * φ (Real.log n)
      * (Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n))

/-- The residual prime sum **is** the corresponding combination of literal Weil
prime terms: the transport is linear and exact. -/
theorem weilGridResidualPrimeSum_eq (φ : ℝ → ℝ) (N : ℕ) (β xu xv : ℝ) :
    weilGridResidualPrimeSum φ N β xu xv
      = weilGridPrimeSum φ N xv - β * weilGridPrimeSum φ N xu := by
  unfold weilGridResidualPrimeSum weilGridPrimeSum
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The literal transverse-residual prime identity.**

Applying the G18 compensated-anchor identity at the two grid frequencies `x_u`
and `x_v` and forming the Schur/regression residual combination with the
projection coefficient `β` gives, with no new explicit formula and no
majorization:

```
m_ρ (φ̂(z_ρ+x_v) − β φ̂(z_ρ+x_u))
  = −(P_N(φ,x_v) − β P_N(φ,x_u)) + (A_v − β A_u) − (R_v − β R_u),
```

whose prime side is the **linear** sum `weilGridResidualPrimeSum` with
coefficients `c_n = cos(x_v log n) − β cos(x_u log n)`.  The residual is
transported linearly in the prime data — one power of the prime mass, not two. -/
theorem literalTransverseResidualPrimeIdentity {φ : ℝ → ℝ} {L : ℝ} {N : ℕ} {xu xv : ℝ}
    (Z : ZeroData) (archu archv : ℂ) (j₀ : ℕ) (β : ℝ)
    (hev : ∀ u, φ (-u) = φ u) (hsupp : ∀ u, L < |u| → φ u = 0)
    (hN : Real.exp L < (N : ℝ) + 1)
    (hsummableu : Summable fun j : ℕ =>
      (Z.mult j : ℂ) * PhiExtC (gridTest φ xu) (zeroCoord (Z.zeros j)))
    (hsummablev : Summable fun j : ℕ =>
      (Z.mult j : ℂ) * PhiExtC (gridTest φ xv) (zeroCoord (Z.zeros j)))
    (hEFu : WeilExplicitFormula Z archu (gridTest φ xu))
    (hEFv : WeilExplicitFormula Z archv (gridTest φ xv)) :
    (Z.mult j₀ : ℂ) * (PhiExt φ (zeroCoord (Z.zeros j₀) + (xv : ℂ))
        - (β : ℂ) * PhiExt φ (zeroCoord (Z.zeros j₀) + (xu : ℂ)))
      = -((weilGridResidualPrimeSum φ N β xu xv : ℝ) : ℂ)
        + (archv - (β : ℂ) * archu)
        - (zeroRemainder Z φ xv j₀ - (β : ℂ) * zeroRemainder Z φ xu j₀) := by
  have hu := literalCompensatedAnchorExplicitFormula (φ := φ) (L := L) (N := N) (x := xu)
    Z archu j₀ hev hsupp hN hsummableu hEFu
  have hv := literalCompensatedAnchorExplicitFormula (φ := φ) (L := L) (N := N) (x := xv)
    Z archv j₀ hev hsupp hN hsummablev hEFv
  have hres : ((weilGridResidualPrimeSum φ N β xu xv : ℝ) : ℂ)
      = ((weilGridPrimeSum φ N xv : ℝ) : ℂ) - (β : ℂ) * ((weilGridPrimeSum φ N xu : ℝ) : ℂ) := by
    rw [weilGridResidualPrimeSum_eq]; push_cast; ring
  rw [hres]
  linear_combination hv - (β : ℂ) * hu

/-! ## 4.  The phase audit of the literal prime interface -/

/-- The cosine (even) channel of the literal prime transport of the grid family:
`C_N(φ,x) = ∑_{n ≤ N} Λ(n) n^{-1/2} (φ(ℓ_n) + φ(−ℓ_n)) cos(x ℓ_n)`. -/
noncomputable def weilGridCosSum (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
    * (φ (Real.log n) + φ (-Real.log n)) * Real.cos (x * Real.log n)

/-- The sine (odd, phase) channel of the literal prime transport of the grid
family: `S_N(φ,x) = ∑_{n ≤ N} Λ(n) n^{-1/2} (φ(ℓ_n) − φ(−ℓ_n)) sin(x ℓ_n)`. -/
noncomputable def weilGridSinSum (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
    * (φ (Real.log n) - φ (-Real.log n)) * Real.sin (x * Real.log n)

/-- **The literal prime transport of the grid family, for an arbitrary real
taper.**  For `φ` real and supported in `[-L,L]` and `e^L < N+1`,

```
P(g_x) = C_N(φ,x) − i·S_N(φ,x).
```

No evenness is assumed: this exhibits both channels of the literal interface.
-/
theorem weilPrimeTerm_gridTest_eq_cos_sub_sin {φ : ℝ → ℝ} {L : ℝ} {N : ℕ} (x : ℝ)
    (hsupp : ∀ u, L < |u| → φ u = 0) (hN : Real.exp L < (N : ℝ) + 1) :
    weilPrimeTerm (gridTest φ x)
      = ((weilGridCosSum φ N x : ℝ) : ℂ) - Complex.I * ((weilGridSinSum φ N x : ℝ) : ℂ) := by
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
      have h2 : φ (-Real.log n) = 0 := hsupp _ (by rw [abs_neg]; rwa [abs_of_nonneg hlognn])
      simp [gridTest, h1, h2]
  have hexp : ∀ θ : ℝ, Complex.exp (-(Complex.I * (x : ℂ) * (θ : ℂ)))
      = ((Real.cos (x * θ) : ℝ) : ℂ) - Complex.I * ((Real.sin (x * θ) : ℝ) : ℂ) := by
    intro θ
    have h : -(Complex.I * (x : ℂ) * (θ : ℂ)) = ((-(x * θ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [weilPrimeTerm, tsum_eq_sum hzero]
  unfold weilGridCosSum weilGridSinSum
  rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [gridTest]
  rw [hexp (Real.log n), hexp (-Real.log n),
    show x * -Real.log (n : ℕ) = -(x * Real.log (n : ℕ)) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The sine channel is carried **exactly by the odd part of the taper**. -/
theorem weilGridSinSum_eq_oddPart (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    weilGridSinSum φ N x
      = 2 * ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
          * ((φ (Real.log n) - φ (-Real.log n)) / 2) * Real.sin (x * Real.log n) := by
  unfold weilGridSinSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **For a real even taper the phase channel vanishes identically.**  The Weil
symmetrization annihilates the sine (transverse phase) coordinate of the grid
family. -/
theorem weilGridSinSum_eq_zero_of_even {φ : ℝ → ℝ} (hev : ∀ u, φ (-u) = φ u) (N : ℕ) (x : ℝ) :
    weilGridSinSum φ N x = 0 := by
  unfold weilGridSinSum
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [hev]
  ring

/-- For a real even taper the cosine channel is the G18 prime term. -/
theorem weilGridCosSum_of_even {φ : ℝ → ℝ} (hev : ∀ u, φ (-u) = φ u) (N : ℕ) (x : ℝ) :
    weilGridCosSum φ N x = weilGridPrimeSum φ N x := by
  unfold weilGridCosSum weilGridPrimeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hev]
  ring

/-- **The literal prime transport of an even taper is cosine-only**: an even
function of the grid frequency. -/
theorem weilGridPrimeSum_neg (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    weilGridPrimeSum φ N (-x) = weilGridPrimeSum φ N x := by
  unfold weilGridPrimeSum
  refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
  rw [show -x * Real.log n = -(x * Real.log n) by ring, Real.cos_neg]

/-- **The antisymmetric (odd) part of the literal prime transport vanishes
identically.**  So no linear/odd prime amplitude can be extracted from the
present interface with an even taper: the phase-sensitive coordinate has been
projected away by the Weil symmetrization, and recovering it requires giving the
taper an odd part (`weilGridSinSum_eq_oddPart`). -/
theorem weilGridPrimeSum_antisymmetric_part_eq_zero (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    weilGridPrimeSum φ N x - weilGridPrimeSum φ N (-x) = 0 := by
  rw [weilGridPrimeSum_neg]
  ring

/-- **The phase channel is capped by the same prime mass.**  Even when the taper
is given an odd part, the sine (phase) channel of the literal transport is
bounded by `B · ∑_{n≤N} Λ(n)n^{-1/2}`, `B` a bound for the odd part: the
unsymmetrized amplitude does not by itself supply a smaller scale than the
cosine channel.  Any gain must come from cancellation in the sum, not from the
channel. -/
theorem weilGridSinSum_abs_le {φ : ℝ → ℝ} {N : ℕ} {B : ℝ} (x : ℝ)
    (hB : ∀ u, |φ u - φ (-u)| ≤ B) :
    |weilGridSinSum φ N x| ≤ B * ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  unfold weilGridSinSum
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => ?_)
  have hw : (0 : ℝ) ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hs : |Real.sin (x * Real.log n)| ≤ 1 := Real.abs_sin_le_one _
  rw [abs_mul, abs_mul, abs_of_nonneg hw]
  calc Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * |φ (Real.log n) - φ (-Real.log n)|
        * |Real.sin (x * Real.log n)|
      ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * B * 1 := by
        have h1 : Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * |φ (Real.log n) - φ (-Real.log n)|
            ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * B :=
          mul_le_mul_of_nonneg_left (hB _) hw
        have h2 : (0 : ℝ) ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
            * |φ (Real.log n) - φ (-Real.log n)| := by positivity
        nlinarith [abs_nonneg (Real.sin (x * Real.log n)), hs, h1, h2, mul_nonneg hw hB0]
    _ = B * (Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)) := by ring

/-! ## 5.  The decision for the linear transverse lane -/

/-- `weilMass N 0` is the plain literal prime mass `∑_{n ≤ N} Λ(n) n^{-1/2}`. -/
theorem weilMass_zero_eq (N : ℕ) :
    weilMass N 0 = ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
  unfold weilMass weilWeight
  refine Finset.sum_congr rfl fun n _ => ?_
  norm_num

/-- **No cancellation ⟹ the residual carries the full prime mass.**  If the
residual coefficients `c_n = cos(x_v ℓ_n) − β cos(x_u ℓ_n)` stay above `κ > 0`
on the plateau, the transported residual is at least `κ N^{1/2}/16`. -/
theorem weilGridResidualPrimeSum_lowerBound {φ : ℝ → ℝ} {N : ℕ} {β xu xv κ : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hκ : 0 ≤ κ)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hcoef : ∀ n ∈ Icc 1 N,
      κ ≤ Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)) :
    κ * (N : ℝ) ^ (1 / 2 : ℝ) / 16 ≤ weilGridResidualPrimeSum φ N β xu xv := by
  have hmass := (weilMass_two_sided (α := 0) hN (by norm_num)).1
  rw [show (1 / 2 + 2 * |(0 : ℝ)| : ℝ) = 1 / 2 by norm_num] at hmass
  have hstep : κ * weilMass N 0
      ≤ ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * φ (Real.log n)
          * (Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)) := by
    rw [weilMass_zero_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hw : (0 : ℝ) ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) :=
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [hplat n hn, mul_one]
    calc κ * (Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ))
        = Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * κ := by ring
      _ ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
            * (Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)) :=
          mul_le_mul_of_nonneg_left (hcoef n hn) hw
  unfold weilGridResidualPrimeSum
  nlinarith [hstep, hmass, hκ]

/-- **The trivial transport bound.**  On the plateau the residual never exceeds
`2(1+|β|)` times the literal prime mass, i.e. `1618(1+|β|) N^{1/2}`.  This is the
*only* size the literal identity supplies without new cancellation input. -/
theorem weilGridResidualPrimeSum_trivial_upperBound {φ : ℝ → ℝ} {N : ℕ} {β xu xv : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    |weilGridResidualPrimeSum φ N β xu xv| ≤ 1618 * (1 + |β|) * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hmass := (weilMass_two_sided (α := 0) hN (by norm_num)).2
  rw [show (1 / 2 + 2 * |(0 : ℝ)| : ℝ) = 1 / 2 by norm_num] at hmass
  have hstep : |∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * φ (Real.log n)
      * (Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n))|
      ≤ (1 + |β|) * weilMass N 0 := by
    rw [weilMass_zero_eq, Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n hn => ?_)
    have hw : (0 : ℝ) ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) :=
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [hplat n hn, mul_one, abs_mul, abs_of_nonneg hw]
    have hc : |Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)| ≤ 1 + |β| := by
      have h1 : |Real.cos (xv * Real.log n)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : |β * Real.cos (xu * Real.log n)| ≤ |β| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg β) (Real.abs_cos_le_one _)
      calc |Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)|
          = |Real.cos (xv * Real.log n) + -(β * Real.cos (xu * Real.log n))| := by
            rw [sub_eq_add_neg]
        _ ≤ |Real.cos (xv * Real.log n)| + |-(β * Real.cos (xu * Real.log n))| := abs_add_le _ _
        _ ≤ 1 + |β| := by rw [abs_neg]; linarith
    calc Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
          * |Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)|
        ≤ Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * (1 + |β|) := mul_le_mul_of_nonneg_left hc hw
      _ = (1 + |β|) * (Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)) := by ring
  have hβ : (0 : ℝ) ≤ 1 + |β| := by positivity
  unfold weilGridResidualPrimeSum
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [hstep, hmass, hβ, abs_nonneg (∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ)
    * φ (Real.log n) * (Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)))]

/-- The gate ratio of the linear transverse lane: the transported linear prime
residual, measured against the transverse source floor `c_r L² |α|` of
`transverseResidual_source_lowerBound`.  The lane survives iff this is `< 1`. -/
noncomputable def linearTransverseGateRatio (φ : ℝ → ℝ) (N : ℕ) (β xu xv cr L alpha : ℝ) : ℝ :=
  |weilGridResidualPrimeSum φ N β xu xv| / (cr * L ^ 2 * |alpha|)

/-- **`linearTransverseGateDecision` — the verdict of the linear lane.**

For the plateau taper, a taper support `L ≤ log N` (which is exactly the literal
constraint `e^L < N+1` of the truncation), an off-line displacement
`0 < |α| ≤ 1/2`, and residual coefficients that do not cancel (`c_n ≥ κ > 0`),

```
Ξ_lin(N) ≥ κ N^{1/4} / (1000 c_r).
```

So the ratio diverges: the linear transverse lane is **red** for uncancelled
coefficients, by a full power `N^{1/4}` against the `L²|α|` floor. -/
theorem linearTransverseGateDecision {φ : ℝ → ℝ} {N : ℕ} {β xu xv κ cr L alpha : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hcr : 0 < cr) (hκ : 0 < κ)
    (hL : 0 < L) (hLN : L ≤ Real.log N) (halpha : alpha ≠ 0) (halpha2 : |alpha| ≤ 1 / 2)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hcoef : ∀ n ∈ Icc 1 N,
      κ ≤ Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)) :
    κ * (N : ℝ) ^ (1 / 4 : ℝ) / (1000 * cr)
      ≤ linearTransverseGateRatio φ N β xu xv cr L alpha := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  have hq : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hhalf : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hlog2 : (Real.log N) ^ 2 ≤ 64 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := log_pow_le_mul_rpow N (k := 2) (by norm_num) (δ := 1 / 4) (by norm_num)
    norm_num at h
    linarith
  have habs : 0 < |alpha| := abs_pos.2 halpha
  have hlow := weilGridResidualPrimeSum_lowerBound hN hκ.le hplat hcoef
  have hden : 0 < cr * L ^ 2 * |alpha| := by positivity
  have habsres : κ * (N : ℝ) ^ (1 / 2 : ℝ) / 16 ≤ |weilGridResidualPrimeSum φ N β xu xv| :=
    le_trans hlow (le_abs_self _)
  have hdenle : cr * L ^ 2 * |alpha| ≤ cr * (64 * (N : ℝ) ^ (1 / 4 : ℝ)) * (1 / 2) := by
    have hL2 : L ^ 2 ≤ (Real.log N) ^ 2 := by nlinarith [hL.le, hLN, hlogpos]
    have h1 : cr * L ^ 2 ≤ cr * (64 * (N : ℝ) ^ (1 / 4 : ℝ)) := by nlinarith [hcr.le, hL2, hlog2]
    have h2 : (0 : ℝ) ≤ cr * L ^ 2 := by positivity
    nlinarith [halpha2, habs.le, h1, h2, hcr.le, hq.le]
  unfold linearTransverseGateRatio
  rw [div_le_div_iff₀ (by positivity) hden]
  have hnn : (0 : ℝ) ≤ κ * (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have step1 : κ * (N : ℝ) ^ (1 / 4 : ℝ) * (cr * L ^ 2 * |alpha|)
      ≤ κ * (N : ℝ) ^ (1 / 4 : ℝ) * (cr * (64 * (N : ℝ) ^ (1 / 4 : ℝ)) * (1 / 2)) :=
    mul_le_mul_of_nonneg_left hdenle hnn
  have step2 : κ * (N : ℝ) ^ (1 / 4 : ℝ) * (cr * (64 * (N : ℝ) ^ (1 / 4 : ℝ)) * (1 / 2))
      ≤ κ * (N : ℝ) ^ (1 / 2 : ℝ) / 16 * (1000 * cr) := by
    rw [hhalf]
    nlinarith [hq, hcr, hκ.le, mul_pos hq hq]
  have step3 : κ * (N : ℝ) ^ (1 / 2 : ℝ) / 16 * (1000 * cr)
      ≤ |weilGridResidualPrimeSum φ N β xu xv| * (1000 * cr) :=
    mul_le_mul_of_nonneg_right habsres (by positivity)
  linarith

/-- **The degenerate anchor is already red.**  At `x_u = x_v = 0` with a
projection coefficient `β < 1` the residual coefficients are the constant
`1 − β > 0`, so the hypothesis of `linearTransverseGateDecision` holds with
`κ = 1 − β`: the linear lane fails there outright. -/
theorem linearTransverseGate_fails_at_degenerate_anchor {φ : ℝ → ℝ} {N : ℕ} {β cr L alpha : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hcr : 0 < cr) (hβ : β < 1)
    (hL : 0 < L) (hLN : L ≤ Real.log N) (halpha : alpha ≠ 0) (halpha2 : |alpha| ≤ 1 / 2)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    (1 - β) * (N : ℝ) ^ (1 / 4 : ℝ) / (1000 * cr)
      ≤ linearTransverseGateRatio φ N β 0 0 cr L alpha := by
  refine linearTransverseGateDecision hN hcr (by linarith) hL hLN halpha halpha2 hplat ?_
  intro n _
  simp

/-- **Closing the linear gate forces square-root cancellation.**  If the
transported residual were small enough to beat the transverse source floor, then
relative to its own trivial size `2 ∑_{n≤N} Λ(n)n^{-1/2}` it would have to be
smaller by the factor `(log N)²/N^{1/2}` — i.e. the literal von Mangoldt sum with
coefficients `c_n` would have to exhibit square-root cancellation.  That is an
input of the same strength as the conclusion, not a consequence of the
identity. -/
theorem linearTransverseGate_requires_sqrt_cancellation {φ : ℝ → ℝ} {N : ℕ} {β xu xv cr L alpha : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hcr : 0 < cr)
    (hL : 0 ≤ L) (hLN : L ≤ Real.log N) (halpha2 : |alpha| ≤ 1 / 2)
    (hgate : |weilGridResidualPrimeSum φ N β xu xv| ≤ cr * L ^ 2 * |alpha|) :
    |weilGridResidualPrimeSum φ N β xu xv|
      ≤ 32 * cr * (Real.log N) ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ) * weilMass N 0 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  have hq : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hmass := (weilMass_two_sided (α := 0) hN (by norm_num)).1
  rw [show (1 / 2 + 2 * |(0 : ℝ)| : ℝ) = 1 / 2 by norm_num] at hmass
  have hL2 : L ^ 2 ≤ (Real.log N) ^ 2 := by nlinarith [hL, hLN, hlogpos]
  have hstep1 : cr * L ^ 2 * |alpha| ≤ cr * L ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left halpha2 (by positivity)
  have hstep2 : cr * L ^ 2 * (1 / 2) ≤ cr * (Real.log N) ^ 2 / 2 := by
    nlinarith [hcr.le, hL2]
  have h2 : cr * (Real.log N) ^ 2 / 2
      ≤ 32 * cr * (Real.log N) ^ 2 / (N : ℝ) ^ (1 / 2 : ℝ) * weilMass N 0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    have hnn : (0 : ℝ) ≤ 32 * cr * (Real.log N) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmass hnn, hq, hcr, sq_nonneg (Real.log N)]
  linarith

/-- **The verdict in limit form.**  For every target `M` there is a threshold
beyond which the linear transverse gate ratio exceeds `M`, for every plateau
taper, every admissible support length, every off-line displacement
`0 < |α| ≤ 1/2` and all residual coefficients bounded below by `κ > 0`. -/
theorem linearTransverseGateDecision_tendsto {κ cr : ℝ} (hκ : 0 < κ) (hcr : 0 < cr) (M : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ φ : ℝ → ℝ, (∀ n ∈ Icc 1 N, φ (Real.log n) = 1) →
      ∀ β xu xv L alpha : ℝ, 0 < L → L ≤ Real.log N → alpha ≠ 0 → |alpha| ≤ 1 / 2 →
        (∀ n ∈ Icc 1 N,
          κ ≤ Real.cos (xv * Real.log n) - β * Real.cos (xu * Real.log n)) →
        M ≤ linearTransverseGateRatio φ N β xu xv cr L alpha := by
  set K : ℝ := max 0 (M * (1000 * cr) / κ) with hK
  have hK0 : 0 ≤ K := le_max_left _ _
  refine ⟨10 ^ 8 + ⌈K ^ 4⌉₊, fun N hN₀ φ hplat β xu xv L alpha hL hLN halpha halpha2 hcoef => ?_⟩
  have hNge : (10 : ℝ) ^ 8 + K ^ 4 ≤ (N : ℝ) := by
    have h1 : ((10 ^ 8 + ⌈K ^ 4⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀
    have h2 : K ^ 4 ≤ (⌈K ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    push_cast at h1
    linarith
  have hN : (10 : ℝ) ^ 8 ≤ (N : ℝ) := by nlinarith [pow_nonneg hK0 4]
  have hmain := linearTransverseGateDecision hN hcr hκ hL hLN halpha halpha2 hplat hcoef
  refine le_trans ?_ hmain
  rw [le_div_iff₀ (by positivity)]
  have hKle : K ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hle : K ^ 4 ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
    have h1 : (K ^ 4) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hle (by norm_num)
    have h2 : (K ^ 4) ^ (1 / 4 : ℝ) = K := by
      rw [← Real.rpow_natCast K 4, ← Real.rpow_mul hK0]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hMK : M * (1000 * cr) / κ ≤ K := le_max_right _ _
  rw [div_le_iff₀ hκ] at hMK
  nlinarith [hKle, hκ, hMK]

end RiemannAnalytic
