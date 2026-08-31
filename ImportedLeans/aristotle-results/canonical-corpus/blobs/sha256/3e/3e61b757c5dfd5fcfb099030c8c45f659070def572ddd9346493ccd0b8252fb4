/-
# Row A1 — the five quartic channel coefficients from literal source shapes

`FiveChannelQuartic` reduces the nonlinear beta remainder to five channelwise
majorants `|ch_k(g)| ≤ c_k g⁴`, and `QuarticChannelMajorant` produces such a
`c_k` from a uniform bound on the channel's fourth coupling derivative.  Both
still take the numbers `c_k` (or `M_k`) as *given*.  This file removes that
last abstraction for the two shapes the five source channels actually have.

Bałaban's fourth-order remainders come in exactly two literal forms.

* **Logarithmic (spectral) shape.**  The fluctuation determinant and the
  Faddeev–Popov / gauge determinant contribute `log det(1 + gK)`, i.e.
  `∑_i log(1 + g λ_i)` over the spectrum of the relevant operator.  Their
  *quartic remainder* is that sum minus its cubic Taylor polynomial.
* **Polynomial (tail) shape.**  The interaction, chart (Jacobian) and
  localization channels contribute a finite sum of monomials of degree ≥ 4 in
  the coupling, with source-given coefficients.
* **Analytic (power-series) shape.**  When such a channel is not a polynomial
  but is given by a convergent small-field expansion with a Cauchy bound on its
  Taylor coefficients — which is what small-field analyticity supplies — the
  same computation goes through with the geometric tail summed.

All three shapes are handled here with explicit, computed constants.

* `abs_logQuartic_le` : the elementary inequality
  `|log(1+u) − (u − u²/2 + u³/3)| ≤ u⁴ / (4(1−θ))` for `|u| ≤ θ < 1`.  It is
  proved from the exact derivative identity
  `d/du [log(1+u) − u + u²/2 − u³/3] = −u³/(1+u)` and a sign/monotonicity
  argument — no power series, no Taylor remainder machinery, no free constant.
* `abs_logDetChannel_le` : hence for a spectrum bounded by `Λ`,
  `|∑_i (log(1+gλ_i) − ...)| ≤ (n Λ⁴ / (4(1−θ))) g⁴` where `n` is the number of
  modes.  The determinant and gauge coefficients are therefore *computed* from
  `(n, Λ, θ)`.
* `abs_le_quartic_of_analyticChannel` : a third-order-vanishing channel with
  `|a_n| ≤ A Kⁿ` satisfies `|ch(g)| ≤ (A K⁴/(1−ρ)) g⁴` for `Kg ≤ ρ < 1`.
* `abs_tailPolyChannel_le` : a degree-≥4 polynomial channel with coefficients
  `a_n` satisfies `|ch(g)| ≤ (∑_n |a_n| θⁿ) g⁴` on `[0,θ]`.  The interaction,
  chart and localization coefficients are therefore *computed* from the source
  Taylor coefficients.
* `sourceChannelCoefficient`, `betaInt_ge_of_sourceChannels` : the assembled
  five-channel constant

      C_β = C_det + C_int + C_chart + C_gauge + C_loc

  in closed form, and the resulting literal debt `βInt(g) ≥ −C_β g⁴`.

**Honest status.**  What is *not* done here is the source identification: which
operator's spectrum is `λ`, the value of its bound `Λ`, the mode count `n`, and
the source Taylor coefficients `a_n` of the three polynomial channels.  Those
are inputs.  What is removed is any need for a channel constant that is not an
explicit function of such inputs: no channel constant is postulated, and no
channel constant is left as "some finite number".
-/
import RequestProject.YangMills.FiveChannelQuartic

namespace YangMills

open Set Finset

/-! ## 1. The elementary logarithmic quartic remainder -/

/-- The cubic-order remainder of the logarithm,
`log(1+u) − (u − u²/2 + u³/3)`. -/
noncomputable def logQuartic (u : ℝ) : ℝ :=
  Real.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3)

/-- **The exact derivative of the logarithmic remainder**: `−u³/(1+u)`.  The
cubic subtraction is precisely what cancels the `1/(1+u)` expansion through
second order, which is why the derivative carries the full factor `u³`. -/
theorem hasDerivAt_logQuartic {u : ℝ} (hu : 0 < 1 + u) :
    HasDerivAt logQuartic (-(u ^ 3 / (1 + u))) u := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + u)) u := by
    simpa using (((hasDerivAt_id u).const_add (1 : ℝ)).log (ne_of_gt hu))
  have h2 : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2 + x ^ 3 / 3) (1 - u + u ^ 2) u := by
    have h : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2 + x ^ 3 / 3)
        (1 - (2 * u ^ 1) / 2 + (3 * u ^ 2) / 3) u :=
      (((hasDerivAt_id u).sub ((hasDerivAt_pow 2 u).div_const 2)).add
        ((hasDerivAt_pow 3 u).div_const 3))
    convert h using 1
    ring
  have h := h1.sub h2
  convert h using 1
  field_simp
  ring

/-- A function vanishing at `0` whose derivative is nonnegative to the right of
`0` and nonpositive to its left is nonnegative on the whole interval. -/
private lemma nonneg_of_deriv_sign_at_zero {f : ℝ → ℝ} {theta : ℝ} (hth : 0 ≤ theta)
    (hc : ContinuousOn f (Icc (-theta) theta))
    (hd : ∀ x ∈ Ioo (-theta) theta, DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) theta, 0 ≤ deriv f x)
    (hneg : ∀ x ∈ Ioo (-theta) 0, deriv f x ≤ 0)
    (h0 : f 0 = 0) : ∀ x ∈ Icc (-theta) theta, 0 ≤ f x := by
  intro x hx
  rcases le_total 0 x with hx0 | hx0
  · have hsub : Icc (0 : ℝ) theta ⊆ Icc (-theta) theta :=
      Set.Icc_subset_Icc (by linarith) le_rfl
    have hmono : MonotoneOn f (Icc 0 theta) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hc.mono hsub) ?_ ?_ <;>
        intro y hy <;> rw [interior_Icc] at hy
      · exact (hd y ⟨by linarith [hy.1], hy.2⟩).differentiableWithinAt
      · exact hpos y hy
    have h := hmono ⟨le_rfl, hth⟩ ⟨hx0, hx.2⟩ hx0
    simpa [h0] using h
  · have hsub : Icc (-theta) (0 : ℝ) ⊆ Icc (-theta) theta :=
      Set.Icc_subset_Icc le_rfl (by linarith)
    have hanti : AntitoneOn f (Icc (-theta) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hc.mono hsub) ?_ ?_ <;>
        intro y hy <;> rw [interior_Icc] at hy
      · exact (hd y ⟨hy.1, by linarith [hy.2]⟩).differentiableWithinAt
      · exact hneg y hy
    have h := hanti ⟨hx.1, hx0⟩ ⟨by linarith, le_rfl⟩ hx0
    simpa [h0] using h

/-- **The logarithmic quartic remainder bound.**  For `|u| ≤ θ < 1`,

    |log(1+u) − (u − u²/2 + u³/3)| ≤ u⁴ / (4(1−θ)).

This is the literal fourth-order majorant of a single spectral mode of a
`log det` channel.  There is no free constant: `θ` is the small-field radius. -/
theorem abs_logQuartic_le {theta u : ℝ} (hth : theta < 1) (hu : |u| ≤ theta) :
    |logQuartic u| ≤ u ^ 4 / (4 * (1 - theta)) := by
  have hth0 : 0 ≤ theta := le_trans (abs_nonneg u) hu
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  have hmem : u ∈ Icc (-theta) theta := abs_le.mp hu
  have hone : ∀ x ∈ Icc (-theta) theta, 0 < 1 + x := by
    intro x hx; have := hx.1; linarith
  set c : ℝ := 1 / (4 * (1 - theta)) with hc
  have hcval : ∀ x : ℝ, c * (4 * x ^ 3) = x ^ 3 / (1 - theta) := by
    intro x; rw [hc]; field_simp
  have key : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ x ∈ Icc (-theta) theta, 0 ≤ c * x ^ 4 + s * logQuartic x := by
    intro s hs
    refine nonneg_of_deriv_sign_at_zero hth0 ?_ ?_ ?_ ?_ ?_
    · refine ContinuousOn.add (by fun_prop) ?_
      exact ContinuousOn.mul continuousOn_const fun x hx =>
        ((hasDerivAt_logQuartic (hone x hx)).continuousAt).continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc (-theta) theta := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      exact (((hasDerivAt_pow 4 x).const_mul c).add
        ((hasDerivAt_logQuartic (hone x hx')).const_mul s)).differentiableAt
    · intro x hx
      have hx' : x ∈ Icc (-theta) theta := ⟨by linarith [hx.1], le_of_lt hx.2⟩
      have hD := ((hasDerivAt_pow 4 x).const_mul c).add
        ((hasDerivAt_logQuartic (hone x hx')).const_mul s)
      have hdv : deriv (fun y : ℝ => c * y ^ 4 + s * logQuartic y) x
          = c * (4 * x ^ 3) + s * -(x ^ 3 / (1 + x)) := by simpa using hD.deriv
      rw [hdv, hcval]
      have h1x : 0 < 1 + x := hone x hx'
      have hx3 : 0 ≤ x ^ 3 := pow_nonneg (le_of_lt hx.1) 3
      have hlt : x ^ 3 / (1 + x) ≤ x ^ 3 / (1 - theta) :=
        div_le_div_of_nonneg_left hx3 hpos (by linarith [hx'.1])
      have hge : 0 ≤ x ^ 3 / (1 + x) := div_nonneg hx3 (le_of_lt h1x)
      rcases hs with rfl | rfl <;> nlinarith
    · intro x hx
      have hx' : x ∈ Icc (-theta) theta := ⟨le_of_lt hx.1, by linarith [hx.2]⟩
      have hD := ((hasDerivAt_pow 4 x).const_mul c).add
        ((hasDerivAt_logQuartic (hone x hx')).const_mul s)
      have hdv : deriv (fun y : ℝ => c * y ^ 4 + s * logQuartic y) x
          = c * (4 * x ^ 3) + s * -(x ^ 3 / (1 + x)) := by simpa using hD.deriv
      rw [hdv, hcval]
      have h1x : 0 < 1 + x := hone x hx'
      have hx3 : x ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) (le_of_lt hx.2)
      have hneg3 : 0 ≤ -x ^ 3 := by linarith
      have hstep : (-x ^ 3) / (1 + x) ≤ (-x ^ 3) / (1 - theta) :=
        div_le_div_of_nonneg_left hneg3 hpos (by linarith [hx'.1])
      have hlt : x ^ 3 / (1 - theta) ≤ x ^ 3 / (1 + x) := by
        rw [neg_div, neg_div, neg_le_neg_iff] at hstep; exact hstep
      have hle0 : x ^ 3 / (1 + x) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx3 (le_of_lt h1x)
      rcases hs with rfl | rfl <;> nlinarith
    · simp [logQuartic]
  have k1 := key 1 (Or.inl rfl) u hmem
  have k2 := key (-1) (Or.inr rfl) u hmem
  have hcu : c * u ^ 4 = u ^ 4 / (4 * (1 - theta)) := by rw [hc]; ring
  rw [abs_le]
  constructor <;> nlinarith [k1, k2, hcu]

/-! ## 2. The spectral (log-determinant) channels -/

/-- The quartic remainder of a `log det(1 + gK)` channel with spectrum `λ`:
`∑_i (log(1 + gλ_i) − (gλ_i − (gλ_i)²/2 + (gλ_i)³/3))`.  The subtracted cubic
polynomial is exactly the part of the determinant already accounted for by the
Gaussian term and the running coupling. -/
noncomputable def logDetChannel {ι : Type*} [Fintype ι] (lam : ι → ℝ) (g : ℝ) : ℝ :=
  ∑ i, logQuartic (g * lam i)

/-- **The determinant/gauge channel coefficient, computed.**  A spectrum bounded
by `Λ` on `n = card ι` modes, in the small-field regime `gΛ ≤ θ < 1`, gives

    |logDetChannel λ g| ≤ (n Λ⁴ / (4(1−θ))) · g⁴.

Every ingredient of the coefficient is source data: the mode count, the spectral
bound and the small-field radius. -/
theorem abs_logDetChannel_le {ι : Type*} [Fintype ι] {lam : ι → ℝ} {Lam theta g : ℝ}
    (hL : ∀ i, |lam i| ≤ Lam) (hg0 : 0 ≤ g) (hgL : g * Lam ≤ theta) (hth : theta < 1) :
    |logDetChannel lam g| ≤ (Fintype.card ι * Lam ^ 4 / (4 * (1 - theta))) * g ^ 4 := by
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  have hterm : ∀ i : ι, |logQuartic (g * lam i)| ≤ Lam ^ 4 / (4 * (1 - theta)) * g ^ 4 := by
    intro i
    have hLnn : 0 ≤ Lam := le_trans (abs_nonneg _) (hL i)
    have habs : |g * lam i| ≤ theta := by
      rw [abs_mul, abs_of_nonneg hg0]
      exact le_trans (by nlinarith [hL i, abs_nonneg (lam i)]) hgL
    have hbound := abs_logQuartic_le (theta := theta) (u := g * lam i) hth habs
    refine le_trans hbound ?_
    have hpow : (g * lam i) ^ 4 ≤ Lam ^ 4 * g ^ 4 := by
      have h1 : |lam i| ^ 4 ≤ Lam ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (hL i) 4
      have h2 : (lam i) ^ 4 = |lam i| ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hg4 : (0 : ℝ) ≤ g ^ 4 := by positivity
      calc (g * lam i) ^ 4 = (lam i) ^ 4 * g ^ 4 := by ring
        _ ≤ Lam ^ 4 * g ^ 4 := by rw [h2]; exact mul_le_mul_of_nonneg_right h1 hg4
    have hD : (0 : ℝ) < 4 * (1 - theta) := by linarith
    calc (g * lam i) ^ 4 / (4 * (1 - theta))
        ≤ (Lam ^ 4 * g ^ 4) / (4 * (1 - theta)) := by gcongr
      _ = Lam ^ 4 / (4 * (1 - theta)) * g ^ 4 := by ring
  calc |logDetChannel lam g| ≤ ∑ _i : ι, Lam ^ 4 / (4 * (1 - theta)) * g ^ 4 :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => hterm i)
    _ = (Fintype.card ι * Lam ^ 4 / (4 * (1 - theta))) * g ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## 3. The polynomial (tail) channels -/

/-- A channel given by a finite sum of monomials of degree at least four:
`∑_{n<N} a_n g^{n+4}`.  This is the shape of the interaction, chart and
localization remainders once the lower orders have been absorbed. -/
noncomputable def tailPolyChannel (a : ℕ → ℝ) (N : ℕ) (g : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, a n * g ^ (n + 4)

/-- **The polynomial channel coefficient, computed.**  On `0 ≤ g ≤ θ`,

    |tailPolyChannel a N g| ≤ (∑_{n<N} |a_n| θⁿ) · g⁴. -/
theorem abs_tailPolyChannel_le {a : ℕ → ℝ} {N : ℕ} {theta g : ℝ}
    (hg0 : 0 ≤ g) (hg : g ≤ theta) :
    |tailPolyChannel a N g| ≤ (∑ n ∈ Finset.range N, |a n| * theta ^ n) * g ^ 4 := by
  have hterm : ∀ n ∈ Finset.range N, |a n * g ^ (n + 4)| ≤ (|a n| * theta ^ n) * g ^ 4 := by
    intro n _
    have hpow : g ^ n ≤ theta ^ n := pow_le_pow_left₀ hg0 hg n
    have hg4 : (0 : ℝ) ≤ g ^ 4 := by positivity
    have h : |a n * g ^ (n + 4)| = |a n| * g ^ n * g ^ 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ g ^ (n + 4)), pow_add]
      ring
    rw [h]
    have : |a n| * g ^ n ≤ |a n| * theta ^ n :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right this hg4
  calc |tailPolyChannel a N g| ≤ ∑ n ∈ Finset.range N, |a n * g ^ (n + 4)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, (|a n| * theta ^ n) * g ^ 4 := Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.range N, |a n| * theta ^ n) * g ^ 4 := by rw [Finset.sum_mul]

/-- The same bound with the source coefficients replaced by uniform majorants —
the form needed when the coefficients depend on the scale and on the preceding
coupling history but are uniformly dominated. -/
theorem abs_tailPolyChannel_le_of_majorant {a A : ℕ → ℝ} {N : ℕ} {theta g : ℝ}
    (hA : ∀ n, |a n| ≤ A n) (hg0 : 0 ≤ g) (hg : g ≤ theta) :
    |tailPolyChannel a N g| ≤ (∑ n ∈ Finset.range N, |A n| * theta ^ n) * g ^ 4 := by
  have hth0 : 0 ≤ theta := le_trans hg0 hg
  have hg4 : (0 : ℝ) ≤ g ^ 4 := by positivity
  refine le_trans (abs_tailPolyChannel_le hg0 hg) ?_
  refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum ?_) hg4
  intro n _
  exact mul_le_mul_of_nonneg_right (le_trans (hA n) (le_abs_self _)) (pow_nonneg hth0 n)

/-! ## 3b. The analytic (power-series) channels -/

/-- **The analytic channel coefficient, computed.**  A channel given on the
small-field domain by a convergent power series whose coefficients obey a Cauchy
bound `|a_n| ≤ A Kⁿ`, and which vanishes to third order, satisfies

    |F| ≤ (A K⁴ / (1 − ρ)) g⁴      whenever `K g ≤ ρ < 1`.

This is the shape the source actually guarantees for the chart and localization
channels: small-field analyticity gives a Cauchy bound on the Taylor
coefficients, not a polynomial.  The resulting coefficient is again explicit in
source data `(A, K, ρ)` — nothing is postulated. -/
theorem abs_le_quartic_of_analyticChannel {a : ℕ → ℝ} {F A K rho g : ℝ}
    (hsum : HasSum (fun n => a n * g ^ n) F)
    (hA : ∀ n, |a n| ≤ A * K ^ n)
    (hlow : ∀ n, n < 4 → a n = 0)
    (hg0 : 0 ≤ g) (hK0 : 0 ≤ K) (hKg : K * g ≤ rho) (hrho : rho < 1) :
    |F| ≤ (A * K ^ 4 / (1 - rho)) * g ^ 4 := by
  have hA0 : 0 ≤ A := by have := hA 0; simp at this; linarith [abs_nonneg (a 0)]
  set t := K * g with ht
  have ht0 : 0 ≤ t := mul_nonneg hK0 hg0
  have ht1 : t < 1 := lt_of_le_of_lt hKg hrho
  have hgeo : HasSum (fun n : ℕ => A * t ^ n) (A * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0 ht1).mul_left A
  have hfin : HasSum (fun n : ℕ => if n < 4 then A * t ^ n else 0)
      (∑ n ∈ Finset.range 4, if n < 4 then A * t ^ n else 0) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro n hn
    simp at hn
    simp [Nat.not_lt.mpr (by omega : 4 ≤ n)]
  have hbd : HasSum (fun n : ℕ => A * t ^ n - (if n < 4 then A * t ^ n else 0))
      (A * (1 - t)⁻¹ - ∑ n ∈ Finset.range 4, if n < 4 then A * t ^ n else 0) := hgeo.sub hfin
  have hval : A * (1 - t)⁻¹ - (∑ n ∈ Finset.range 4, if n < 4 then A * t ^ n else 0)
      = A * t ^ 4 / (1 - t) := by
    have h1 : (1 : ℝ) - t ≠ 0 := by intro h; linarith [h]
    simp [Finset.sum_range_succ]
    field_simp
    ring
  rw [hval] at hbd
  have hterm : ∀ n : ℕ, |a n * g ^ n| ≤ A * t ^ n - (if n < 4 then A * t ^ n else 0) := by
    intro n
    by_cases h4 : n < 4
    · simp [h4, hlow n h4]
    · simp only [h4, if_false, sub_zero]
      rw [abs_mul, abs_of_nonneg (pow_nonneg hg0 n), ht, mul_pow]
      calc |a n| * g ^ n ≤ A * K ^ n * g ^ n :=
            mul_le_mul_of_nonneg_right (hA n) (pow_nonneg hg0 n)
        _ = A * (K ^ n * g ^ n) := by ring
  have hle : F ≤ A * t ^ 4 / (1 - t) :=
    hasSum_le (fun n => le_trans (le_abs_self _) (hterm n)) hsum hbd
  have hge : -(A * t ^ 4 / (1 - t)) ≤ F := by
    have := hasSum_le (fun n => neg_le_of_abs_le (hterm n)) hbd.neg hsum
    simpa using this
  have hfinal : A * t ^ 4 / (1 - t) ≤ (A * K ^ 4 / (1 - rho)) * g ^ 4 := by
    have h1 : (0 : ℝ) < 1 - t := by linarith
    have h2 : (0 : ℝ) < 1 - rho := by linarith
    have hnum : A * t ^ 4 = (A * K ^ 4) * g ^ 4 := by rw [ht]; ring
    rw [hnum, div_le_iff₀ h1]
    have hstep : A * K ^ 4 / (1 - rho) * g ^ 4 * (1 - rho)
        ≤ A * K ^ 4 / (1 - rho) * g ^ 4 * (1 - t) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc A * K ^ 4 * g ^ 4 = A * K ^ 4 / (1 - rho) * g ^ 4 * (1 - rho) := by field_simp
      _ ≤ A * K ^ 4 / (1 - rho) * g ^ 4 * (1 - t) := hstep
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## 4. The assembled five-channel constant -/

/-- The five channel coefficients in closed form: two spectral coefficients from
`(mode count, spectral bound, small-field radius)` and three polynomial
coefficients from the source Taylor coefficients. -/
noncomputable def sourceChannelCoefficient (cardDet cardGauge : ℕ)
    (LamDet LamGauge theta : ℝ) (aInt aChart aLoc : ℕ → ℝ) (N : ℕ) : BetaChannel → ℝ
  | BetaChannel.determinant => cardDet * LamDet ^ 4 / (4 * (1 - theta))
  | BetaChannel.gauge => cardGauge * LamGauge ^ 4 / (4 * (1 - theta))
  | BetaChannel.interaction => ∑ n ∈ Finset.range N, |aInt n| * theta ^ n
  | BetaChannel.chart => ∑ n ∈ Finset.range N, |aChart n| * theta ^ n
  | BetaChannel.localization => ∑ n ∈ Finset.range N, |aLoc n| * theta ^ n

theorem sourceChannelCoefficient_nonneg {cardDet cardGauge : ℕ}
    {LamDet LamGauge theta : ℝ} {aInt aChart aLoc : ℕ → ℝ} {N : ℕ}
    (hth : theta < 1) (hth0 : 0 ≤ theta) (k : BetaChannel) :
    0 ≤ sourceChannelCoefficient cardDet cardGauge LamDet LamGauge theta aInt aChart aLoc N k := by
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  have hsum : ∀ a : ℕ → ℝ, (0 : ℝ) ≤ ∑ n ∈ Finset.range N, |a n| * theta ^ n :=
    fun a => Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hth0 n)
  cases k
  · simp only [sourceChannelCoefficient]; positivity
  · simpa only [sourceChannelCoefficient] using hsum aInt
  · simpa only [sourceChannelCoefficient] using hsum aChart
  · simp only [sourceChannelCoefficient]; positivity
  · simpa only [sourceChannelCoefficient] using hsum aLoc

/-- **The literal five-channel debt.**  If the two determinant-type channels
have the spectral shape and the three remaining channels have the polynomial
shape, then

    βInt(g) ≥ −C_β g⁴,   C_β = C_det + C_int + C_chart + C_gauge + C_loc,

with all five coefficients given in closed form by `sourceChannelCoefficient`.
No coefficient is assumed: each is an explicit function of source data. -/
theorem betaInt_ge_of_sourceChannels
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {betaInt : ℝ → ℝ} {ch : BetaChannel → ℝ → ℝ}
    {lamDet : ι → ℝ} {lamGauge : κ → ℝ}
    {aInt aChart aLoc : ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta g : ℝ}
    (hsum : betaInt g = ∑ k, ch k g)
    (hdet : ch BetaChannel.determinant g = logDetChannel lamDet g)
    (hgauge : ch BetaChannel.gauge g = logDetChannel lamGauge g)
    (hint : ch BetaChannel.interaction g = tailPolyChannel aInt N g)
    (hchart : ch BetaChannel.chart g = tailPolyChannel aChart N g)
    (hloc : ch BetaChannel.localization g = tailPolyChannel aLoc N g)
    (hLd : ∀ i, |lamDet i| ≤ LamDet) (hLg : ∀ i, |lamGauge i| ≤ LamGauge)
    (hg0 : 0 ≤ g) (hgth : g ≤ theta) (hth : theta < 1)
    (hgLd : g * LamDet ≤ theta) (hgLg : g * LamGauge ≤ theta) :
    -(Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta aInt aChart aLoc N)) * g ^ 4 ≤ betaInt g := by
  refine betaInt_ge_of_channelMajorants hsum ?_
  intro k
  cases k
  · rw [hdet]; exact abs_logDetChannel_le hLd hg0 hgLd hth
  · rw [hint]; exact abs_tailPolyChannel_le hg0 hgth
  · rw [hchart]; exact abs_tailPolyChannel_le hg0 hgth
  · rw [hgauge]; exact abs_logDetChannel_le hLg hg0 hgLg hth
  · rw [hloc]; exact abs_tailPolyChannel_le hg0 hgth

/-- The assembled constant written out: the five-term sum the source has to
supply. -/
theorem Cbeta_sourceChannelCoefficient (cardDet cardGauge : ℕ)
    (LamDet LamGauge theta : ℝ) (aInt aChart aLoc : ℕ → ℝ) (N : ℕ) :
    Cbeta (sourceChannelCoefficient cardDet cardGauge LamDet LamGauge theta
        aInt aChart aLoc N)
      = cardDet * LamDet ^ 4 / (4 * (1 - theta))
        + (∑ n ∈ Finset.range N, |aInt n| * theta ^ n)
        + (∑ n ∈ Finset.range N, |aChart n| * theta ^ n)
        + cardGauge * LamGauge ^ 4 / (4 * (1 - theta))
        + (∑ n ∈ Finset.range N, |aLoc n| * theta ^ n) := by
  rw [Cbeta, show (Finset.univ : Finset BetaChannel)
      = {BetaChannel.determinant, .interaction, .chart, .gauge, .localization} from rfl]
  simp [sourceChannelCoefficient]
  ring

end YangMills
