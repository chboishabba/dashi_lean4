/-
# Row A — the **differentiated** literal channel majorants

`QuarticChannelSources` bounds the *value* of every literal remainder channel by
`C·g⁴`.  Closing Row A needs the *sensitivity* of the same channels, i.e. a
Lipschitz constant in the coupling, and the whole point is that it must be
extracted from the same source norms — the spectral bound `Λ` and the Cauchy
pair `(A, K)` — rather than from a fresh, unsourced constant.

This file differentiates the source majorants.  The gain is one power of the
coupling less than the value bound, i.e. a **cubic** suppression:

* `abs_logQuartic_sub_le` — the log-determinant remainder `log(1+u) −
  (u − u²/2 + u³/3)` has exact derivative `−u³/(1+u)`, hence is Lipschitz with
  constant `t³/(1−θ)` on `|u| ≤ t ≤ θ < 1`;
* `abs_logDetChannel_sub_le` — hence a spectral channel with `n` modes and
  spectrum `|λ| ≤ Λ`, in the small-field regime `GΛ ≤ θ`, obeys
  `|logDetChannel λ g − logDetChannel λ h| ≤ (nΛ⁴/(1−θ))·G³·|g − h|`;
* `sum_add_four_mul_geom_le` — the closed form of the differentiated geometric
  family, `Σ_{m≥0}(m+4)xᵐ = (4−3x)/(1−x)²`;
* `abs_tailPolyChannel_sub_le` — hence a polynomial channel `Σ_{n} a_n g^{n+4}`
  with Cauchy coefficients `|a_n| ≤ A·K^{n+4}` obeys
  `|R(g) − R(h)| ≤ A·K⁴·((4−3ρ)/(1−ρ)²)·G³·|g − h|` for `KG ≤ ρ < 1`;
* `abs_frozenShellInteraction_sub_le` — the five literal channels assembled:
  the whole interaction sector is Lipschitz in the coupling with constant
  `analyticDirectSensitivityBound · G³`, the differentiated analogue of
  `analyticCbetaBound`, built from exactly the same source data.

Nothing here is assumed: each constant is the derivative of the corresponding
majorant already in the repository, and no new source datum is introduced.
-/
import RequestProject.YangMills.A1SourceObjects

namespace YangMills

open Finset

/-! ## 1. The differentiated geometric family -/

/-- **The closed form of the differentiated geometric family.**
`Σ_{m<M}(m+4)xᵐ ≤ (4−3x)/(1−x)²`, the sum that appears when a Cauchy family
`|a_n| ≤ A·Kⁿ` is differentiated term by term. -/
theorem sum_add_four_mul_geom_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (M : ℕ) :
    ∑ m ∈ range M, ((m : ℝ) + 4) * x ^ m ≤ (4 - 3 * x) / (1 - x) ^ 2 := by
  have hx : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * x ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hx
  have hs2 : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one h0 h1
  have hsplit : (fun n : ℕ => ((n : ℝ) + 4) * x ^ n)
      = fun n : ℕ => (n : ℝ) * x ^ n + 4 * x ^ n := by
    funext n; ring
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 4) * x ^ n) := by
    rw [hsplit]; exact hs1.add (hs2.mul_left 4)
  have hpart := hs.sum_le_tsum (range M) (fun n _ => by positivity)
  have hval : ∑' n : ℕ, ((n : ℝ) + 4) * x ^ n = (4 - 3 * x) / (1 - x) ^ 2 := by
    rw [hsplit, hs1.tsum_add (hs2.mul_left 4), tsum_coe_mul_geometric_of_norm_lt_one hx,
      tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have hne : (1 : ℝ) - x ≠ 0 := by intro h; rw [sub_eq_zero] at h; exact absurd h.symm (ne_of_lt h1)
    field_simp
    ring
  rw [hval] at hpart
  exact hpart

/-! ## 2. Powers -/

/-- On `[0, G]` the monomial `x ↦ x^{m+1}` is Lipschitz with constant
`(m+1)·G^m`. -/
theorem abs_pow_succ_sub_le {g h G : ℝ} (hg0 : 0 ≤ g) (hh0 : 0 ≤ h)
    (hgG : g ≤ G) (hhG : h ≤ G) (m : ℕ) :
    |g ^ (m + 1) - h ^ (m + 1)| ≤ ((m : ℝ) + 1) * G ^ m * |g - h| := by
  have hG0 : 0 ≤ G := le_trans hg0 hgG
  induction m with
  | zero => simp
  | succ n ih =>
      have key : g ^ (n + 2) - h ^ (n + 2)
          = g * (g ^ (n + 1) - h ^ (n + 1)) + h ^ (n + 1) * (g - h) := by ring
      have h1 : |g * (g ^ (n + 1) - h ^ (n + 1))| ≤ G * (((n : ℝ) + 1) * G ^ n * |g - h|) := by
        rw [abs_mul, abs_of_nonneg hg0]
        refine mul_le_mul hgG ih (abs_nonneg _) hG0
      have h2 : |h ^ (n + 1) * (g - h)| ≤ G ^ (n + 1) * |g - h| := by
        rw [abs_mul, abs_pow, abs_of_nonneg hh0]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh0 hhG (n + 1)) (abs_nonneg _)
      have hsum : |g ^ (n + 2) - h ^ (n + 2)|
          ≤ G * (((n : ℝ) + 1) * G ^ n * |g - h|) + G ^ (n + 1) * |g - h| := by
        rw [key]
        exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
      have hid : G * (((n : ℝ) + 1) * G ^ n * |g - h|) + G ^ (n + 1) * |g - h|
          = (((n : ℝ) + 1) + 1) * G ^ (n + 1) * |g - h| := by
        rw [pow_succ]; ring
      calc |g ^ (n + 2) - h ^ (n + 2)|
          ≤ G * (((n : ℝ) + 1) * G ^ n * |g - h|) + G ^ (n + 1) * |g - h| := hsum
        _ = (((n : ℝ) + 1) + 1) * G ^ (n + 1) * |g - h| := hid
        _ = ((↑(n + 1) : ℝ) + 1) * G ^ (n + 1) * |g - h| := by push_cast; ring

/-! ## 3. The spectral channel, differentiated -/

/-- **The differentiated log-determinant remainder.**  `logQuartic` has exact
derivative `−u³/(1+u)`; on `|u| ≤ t ≤ θ < 1` this is bounded by `t³/(1−θ)`, so
`logQuartic` is Lipschitz there with that constant — one power of the field
*less* suppressed than its value bound `t⁴/(4(1−θ))`, and no more. -/
theorem abs_logQuartic_sub_le {theta t u v : ℝ} (hth : theta < 1) (ht0 : 0 ≤ t)
    (htth : t ≤ theta) (hu : |u| ≤ t) (hv : |v| ≤ t) :
    |logQuartic u - logQuartic v| ≤ (t ^ 3 / (1 - theta)) * |u - v| := by
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  set s : Set ℝ := Set.Icc (-t) t with hs
  have hconv : Convex ℝ s := convex_Icc _ _
  have hone : ∀ x ∈ s, 0 < 1 + x := by
    intro x hx
    have := hx.1
    have : -t ≤ x := hx.1
    have ht : t ≤ theta := htth
    linarith [hx.1, hth, htth]
  have hderiv : ∀ x ∈ s, HasDerivWithinAt logQuartic (-(x ^ 3 / (1 + x))) s x :=
    fun x hx => (hasDerivAt_logQuartic (hone x hx)).hasDerivWithinAt
  have hbound : ∀ x ∈ s, ‖-(x ^ 3 / (1 + x))‖ ≤ t ^ 3 / (1 - theta) := by
    intro x hx
    have hx1 : -t ≤ x := hx.1
    have hx2 : x ≤ t := hx.2
    have h1x : 0 < 1 + x := hone x hx
    have h1x' : 1 - theta ≤ 1 + x := by linarith
    have habs : |x| ≤ t := abs_le.mpr ⟨hx1, hx2⟩
    have hnum : |x ^ 3| ≤ t ^ 3 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 3
    rw [norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos h1x]
    calc |x ^ 3| / (1 + x) ≤ t ^ 3 / (1 + x) := by gcongr
      _ ≤ t ^ 3 / (1 - theta) := by
          refine div_le_div_of_nonneg_left (by positivity) hpos h1x'
  have hus : u ∈ s := abs_le.mp hu
  have hvs : v ∈ s := abs_le.mp hv
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hvs hus
  simpa [Real.norm_eq_abs] using this

/-- **The spectral channel is Lipschitz with a cubically suppressed constant.**
The mode count, the spectral bound and the small-field radius are the same
source data that produce the value bound `abs_logDetChannel_le`; differentiating
turns `nΛ⁴/(4(1−θ))·g⁴` into `nΛ⁴/(1−θ)·G³·|g−h|`. -/
theorem abs_logDetChannel_sub_le {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    {Lam theta G g h : ℝ} (hL : ∀ i, |lam i| ≤ Lam) (hLam0 : 0 ≤ Lam)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hgG : g ≤ G) (hhG : h ≤ G)
    (hGL : G * Lam ≤ theta) (hth : theta < 1) :
    |logDetChannel lam g - logDetChannel lam h|
      ≤ (Fintype.card ι * Lam ^ 4 / (1 - theta)) * G ^ 3 * |g - h| := by
  classical
  have hG0 : 0 ≤ G := le_trans hg0 hgG
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  have hterm : ∀ i : ι, |logQuartic (g * lam i) - logQuartic (h * lam i)|
      ≤ (Lam ^ 4 / (1 - theta)) * G ^ 3 * |g - h| := by
    intro i
    have hLi : |lam i| ≤ Lam := hL i
    have habs1 : |g * lam i| ≤ G * Lam := by
      rw [abs_mul, abs_of_nonneg hg0]
      exact mul_le_mul hgG hLi (abs_nonneg _) hG0
    have habs2 : |h * lam i| ≤ G * Lam := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hhG hLi (abs_nonneg _) hG0
    have hkey := abs_logQuartic_sub_le (theta := theta) (t := G * Lam)
      hth (by positivity) hGL habs1 habs2
    have hdiff : |g * lam i - h * lam i| = |lam i| * |g - h| := by
      rw [show g * lam i - h * lam i = (g - h) * lam i by ring, abs_mul, mul_comm]
    rw [hdiff] at hkey
    refine le_trans hkey ?_
    have h1 : ((G * Lam) ^ 3 / (1 - theta)) * (|lam i| * |g - h|)
        ≤ ((G * Lam) ^ 3 / (1 - theta)) * (Lam * |g - h|) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hLi (abs_nonneg _)
    refine le_trans h1 ?_
    have h2 : ((G * Lam) ^ 3 / (1 - theta)) * (Lam * |g - h|)
        = (Lam ^ 4 / (1 - theta)) * G ^ 3 * |g - h| := by
      field_simp
    exact le_of_eq h2
  have hsub : logDetChannel lam g - logDetChannel lam h
      = ∑ i, (logQuartic (g * lam i) - logQuartic (h * lam i)) := by
    rw [logDetChannel, logDetChannel, Finset.sum_sub_distrib]
  rw [hsub]
  calc |∑ i, (logQuartic (g * lam i) - logQuartic (h * lam i))|
      ≤ ∑ i, |logQuartic (g * lam i) - logQuartic (h * lam i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (Lam ^ 4 / (1 - theta)) * G ^ 3 * |g - h| :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι * Lam ^ 4 / (1 - theta)) * G ^ 3 * |g - h| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## 4. The polynomial channel, differentiated -/

/-- **A Cauchy family, differentiated.**  From `|a_n| ≤ A·K^{n+4}` and
`KG ≤ ρ < 1`,
`|R(g) − R(h)| ≤ A·K⁴·((4−3ρ)/(1−ρ)²)·G³·|g − h|` on `0 ≤ g, h ≤ G`.
This is the estimate that produces the cubic (rather than quartic) sensitivity
of the interaction sector from the same analyticity datum used for the debt. -/
theorem abs_tailPolyChannel_sub_le {a : ℕ → ℝ} {N : ℕ} {A K G rho g h : ℝ}
    (ha : ∀ n, |a n| ≤ A * K ^ (n + 4)) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hgG : g ≤ G) (hhG : h ≤ G)
    (hrho : K * G ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    |tailPolyChannel a N g - tailPolyChannel a N h|
      ≤ A * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) * G ^ 3 * |g - h| := by
  have hG0 : 0 ≤ G := le_trans hg0 hgG
  have hsub : tailPolyChannel a N g - tailPolyChannel a N h
      = ∑ n ∈ range N, a n * (g ^ (n + 4) - h ^ (n + 4)) := by
    rw [tailPolyChannel, tailPolyChannel, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hterm : ∀ n ∈ range N, |a n * (g ^ (n + 4) - h ^ (n + 4))|
      ≤ (A * K ^ 4 * G ^ 3 * |g - h|) * (((n : ℝ) + 4) * rho ^ n) := by
    intro n _
    have hpow : |g ^ (n + 4) - h ^ (n + 4)| ≤ ((n : ℝ) + 4) * G ^ (n + 3) * |g - h| := by
      have := abs_pow_succ_sub_le hg0 hh0 hgG hhG (n + 3)
      have hcast : ((↑(n + 3) : ℝ) + 1) = (n : ℝ) + 4 := by push_cast; ring
      rw [hcast] at this
      simpa [show n + 3 + 1 = n + 4 from rfl] using this
    have h1 : |a n * (g ^ (n + 4) - h ^ (n + 4))|
        ≤ (A * K ^ (n + 4)) * (((n : ℝ) + 4) * G ^ (n + 3) * |g - h|) := by
      rw [abs_mul]
      refine mul_le_mul (ha n) hpow (abs_nonneg _) (by positivity)
    refine le_trans h1 ?_
    have hKG : (K * G) ^ n ≤ rho ^ n := pow_le_pow_left₀ (by positivity) hrho n
    have hid : (A * K ^ (n + 4)) * (((n : ℝ) + 4) * G ^ (n + 3) * |g - h|)
        = (A * K ^ 4 * G ^ 3 * |g - h|) * (((n : ℝ) + 4) * (K * G) ^ n) := by
      rw [mul_pow, pow_add, pow_add]
      ring
    rw [hid]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hKG (by positivity)
  rw [hsub]
  calc |∑ n ∈ range N, a n * (g ^ (n + 4) - h ^ (n + 4))|
      ≤ ∑ n ∈ range N, |a n * (g ^ (n + 4) - h ^ (n + 4))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, (A * K ^ 4 * G ^ 3 * |g - h|) * (((n : ℝ) + 4) * rho ^ n) :=
        Finset.sum_le_sum hterm
    _ = (A * K ^ 4 * G ^ 3 * |g - h|) * ∑ n ∈ range N, ((n : ℝ) + 4) * rho ^ n := by
        rw [Finset.mul_sum]
    _ ≤ (A * K ^ 4 * G ^ 3 * |g - h|) * ((4 - 3 * rho) / (1 - rho) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_add_four_mul_geom_le hrho0 hrho1 N) (by positivity)
    _ = A * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) * G ^ 3 * |g - h| := by ring

/-! ## 5. The assembled interaction sector -/

/-- The five literal remainder channels with their coefficients frozen: exactly
`shellInteractionOfChannels` at a fixed history, read as a function of the
coupling alone. -/
noncomputable def frozenShellInteraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lamD : ι → ℝ) (lamG : κ → ℝ) (aI aC aL : ℕ → ℝ) (N : ℕ) (g : ℝ) : ℝ :=
  logDetChannel lamD g + tailPolyChannel aI N g + tailPolyChannel aC N g
    + logDetChannel lamG g + tailPolyChannel aL N g

theorem shellInteractionOfChannels_eq_frozen {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lamDet : ℕ → (ℕ → ℝ) → ι → ℝ) (lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ)
    (aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ) (N j : ℕ) (hst : ℕ → ℝ) :
    shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N j hst
      = frozenShellInteraction (lamDet j hst) (lamGauge j hst) (aInt j hst)
          (aChart j hst) (aLoc j hst) N (hst j) := rfl

/-- **The differentiated five-channel constant.**  The exact analogue of
`analyticCbetaBound` for the sensitivity: the same spectral data and the same
Cauchy pair, with the derivative weights `1/(1−θ)` and `(4−3ρ)/(1−ρ)²` in place
of the value weights `1/(4(1−θ))` and `1/(1−Kθ)`. -/
noncomputable def analyticDirectSensitivityBound (cardDet cardGauge : ℕ)
    (LamDet LamGauge theta AI AC AL K rho : ℝ) : ℝ :=
  cardDet * LamDet ^ 4 / (1 - theta) + cardGauge * LamGauge ^ 4 / (1 - theta)
    + (AI + AC + AL) * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2)

theorem analyticDirectSensitivityBound_nonneg {cardDet cardGauge : ℕ}
    {LamDet LamGauge theta AI AC AL K rho : ℝ}
    (hth : theta < 1) (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL)
    (hrho1 : rho < 1) :
    0 ≤ analyticDirectSensitivityBound cardDet cardGauge LamDet LamGauge theta AI AC AL K rho := by
  have h1 : (0 : ℝ) < 1 - theta := by linarith
  have h2 : (0 : ℝ) < (1 - rho) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ 4 - 3 * rho := by linarith
  have h4 : (0 : ℝ) ≤ (4 - 3 * rho) / (1 - rho) ^ 2 := by positivity
  rw [analyticDirectSensitivityBound]
  have : (0 : ℝ) ≤ (AI + AC + AL) * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) := by
    have hK4 : (0 : ℝ) ≤ K ^ 4 := by positivity
    have : (0 : ℝ) ≤ AI + AC + AL := by linarith
    positivity
  have hd : (0 : ℝ) ≤ (cardDet : ℝ) * LamDet ^ 4 / (1 - theta) := by positivity
  have hg : (0 : ℝ) ≤ (cardGauge : ℝ) * LamGauge ^ 4 / (1 - theta) := by positivity
  linarith

/-- **The whole interaction sector is Lipschitz in the coupling with a cubically
suppressed constant, from the literal source norms.** -/
theorem abs_frozenShellInteraction_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {lamD : ι → ℝ} {lamG : κ → ℝ} {aI aC aL : ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL K G rho g h : ℝ}
    (hLd : ∀ i, |lamD i| ≤ LamDet) (hLg : ∀ i, |lamG i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ n, |aI n| ≤ AI * K ^ (n + 4)) (hC : ∀ n, |aC n| ≤ AC * K ^ (n + 4))
    (hLc : ∀ n, |aL n| ≤ AL * K ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ K)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hgG : g ≤ G) (hhG : h ≤ G)
    (hGLd : G * LamDet ≤ theta) (hGLg : G * LamGauge ≤ theta) (hth : theta < 1)
    (hrho : K * G ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    |frozenShellInteraction lamD lamG aI aC aL N g
        - frozenShellInteraction lamD lamG aI aC aL N h|
      ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
          LamDet LamGauge theta AI AC AL K rho * G ^ 3 * |g - h| := by
  have hD := abs_logDetChannel_sub_le (lam := lamD) (Lam := LamDet) (theta := theta)
    (G := G) hLd hLd0 hg0 hh0 hgG hhG hGLd hth
  have hGa := abs_logDetChannel_sub_le (lam := lamG) (Lam := LamGauge) (theta := theta)
    (G := G) hLg hLg0 hg0 hh0 hgG hhG hGLg hth
  have hI' := abs_tailPolyChannel_sub_le (a := aI) (N := N) (A := AI) (K := K) (G := G)
    (rho := rho) hI hAI hK hg0 hh0 hgG hhG hrho hrho0 hrho1
  have hC' := abs_tailPolyChannel_sub_le (a := aC) (N := N) (A := AC) (K := K) (G := G)
    (rho := rho) hC hAC hK hg0 hh0 hgG hhG hrho hrho0 hrho1
  have hL' := abs_tailPolyChannel_sub_le (a := aL) (N := N) (A := AL) (K := K) (G := G)
    (rho := rho) hLc hAL hK hg0 hh0 hgG hhG hrho hrho0 hrho1
  have hsplit : frozenShellInteraction lamD lamG aI aC aL N g
      - frozenShellInteraction lamD lamG aI aC aL N h
      = (logDetChannel lamD g - logDetChannel lamD h)
        + (tailPolyChannel aI N g - tailPolyChannel aI N h)
        + (tailPolyChannel aC N g - tailPolyChannel aC N h)
        + (logDetChannel lamG g - logDetChannel lamG h)
        + (tailPolyChannel aL N g - tailPolyChannel aL N h) := by
    rw [frozenShellInteraction, frozenShellInteraction]; ring
  have habs : |frozenShellInteraction lamD lamG aI aC aL N g
      - frozenShellInteraction lamD lamG aI aC aL N h|
      ≤ |logDetChannel lamD g - logDetChannel lamD h|
        + |tailPolyChannel aI N g - tailPolyChannel aI N h|
        + |tailPolyChannel aC N g - tailPolyChannel aC N h|
        + |logDetChannel lamG g - logDetChannel lamG h|
        + |tailPolyChannel aL N g - tailPolyChannel aL N h| := by
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _)
      (add_le_add (le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _)
        (add_le_add (le_refl _) (le_refl _))) (le_refl _))) (le_refl _))) (le_refl _))
  have hcollect : (Fintype.card ι * LamDet ^ 4 / (1 - theta)) * G ^ 3 * |g - h|
      + AI * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) * G ^ 3 * |g - h|
      + AC * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) * G ^ 3 * |g - h|
      + (Fintype.card κ * LamGauge ^ 4 / (1 - theta)) * G ^ 3 * |g - h|
      + AL * K ^ 4 * ((4 - 3 * rho) / (1 - rho) ^ 2) * G ^ 3 * |g - h|
      = analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
          LamDet LamGauge theta AI AC AL K rho * G ^ 3 * |g - h| := by
    rw [analyticDirectSensitivityBound]; ring
  linarith [habs, hD, hGa, hI', hC', hL', hcollect.le, hcollect.ge]

end YangMills
