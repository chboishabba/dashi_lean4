/-
# Row A1 (remainders lane) — all three polynomial channels from *one* source norm

`QuarticChannelSources` computes the five remainder channels from per-degree
majorants `A_n` for the Taylor coefficients of each channel.  That is more data
than the source actually supplies, and more than is needed: small-field
analyticity of the effective action supplies a **single Cauchy pair** `(A, K)`
with

    |a_n| ≤ A·Kⁿ

for every channel at once.  This file feeds all three polynomial channels from
that one datum and produces an `N`-independent closed-form debt constant:

    Σ_{n<N} |A Kⁿ|·θⁿ ≤ A/(1 − Kθ)                (`geometricMajorant_sum_le`)

hence

    C_β ≤ card_det·Λ_det⁴/(4(1−θ)) + card_gauge·Λ_gauge⁴/(4(1−θ))
          + (A_int + A_chart + A_loc)/(1 − Kθ)      (`analyticCbetaBound`)

with no dependence on the truncation order `N`.  Since the admissible coupling
`γ_* = b/(2(C_β + b))` is *antitone* in `C_β`, a coupling below the threshold
computed from this bound is below the true threshold, so the Row A1a shell bound
runs unchanged:

* `A1_beta_pos_ward_from_analyticChannels` — the shell bound `β_j ≥ 1/16777216`
  with the Gaussian sector driven by kernel data and the entire remainder sector
  driven by one small-field Cauchy pair.

**Honest status — Row A1 is not closed.**  The Cauchy pair itself is a source
estimate; what is removed here is the need for five independent majorant
families and for any `N`-dependent constant.
-/
import RequestProject.YangMills.ZeroMassKernelVanishing

namespace YangMills

open Real Finset

/-! ## 1. The geometric majorant sum -/

/-- The truncated geometric series is bounded by its limit. -/
theorem geom_partial_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, r ^ n ≤ (1 - r)⁻¹ :=
  sum_le_hasSum _ (fun n _ => pow_nonneg h0 n) (hasSum_geometric_of_lt_one h0 h1)

/-- **One Cauchy pair bounds a whole channel.**  If the Taylor coefficients of a
channel obey `|a_n| ≤ A·Kⁿ`, then the truncated channel coefficient computed by
`sourceChannelCoefficient` is at most `A/(1 − Kθ)`, uniformly in the truncation
order. -/
theorem geometricMajorant_sum_le {A K theta : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hth0 : 0 ≤ theta) (hKth : K * theta < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, |A * K ^ n| * theta ^ n ≤ A / (1 - K * theta) := by
  have hr0 : 0 ≤ K * theta := mul_nonneg hK hth0
  have hterm : ∀ n ∈ Finset.range N, |A * K ^ n| * theta ^ n = A * (K * theta) ^ n := by
    intro n _
    rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg (pow_nonneg hK n), mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeo := geom_partial_le_inv hr0 hKth N
  calc A * ∑ n ∈ Finset.range N, (K * theta) ^ n ≤ A * (1 - K * theta)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo hA
    _ = A / (1 - K * theta) := by rw [div_eq_mul_inv]

/-! ## 2. The `N`-independent debt constant -/

/-- The five-channel debt constant computed from spectral data and a single
small-field Cauchy pair. -/
noncomputable def analyticCbetaBound (cardDet cardGauge : ℕ)
    (LamDet LamGauge theta AI AC AL K : ℝ) : ℝ :=
  cardDet * LamDet ^ 4 / (4 * (1 - theta))
    + cardGauge * LamGauge ^ 4 / (4 * (1 - theta))
    + (AI + AC + AL) / (1 - K * theta)

/-- **The assembled debt constant is bounded by the analytic one.** -/
theorem Cbeta_sourceChannelCoefficient_analytic_le
    {cardDet cardGauge : ℕ} {LamDet LamGauge theta AI AC AL K : ℝ} {N : ℕ}
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ K)
    (hth0 : 0 ≤ theta) (hKth : K * theta < 1) :
    Cbeta (sourceChannelCoefficient cardDet cardGauge LamDet LamGauge theta
        (fun n => AI * K ^ n) (fun n => AC * K ^ n) (fun n => AL * K ^ n) N)
      ≤ analyticCbetaBound cardDet cardGauge LamDet LamGauge theta AI AC AL K := by
  rw [Cbeta_sourceChannelCoefficient, analyticCbetaBound]
  have h1 := geometricMajorant_sum_le (A := AI) hAI hK hth0 hKth N
  have h2 := geometricMajorant_sum_le (A := AC) hAC hK hth0 hKth N
  have h3 := geometricMajorant_sum_le (A := AL) hAL hK hth0 hKth N
  have hden : 0 < 1 - K * theta := by linarith
  have hsum : AI / (1 - K * theta) + AC / (1 - K * theta) + AL / (1 - K * theta)
      = (AI + AC + AL) / (1 - K * theta) := by field_simp
  linarith [hsum.le, hsum.ge]

/-! ## 3. Monotonicity of the admissible coupling -/

/-- The admissible coupling `γ_* = b/(2(C_β + b))` is antitone in the debt
constant: a larger debt bound gives a smaller — hence safe — threshold. -/
theorem criticalCoupling_antitone {b Cb Cb' : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb)
    (hle : Cb ≤ Cb') : criticalCoupling b Cb' ≤ criticalCoupling b Cb := by
  have h1 : 0 < 2 * (Cb + b) := by linarith
  have h2 : 0 < 2 * (Cb' + b) := by linarith
  rw [criticalCoupling, criticalCoupling, div_le_div_iff₀ h2 h1]
  nlinarith

/-! ## 4. Row A1a with the remainder sector driven by one source norm -/

/-- **Row A1a from kernel data and a single small-field Cauchy pair.**  The
Gaussian sector is the literal one-loop trace with the averaging /
constrained-projection variation and the seagull given by finite-range position
kernels; the whole remainder sector is fed by one analyticity datum `(A, K)` per
channel with a common Cauchy radius, and the admissible-coupling threshold is
the `N`-independent constant `analyticCbetaBound`.

For every shell index and every admissible history, `β_j(g) ≥ 1/16777216 > 0`. -/
theorem A1_beta_pos_ward_from_analyticChannels
    {ι κ ξ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f R M MW AI AC AL K : ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ j h a, ∑ i, Kk j h a i = 0)
    (hd : ∀ j h a i mu, |dd j h a i mu| ≤ R)
    (hmass : ∀ j h a, kernelMass (Kk j h a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ j h a b, kernelMass (KW j h a b) ≤ MW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ K) (hKth : K * theta < 1)
    (hcInt : ∀ j h n, |aInt j h n| ≤ AI * K ^ n)
    (hcChart : ∀ j h n, |aChart j h n| ≤ AC * K ^ n)
    (hcLoc : ∀ j h n, |aLoc j h n| ≤ AL * K ^ n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (analyticCbetaBound (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AI AC AL K))
    (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h) (dd j' h)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g := by
  have hCnn : ∀ k, 0 ≤ sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta (fun n => AI * K ^ n) (fun n => AC * K ^ n)
      (fun n => AL * K ^ n) N k :=
    fun k => sourceChannelCoefficient_nonneg hth hth0 k
  have hCb : 0 ≤ Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta (fun n => AI * K ^ n) (fun n => AC * K ^ n)
      (fun n => AL * K ^ n) N) := Cbeta_nonneg hCnn
  have hle := Cbeta_sourceChannelCoefficient_analytic_le
    (cardDet := Fintype.card ι) (cardGauge := Fintype.card κ)
    (LamDet := LamDet) (LamGauge := LamGauge) (theta := theta) (N := N)
    hAI hAC hAL hK hth0 hKth
  have hmono := criticalCoupling_antitone (b := (1 / 8388608 : ℝ)) (by norm_num) hCb hle
  exact A1_beta_pos_ward_from_kernels (R := R) (M := M) (MW := MW)
    (AInt := fun n => AI * K ^ n) (AChart := fun n => AC * K ^ n)
    (ALoc := fun n => AL * K ^ n)
    hR hM hMW hzero hd hmass hsmallK hmassW hLd hLg hcInt hcChart hcLoc
    hsmall hth hth0 hadm hg0 (fun j' => le_trans (hgg j') hmono) j

end YangMills
