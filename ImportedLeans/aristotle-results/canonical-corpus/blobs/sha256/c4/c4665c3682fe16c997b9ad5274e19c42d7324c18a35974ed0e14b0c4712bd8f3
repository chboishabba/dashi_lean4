/-
# Charging the modulus active set to the finite budget

The De Giorgi route asks for control of *every* bad level separately.  The
cheaper mechanism — the one the shell/dissipation ledger uses — is to charge the
total space-time occupation of the bad set to a finite budget, and to observe
that the occupation therefore has to vanish as the level grows.  This file makes
that bridge for the *modulus* carrier, whose active set is a spatial level set
of `|δ_h u|` rather than a Fourier shell.

* `ClayNS.modulusActive` — the active set at level `k` on a region.
* `ClayNS.level_measure_le_setIntegral_rpow` — the Chebyshev step: the measure of
  the active set is charged to any `L^p` budget of the carrier,
  `kᵖ·μ(A_k) ≤ ∫|q|ᵖ`.
* `ClayNS.occupation_le_of_budget` — the space-time form: the total occupation
  `∫μ(A_k(t))dt` of the bad set is at most `B/kᵖ`, where `B` is the space-time
  budget produced by the parabolic embedding.
* `ClayNS.occupation_tendsto_zero` and `ClayNS.exists_level_occupation_lt` — the
  consequence: the occupation of the bad set tends to zero as the level grows,
  so beyond an explicit level the bad set occupies less than any prescribed
  amount.  Together with `ClayNS.compactCarrier_parabolic_gain` (which supplies
  the budget `B = C_S·K^{5/3}` at `p = 10/3`) this is the modulus analogue of
  the shell residence charge of `ExpenditureLedger.lean`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CompactCarrierBridge
import RequestProject.NavierStokes.ExpenditureLedger

open MeasureTheory Set Filter

noncomputable section

namespace ClayNS

/-- The active set of the modulus carrier at level `k` on a region. -/
def modulusActive (S : Set E3) (q : E3 → ℝ) (k : ℝ) : Set E3 := {x | x ∈ S ∧ k ≤ q x}

lemma measurableSet_modulusActive {S : Set E3} (hS : MeasurableSet S) {q : E3 → ℝ}
    (hq : Continuous q) (k : ℝ) : MeasurableSet (modulusActive S q k) := by
  have h1 : MeasurableSet {x : E3 | k ≤ q x} :=
    measurableSet_le measurable_const hq.measurable
  simpa [modulusActive, Set.setOf_and] using hS.inter h1

lemma modulusActive_subset (S : Set E3) (q : E3 → ℝ) (k : ℝ) :
    modulusActive S q k ⊆ S := fun _ hx => hx.1

/-! ## The Chebyshev charge -/

/-- **The Chebyshev charge.**  The measure of the active set at level `k` is
charged to the `L^p` budget of the carrier: `kᵖ·μ(A_k) ≤ ∫_S|q|ᵖ`. -/
theorem level_measure_le_setIntegral_rpow {S : Set E3} (hS : MeasurableSet S)
    (hSfin : volume S ≠ ⊤) {q : E3 → ℝ} (hq : Continuous q) {k p : ℝ} (hk : 0 < k)
    (hp : 0 < p) (hint : IntegrableOn (fun x => |q x| ^ p) S volume) :
    k ^ p * (volume (modulusActive S q k)).toReal ≤ ∫ x in S, |q x| ^ p := by
  set A := modulusActive S q k with hA
  have hAmeas : MeasurableSet A := measurableSet_modulusActive hS hq k
  have hAsub : A ⊆ S := modulusActive_subset S q k
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hSfin (measure_mono hAsub)
  have hnn : ∀ x, 0 ≤ |q x| ^ p := fun x => Real.rpow_nonneg (abs_nonneg _) _
  -- restrict to the active set
  have hrestrict : (∫ x in A, |q x| ^ p) ≤ ∫ x in S, |q x| ^ p :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hnn)
      (Filter.Eventually.of_forall hAsub)
  -- on the active set the integrand is at least `kᵖ`
  have hlow : ∀ x ∈ A, k ^ p ≤ |q x| ^ p := by
    intro x hx
    have hx2 : k ≤ q x := hx.2
    have hqx : k ≤ |q x| := le_trans hx2 (le_abs_self _)
    exact Real.rpow_le_rpow hk.le hqx hp.le
  have hconst : (∫ x in A, k ^ p) ≤ ∫ x in A, |q x| ^ p := by
    refine setIntegral_mono_on (integrableOn_const (by simp [hAfin]))
      (hint.mono_set hAsub) hAmeas hlow
  rw [setIntegral_const, smul_eq_mul] at hconst
  have : k ^ p * (volume A).toReal = (volume A).toReal * k ^ p := by ring
  rw [this]
  simp only [measureReal_def] at hconst
  linarith [hconst, hrestrict]

/-! ## The space-time occupation -/

/-- **The occupation bound.**  If the space-time `L^p` budget of the carrier is
`B`, then the total occupation of the bad set at level `k` is at most `B/kᵖ`. -/
theorem occupation_le_of_budget {a b k p B : ℝ} {S : Set E3} (hab : a ≤ b)
    (hk : 0 < k) {q : ℝ → E3 → ℝ}
    (hslice : ∀ t ∈ Icc a b,
      k ^ p * (volume (modulusActive S (q t) k)).toReal ≤ ∫ x in S, |q t x| ^ p)
    (hocc : IntervalIntegrable
      (fun t => (volume (modulusActive S (q t) k)).toReal) volume a b)
    (hbud : IntervalIntegrable (fun t => ∫ x in S, |q t x| ^ p) volume a b)
    (hB : (∫ t in a..b, ∫ x in S, |q t x| ^ p) ≤ B) :
    (∫ t in a..b, (volume (modulusActive S (q t) k)).toReal) ≤ B / k ^ p := by
  have hkp : 0 < k ^ p := Real.rpow_pos_of_pos hk p
  have hmono := intervalIntegral.integral_mono_on hab (hocc.const_mul (k ^ p)) hbud hslice
  rw [intervalIntegral.integral_const_mul] at hmono
  have : k ^ p * ∫ t in a..b, (volume (modulusActive S (q t) k)).toReal ≤ B := by
    linarith [hmono, hB]
  rw [le_div_iff₀ hkp]
  linarith [this]

/-- The occupation budget `B/kᵖ` vanishes as the level grows. -/
theorem occupation_tendsto_zero {p B : ℝ} (hp : 0 < p) :
    Tendsto (fun k : ℝ => B / k ^ p) atTop (nhds 0) := by
  have h1 : Tendsto (fun k : ℝ => k ^ p) atTop atTop := tendsto_rpow_atTop hp
  simpa [div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul B

/-- **Finite occupation at high levels.**  For any prescribed amount `eps > 0`
there is a level beyond which the bad set occupies less than `eps` of space-time
budget.  This is the modulus form of "charge the total bad residence to the
finite dissipation": no level-by-level control is needed. -/
theorem exists_level_occupation_lt {p B eps : ℝ} (hp : 0 < p) (heps : 0 < eps) :
    ∃ k0 : ℝ, 0 < k0 ∧ ∀ k ≥ k0, B / k ^ p < eps := by
  have htend := occupation_tendsto_zero (p := p) (B := B) hp
  have hev : ∀ᶠ k : ℝ in atTop, B / k ^ p < eps := by
    have := htend.eventually (eventually_lt_nhds heps)
    exact this
  obtain ⟨k1, hk1⟩ := (hev.and (eventually_gt_atTop (0:ℝ))).exists_forall_of_atTop
  refine ⟨max k1 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun k hk => ?_⟩
  exact (hk1 k (le_trans (le_max_left _ _) hk)).1

/-! ## The assembled bridge -/

/-- **The modulus occupation bridge.**  Combining the Chebyshev charge with a
space-time budget: with the budget `B` for `∫∫|q|ᵖ` on the region `S`, the total
occupation of the level-`k` active set is at most `B/kᵖ`, and hence smaller than
any prescribed amount for `k` large.  With `p = 10/3` and
`B = C_S·K^{5/3}` supplied by `ClayNS.compactCarrier_parabolic_gain`, this
charges the modulus active set directly to the Caccioppoli budget. -/
theorem modulus_occupation_bridge {a b p B : ℝ} {S : Set E3} (hS : MeasurableSet S)
    (hSfin : volume S ≠ ⊤) (hab : a ≤ b) (hp : 0 < p) {q : ℝ → E3 → ℝ}
    (hq : ∀ t, Continuous (q t))
    (hint : ∀ t, IntegrableOn (fun x => |q t x| ^ p) S volume)
    (hbud : IntervalIntegrable (fun t => ∫ x in S, |q t x| ^ p) volume a b)
    (hB : (∫ t in a..b, ∫ x in S, |q t x| ^ p) ≤ B)
    {k : ℝ} (hk : 0 < k)
    (hocc : IntervalIntegrable
      (fun t => (volume (modulusActive S (q t) k)).toReal) volume a b) :
    (∫ t in a..b, (volume (modulusActive S (q t) k)).toReal) ≤ B / k ^ p :=
  occupation_le_of_budget hab hk
    (fun t _ => level_measure_le_setIntegral_rpow hS hSfin (hq t) hk hp (hint t))
    hocc hbud hB

/-! ## End to end: from the Gaussian-weighted budget to a small bad set -/

/-- **The end-to-end occupation bound.**  Starting from the Gaussian-weighted
Caccioppoli budget on the concentration ball — a sup-in-time weighted mass `Mw`
and a total weighted dissipation `Dw` — the modulus bad set at level `k` *inside
the half ball*, where the cut-off is one, occupies at most

  `C_S·K^{5/3}/k^{10/3}`,  `K = 2e^{1/(4κ)}(Mw + Dw + L²(b−a)Mw)`,

of space-time.  Composing `ClayNS.compactCarrier_parabolic_gain` with the
Chebyshev charge, this is the modulus form of "charge the bad residence to the
finite budget": the occupation vanishes as the level grows, with an explicit
rate and with all constants independent of the level. -/
theorem halfBall_occupation_le_of_weighted_budget {kap R a b Mw Dw k : ℝ}
    (hkap : 0 < kap) (hR : 0 < R) (x0 : E3) (psi : BallCutoff x0 R)
    (hone : ∀ x ∈ concBall x0 (R / 2), psi.fn x = 1)
    (hab : a ≤ b) (hMw : 0 ≤ Mw) (hDw : 0 ≤ Dw) (hk : 0 < k)
    {q : ℝ → E3 → ℝ} (hq : ∀ t, ContDiff ℝ 1 (q t))
    (hmass : ∀ t ∈ Icc a b,
      (∫ x in concBall x0 R, torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ Mw)
    (hdiss : (∫ t in a..b, ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2) ≤ Dw)
    (hintM : IntervalIntegrable (fun t => ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) volume a b)
    (hintD : IntervalIntegrable (fun t => ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2) volume a b)
    (hint1 : IntervalIntegrable
      (fun t => ∫ x, |psi.carrier (q t) x| ^ (10 / 3 : ℝ)) volume a b)
    (hint2 : IntervalIntegrable
      (fun t => ∫ x, ‖fderiv ℝ (psi.carrier (q t)) x‖ ^ 2) volume a b)
    (hintHalf : IntervalIntegrable
      (fun t => ∫ x in concBall x0 (R / 2), |q t x| ^ (10 / 3 : ℝ)) volume a b)
    (hocc : IntervalIntegrable (fun t =>
      (volume (modulusActive (concBall x0 (R / 2)) (q t) k)).toReal) volume a b) :
    (∫ t in a..b, (volume (modulusActive (concBall x0 (R / 2)) (q t) k)).toReal)
      ≤ (sobolevConstE3 ^ 2
          * (2 * Real.exp (1 / (4 * kap))
              * (Mw + Dw + psi.gradBound ^ 2 * (b - a) * Mw)) ^ (5 / 3 : ℝ))
        / k ^ (10 / 3 : ℝ) := by
  set S := concBall x0 (R / 2) with hS
  have hRhalf : (0:ℝ) < R / 2 := by linarith
  have hSmeas : MeasurableSet S := measurableSet_concBall x0 hRhalf.le
  have hScomp : IsCompact S := isCompact_concBall x0 hRhalf.le
  have hSfin : volume S ≠ ⊤ := hScomp.measure_ne_top
  -- on the half ball the carrier is the modulus itself
  have hslice : ∀ t, (∫ x in S, |q t x| ^ (10 / 3 : ℝ))
      ≤ ∫ x, |psi.carrier (q t) x| ^ (10 / 3 : ℝ) := by
    intro t
    have hcarrc : Continuous (psi.carrier (q t)) :=
      (psi.smooth.continuous).mul (hq t).continuous
    have hgc : Continuous (fun x => |psi.carrier (q t) x| ^ (10 / 3 : ℝ)) :=
      (continuous_abs.comp hcarrc).rpow_const fun _ => Or.inr (by norm_num)
    have hgs : HasCompactSupport (fun x => |psi.carrier (q t) x| ^ (10 / 3 : ℝ)) :=
      (psi.carrier_hasCompactSupport hR.le (q t)).comp_left
        (g := fun y : ℝ => |y| ^ (10 / 3 : ℝ)) (by simp [Real.zero_rpow])
    have hgint : Integrable (fun x => |psi.carrier (q t) x| ^ (10 / 3 : ℝ)) volume :=
      hgc.integrable_of_hasCompactSupport hgs
    have heq : (∫ x in S, |q t x| ^ (10 / 3 : ℝ))
        = ∫ x in S, |psi.carrier (q t) x| ^ (10 / 3 : ℝ) := by
      refine setIntegral_congr_fun hSmeas fun x hx => ?_
      rw [show psi.carrier (q t) x = q t x by
        simp [BallCutoff.carrier, hone x hx]]
    rw [heq]
    exact setIntegral_le_integral hgint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hbudget : (∫ t in a..b, ∫ x in S, |q t x| ^ (10 / 3 : ℝ))
      ≤ sobolevConstE3 ^ 2
        * (2 * Real.exp (1 / (4 * kap))
            * (Mw + Dw + psi.gradBound ^ 2 * (b - a) * Mw)) ^ (5 / 3 : ℝ) := by
    have hmono := intervalIntegral.integral_mono_on hab hintHalf hint1
      (fun t _ => hslice t)
    exact hmono.trans (compactCarrier_parabolic_gain hkap hR x0 psi hab hMw hDw hq
      hmass hdiss hintM hintD hint1 hint2)
  have hint : ∀ t, IntegrableOn (fun x => |q t x| ^ (10 / 3 : ℝ)) S volume := by
    intro t
    have hgc : Continuous (fun x => |q t x| ^ (10 / 3 : ℝ)) :=
      (continuous_abs.comp (hq t).continuous).rpow_const fun _ => Or.inr (by norm_num)
    exact hgc.continuousOn.integrableOn_compact hScomp
  exact modulus_occupation_bridge hSmeas hSfin hab (by norm_num)
    (fun t => (hq t).continuous) hint hintHalf hbudget hk hocc

/-! ## The residence charge over a finite family of bad time cells -/

/-- **The modulus residence charge.**  Over any finite family of time cells, the
*total* occupation of the level-`k` modulus active set is charged to the summed
finite budget:

  `∑ᵢ ∫_{aᵢ}^{bᵢ} μ(A_k(t))dt ≤ (∑ᵢ Bᵢ)/kᵖ`.

This is the modulus analogue of the shell residence charge
`ClayNS.residence_charge_sum`: no bad cell is controlled separately, only their
aggregate, and the aggregate is paid for by the aggregate budget. -/
theorem modulus_residence_charge {ι : Type*} (s : Finset ι) {p k : ℝ} (hk : 0 < k)
    {a b : ι → ℝ} {S : Set E3} {q : ℝ → E3 → ℝ} {B : ι → ℝ}
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hslice : ∀ i ∈ s, ∀ t ∈ Icc (a i) (b i),
      k ^ p * (volume (modulusActive S (q t) k)).toReal ≤ ∫ x in S, |q t x| ^ p)
    (hocc : ∀ i ∈ s, IntervalIntegrable
      (fun t => (volume (modulusActive S (q t) k)).toReal) volume (a i) (b i))
    (hbud : ∀ i ∈ s, IntervalIntegrable
      (fun t => ∫ x in S, |q t x| ^ p) volume (a i) (b i))
    (hB : ∀ i ∈ s, (∫ t in (a i)..(b i), ∫ x in S, |q t x| ^ p) ≤ B i) :
    ∑ i ∈ s, (∫ t in (a i)..(b i), (volume (modulusActive S (q t) k)).toReal)
      ≤ (∑ i ∈ s, B i) / k ^ p := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  exact occupation_le_of_budget (hab i hi) hk (hslice i hi) (hocc i hi) (hbud i hi) (hB i hi)

end ClayNS
