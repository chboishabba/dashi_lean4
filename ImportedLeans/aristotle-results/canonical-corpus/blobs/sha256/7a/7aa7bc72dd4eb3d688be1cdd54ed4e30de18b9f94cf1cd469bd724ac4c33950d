/-
# Row A-ii — the irrelevant-history response kernel pays the shooting sensitivity

The Row-A shooting consumer (`RowAShooting.shooting_exists_unique`,
`RowAShooting.tuned_bare_coupling_window`) asks for one scalar datum: a
cumulative per-shell Lipschitz sum

    Σ_{j<K} L_j ≤ q < 1,      uniformly in the cutoff `K`.

Earlier rounds supplied that by *assuming* a summable history sensitivity.  This
file removes that assumption in favour of the two estimates the RG actually
produces for the irrelevant sector:

* a **one-step response recurrence** for the propagated irrelevant response
  `r_j`,

      r_0 = 0,     r_{j+1} ≤ R·s_j + ½·r_j,

  i.e. the injected source `s_j` from the current shell plus the (geometrically
  contracting) memory of the previous one; and

* a **quartic source budget** `s_j ≤ D·g_j⁴` for that injection.

What is proved:

* `sum_response_of_recurrence` — the recurrence alone gives the *cutoff-uniform*
  prefix estimate `Σ_{j<K} r_j ≤ 2R·Σ_{j<K} s_j`.  No summability of `r` is
  assumed, and no exponential forgetting law is imposed on any coordinate: the
  factor `2 = (1 − ½)⁻¹` is the geometric mass of the response kernel.
* `history_response_budget` — feeding the quartic source budget into the
  repository's own positive-drift telescope (`debt_block_telescope`) turns this
  into the cutoff-uniform bound `Σ_{j<K} r_j ≤ 2RD·κ·b₋⁻¹·g₀²`,
  `κ = (u₀+b₊)/u₀`.
* `cumulative_lipschitz_of_response` — with a marginal (current-coupling) shell
  sensitivity `m_j ≤ C_m·g_j⁴`, the *total* shell sensitivity obeys
  `Σ_{j<K} L_j ≤ (C_m + 2RD)·κ·b₋⁻¹·g₀²`.  So the marginal and history halves
  are carried by one and the same small-coupling budget; there is no separate
  summability theorem left.
* `response_gate_lt_one`, `canonical_bare_coupling_gate` — the resulting
  smallness condition is met by the *explicit* bare inverse coupling
  `u₀ = b₊ + 2(C_m+2RD)/b₋ + 1`; choosing a sufficiently small bare coupling is
  therefore exact rational arithmetic, not a search.
* `tuned_bare_coupling_of_response` and `tuned_bare_coupling_canonical` — the
  Row-A shooting statement (unique tuned bare coupling hitting the prescribed
  observation-scale value, with the whole trajectory inside the small-field
  window) follows from the response data alone.

**Honest status.**  Everything here is downstream algebra: the physics inputs
are the hypotheses `hrec` (the literal one-step response recurrence of the
generated irrelevant coordinate), `hs` (the quartic injection budget), `hm` (the
marginal shell sensitivity) and the two-sided shell bounds.  None of them is
proved here, and none is transcribed from a source.  Row A is **not** closed by
this file, and the frozen research count is unchanged.
-/
import RequestProject.YangMills.RowACompletion

namespace YangMills

open Finset

/-! ## 1. The response recurrence sums itself -/

/-- **Prefix summation of the one-step response recurrence.**  If the propagated
irrelevant response starts at zero, stays nonnegative and satisfies
`r_{j+1} ≤ R·s_j + ½ r_j`, then for *every* cutoff `K`

    Σ_{j<K} r_j ≤ 2R·Σ_{j<K} s_j.

The constant `2` is the mass `(1 − ½)⁻¹` of the geometric response kernel; no
summability of `r` is assumed. -/
theorem sum_response_of_recurrence {r s : ℕ → ℝ} {R : ℝ}
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2) (K : ℕ) :
    ∑ j ∈ range K, r j ≤ 2 * R * ∑ j ∈ range K, s j := by
  have hshift : ∑ j ∈ range K, r (j + 1) = ∑ j ∈ range (K + 1), r j - r 0 := by
    rw [Finset.sum_range_succ']
    ring
  have hstep : ∑ j ∈ range K, r (j + 1)
      ≤ ∑ j ∈ range K, (R * s j + r j / 2) :=
    Finset.sum_le_sum fun j _ => hrec j
  have hsplit : ∑ j ∈ range K, (R * s j + r j / 2)
      = R * (∑ j ∈ range K, s j) + (∑ j ∈ range K, r j) / 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hmono : ∑ j ∈ range K, r j ≤ ∑ j ∈ range (K + 1), r j := by
    rw [Finset.sum_range_succ]
    linarith [hrnn K]
  rw [hshift, hr0] at hstep
  rw [hsplit] at hstep
  linarith

/-! ## 2. The quartic source budget, on the repository's own positive drift -/

variable {u beta : ℕ → ℝ} {bm bp : ℝ}

/-- **Cutoff-uniform history sensitivity.**  The response recurrence together
with a quartic injection budget `s_j ≤ D·g_j⁴` gives, on any trajectory with a
uniformly positive shell coefficient,

    Σ_{j<K} r_j ≤ 2RD·κ·b₋⁻¹·g₀²,     κ = (u₀+b₊)/u₀,

uniformly in the cutoff `K`.  The summation itself is the repository's positive
inverse-square drift telescope, not a new estimate. -/
theorem history_response_budget {r s : ℕ → ℝ} {R D : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2)
    (hs : ∀ j, s j ≤ D * couplingSq u j ^ 2) (K : ℕ) :
    ∑ j ∈ range K, r j
      ≤ 2 * R * D * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) := by
  have h1 := sum_response_of_recurrence hr0 hrnn hrec K
  have h2 : ∑ j ∈ range K, s j ≤ D * ∑ j ∈ range K, couplingSq u j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hs j
  have h3 : ∑ j ∈ range K, couplingSq u j ^ 2
      ≤ ((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0 := by
    have hrange : range K = Finset.Ico 0 K := congrFun Finset.range_eq_Ico K
    rw [hrange]
    exact debt_block_telescope hstep hb hbu hbm hu0 0 K
  have hRD : (0:ℝ) ≤ 2 * R := by linarith
  have h4 : 2 * R * ∑ j ∈ range K, s j
      ≤ 2 * R * (D * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0)) := by
    refine mul_le_mul_of_nonneg_left ?_ hRD
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hD)
  calc ∑ j ∈ range K, r j ≤ 2 * R * ∑ j ∈ range K, s j := h1
    _ ≤ 2 * R * (D * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0)) := h4
    _ = 2 * R * D * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) := by ring

/-- **Marginal plus history, on one and the same budget.**  With a marginal
(current-coupling) shell sensitivity `m_j ≤ C_m g_j⁴` and the propagated
irrelevant response `r_j` of §1, the total per-shell sensitivity obeys the
cutoff-uniform bound

    Σ_{j<K} L_j ≤ (C_m + 2RD)·κ·b₋⁻¹·g₀². -/
theorem cumulative_lipschitz_of_response {L m r s : ℕ → ℝ} {Cm R D : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hCm : 0 ≤ Cm) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hL : ∀ j, L j ≤ m j + r j) (hm : ∀ j, m j ≤ Cm * couplingSq u j ^ 2)
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2)
    (hs : ∀ j, s j ≤ D * couplingSq u j ^ 2) (K : ℕ) :
    ∑ j ∈ range K, L j
      ≤ (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) := by
  have hsplit : ∑ j ∈ range K, L j ≤ ∑ j ∈ range K, m j + ∑ j ∈ range K, r j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hL j
  have hmsum : ∑ j ∈ range K, m j
      ≤ Cm * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) := by
    have h2 : ∑ j ∈ range K, m j ≤ Cm * ∑ j ∈ range K, couplingSq u j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hm j
    have h3 : ∑ j ∈ range K, couplingSq u j ^ 2
        ≤ ((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0 := by
      have hrange : range K = Finset.Ico 0 K := congrFun Finset.range_eq_Ico K
      rw [hrange]
      exact debt_block_telescope hstep hb hbu hbm hu0 0 K
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hCm)
  have hrsum := history_response_budget (u := u) (beta := beta) (bm := bm) (bp := bp)
    hstep hb hbu hbm hu0 hR hD hr0 hrnn hrec hs K
  nlinarith [hsplit, hmsum, hrsum]

/-! ## 3. One scalar gate, met by an explicit bare coupling -/

/-- The Row-A response gate: the cumulative sensitivity budget of §2 is `< 1`. -/
def responseGate (Cm R D bm bp u₀ : ℝ) : Prop :=
  (Cm + 2 * R * D) * (((u₀ + bp) / u₀) * bm⁻¹ * u₀⁻¹) < 1

/-- **The gate holds at any sufficiently small bare coupling.**  If
`b₊ ≤ u₀` and `2(C_m+2RD) < b₋·u₀`, the response gate is satisfied. -/
theorem response_gate_lt_one {Cm R D bm bp u₀ : ℝ}
    (hbm : 0 < bm) (hbp : 0 ≤ bp) (hA : 0 ≤ Cm + 2 * R * D)
    (hu₀ : 0 < u₀) (hbpu : bp ≤ u₀) (hsmall : 2 * (Cm + 2 * R * D) < bm * u₀) :
    responseGate Cm R D bm bp u₀ := by
  have hkappa : (u₀ + bp) / u₀ ≤ 2 := by
    rw [div_le_iff₀ hu₀]
    linarith
  have hkpos : 0 < (u₀ + bp) / u₀ := by positivity
  have hbminv : 0 < bm⁻¹ := inv_pos.mpr hbm
  have hu₀inv : 0 < u₀⁻¹ := inv_pos.mpr hu₀
  have hstep1 : ((u₀ + bp) / u₀) * bm⁻¹ * u₀⁻¹ ≤ 2 * bm⁻¹ * u₀⁻¹ := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkappa hbminv.le) hu₀inv.le
    linarith
  have hstep2 : (Cm + 2 * R * D) * (((u₀ + bp) / u₀) * bm⁻¹ * u₀⁻¹)
      ≤ (Cm + 2 * R * D) * (2 * bm⁻¹ * u₀⁻¹) :=
    mul_le_mul_of_nonneg_left hstep1 hA
  have hfinal : (Cm + 2 * R * D) * (2 * bm⁻¹ * u₀⁻¹) < 1 := by
    have hpos : 0 < bm * u₀ := by positivity
    have hid : (Cm + 2 * R * D) * (2 * bm⁻¹ * u₀⁻¹)
        = 2 * (Cm + 2 * R * D) / (bm * u₀) := by
      field_simp
    rw [hid, div_lt_one hpos]
    linarith
  exact lt_of_le_of_lt hstep2 hfinal

/-- **Canonical bare inverse coupling.**  Given the four finite constants, the
*explicit* value `u₀ = b₊ + 2(C_m+2RD)/b₋ + 1` is positive and satisfies the
response gate.  No search over small couplings is required. -/
theorem canonical_bare_coupling_gate {Cm R D bm bp : ℝ}
    (hbm : 0 < bm) (hbp : 0 ≤ bp) (hA : 0 ≤ Cm + 2 * R * D) :
    0 < bp + 2 * (Cm + 2 * R * D) / bm + 1
      ∧ responseGate Cm R D bm bp (bp + 2 * (Cm + 2 * R * D) / bm + 1) := by
  set A : ℝ := Cm + 2 * R * D with hAdef
  set u₀ : ℝ := bp + 2 * A / bm + 1 with hu₀def
  have hAbm : 0 ≤ 2 * A / bm := by positivity
  have hu₀pos : 0 < u₀ := by rw [hu₀def]; linarith
  refine ⟨hu₀pos, ?_⟩
  refine response_gate_lt_one hbm hbp hA hu₀pos (by rw [hu₀def]; linarith) ?_
  have h1 : 2 * A / bm < u₀ := by rw [hu₀def]; linarith
  have h2 : 2 * A < bm * u₀ := by
    rw [div_lt_iff₀ hbm] at h1
    linarith [h1]
  exact h2

/-! ## 4. The tuned bare coupling, from response data only -/

/-- **Row-A shooting from the response kernel.**  Per-shell Lipschitz data split
into a marginal quartic part and the propagated irrelevant response gives a
unique tuned bare coupling landing on the prescribed observation-scale value,
with the whole trajectory inside the small-field window. -/
theorem tuned_bare_coupling_of_response {bet : ℕ → ℝ → ℝ} {L m r s : ℕ → ℝ}
    {Cm R D target : ℝ} {K : ℕ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hCm : 0 ≤ Cm) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hLip : ∀ j v w, |bet j v - bet j w| ≤ L j * |v - w|)
    (hLnn : ∀ j, 0 ≤ L j)
    (hL : ∀ j, L j ≤ m j + r j) (hm : ∀ j, m j ≤ Cm * couplingSq u j ^ 2)
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2)
    (hs : ∀ j, s j ≤ D * couplingSq u j ^ 2)
    (hgate : (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) < 1)
    (hZl : ∀ j v, bm ≤ bet j v) (hZu : ∀ j v, bet j v ≤ bp) (hbmnn : 0 ≤ bm)
    (hwin : 0 < target - bp * K) :
    ∃ v : ℝ, (shootingTrajectory bet v K = target)
      ∧ (∀ j ≤ K, target - bp * K ≤ shootingTrajectory bet v j)
      ∧ (∀ j ≤ K, 0 < couplingSq (shootingTrajectory bet v) j
            ∧ couplingSq (shootingTrajectory bet v) j ≤ (target - bp * K)⁻¹)
      ∧ couplingSq (shootingTrajectory bet v) K = target⁻¹ := by
  have hq := cumulative_lipschitz_of_response (u := u) (beta := beta) (bm := bm) (bp := bp)
    hstep hb hbu hbm hu0 hCm hR hD hL hm hr0 hrnn hrec hs K
  have hq0 : (0:ℝ) ≤ (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) :=
    le_trans (Finset.sum_nonneg fun j _ => hLnn j) hq
  exact tuned_bare_coupling_window (bet := bet) (L := L)
    (q := (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0))
    hLip hq hq0 hgate hZl hZu hbmnn hwin

/-- **The gate is not an extra hypothesis at the canonical bare coupling.**  On
a trajectory started at the canonical value `u₀ = b₊ + 2(C_m+2RD)/b₋ + 1`, the
response gate of §3 holds automatically, so the tuned bare coupling exists with
no smallness hypothesis beyond finiteness of the four constants. -/
theorem tuned_bare_coupling_canonical {bet : ℕ → ℝ → ℝ} {L m r s : ℕ → ℝ}
    {Cm R D target : ℝ} {K : ℕ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hbp : 0 ≤ bp)
    (hCm : 0 ≤ Cm) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hstart : u 0 = bp + 2 * (Cm + 2 * R * D) / bm + 1)
    (hLip : ∀ j v w, |bet j v - bet j w| ≤ L j * |v - w|)
    (hLnn : ∀ j, 0 ≤ L j)
    (hL : ∀ j, L j ≤ m j + r j) (hm : ∀ j, m j ≤ Cm * couplingSq u j ^ 2)
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2)
    (hs : ∀ j, s j ≤ D * couplingSq u j ^ 2)
    (hZl : ∀ j v, bm ≤ bet j v) (hZu : ∀ j v, bet j v ≤ bp)
    (hwin : 0 < target - bp * K) :
    ∃ v : ℝ, (shootingTrajectory bet v K = target)
      ∧ (∀ j ≤ K, target - bp * K ≤ shootingTrajectory bet v j)
      ∧ (∀ j ≤ K, 0 < couplingSq (shootingTrajectory bet v) j
            ∧ couplingSq (shootingTrajectory bet v) j ≤ (target - bp * K)⁻¹)
      ∧ couplingSq (shootingTrajectory bet v) K = target⁻¹ := by
  have hA : 0 ≤ Cm + 2 * R * D := by positivity
  obtain ⟨hu₀pos, hgate⟩ := canonical_bare_coupling_gate (Cm := Cm) (R := R) (D := D)
    (bm := bm) (bp := bp) hbm hbp hA
  rw [← hstart] at hu₀pos hgate
  refine tuned_bare_coupling_of_response (u := u) (beta := beta) (bm := bm) (bp := bp)
    hstep hb hbu hbm hu₀pos hCm hR hD hLip hLnn hL hm hr0 hrnn hrec hs ?_ hZl hZu hbm.le hwin
  simpa [responseGate, couplingSq] using hgate

/-! ## 5. The Row-A completion predicate from response data -/

/-- **Row-A completion, with the cumulative sensitivity derived rather than
assumed.**  The `q < 1` input of `rowA_completion_of_uniform_debt` is replaced
by the one-step response recurrence, the quartic injection budget and the
marginal shell sensitivity, all measured on a trajectory with a uniformly
positive shell coefficient. -/
theorem rowA_completion_of_response_kernel
    {bet betaZ betaInt : ℕ → ℝ → ℝ} {L m r s : ℕ → ℝ}
    {Cm R D target bZm bZp eps : ℝ} {K : ℕ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hb : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 < bm) (hu0 : 0 < u 0)
    (hCm : 0 ≤ Cm) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hdec : ∀ j v, bet j v = betaZ j v + betaInt j v)
    (hZl : ∀ j v, bZm ≤ betaZ j v) (hZu : ∀ j v, betaZ j v ≤ bZp)
    (hIntEps : ∀ j v, |betaInt j v| ≤ eps)
    (hLip : ∀ j v w, |bet j v - bet j w| ≤ L j * |v - w|) (hLnn : ∀ j, 0 ≤ L j)
    (hL : ∀ j, L j ≤ m j + r j) (hm : ∀ j, m j ≤ Cm * couplingSq u j ^ 2)
    (hr0 : r 0 = 0) (hrnn : ∀ j, 0 ≤ r j)
    (hrec : ∀ j, r (j + 1) ≤ R * s j + r j / 2)
    (hs : ∀ j, s j ≤ D * couplingSq u j ^ 2)
    (hgate : (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) < 1)
    (hwin : 0 < target - (bZp + eps) * K) (hepsm : eps < bZm) :
    RowACompletion bet K target (bZm - eps) (bZp + eps)
      (target - (bZp + eps) * K)⁻¹ := by
  have hq := cumulative_lipschitz_of_response (u := u) (beta := beta) (bm := bm) (bp := bp)
    hstep hb hbu hbm hu0 hCm hR hD hL hm hr0 hrnn hrec hs K
  have hq0 : (0:ℝ) ≤ (Cm + 2 * R * D) * (((u 0 + bp) / u 0) * bm⁻¹ * couplingSq u 0) :=
    le_trans (Finset.sum_nonneg fun j _ => hLnn j) hq
  exact rowA_completion_of_uniform_debt hdec hZl hZu hIntEps hLip hq hq0 hgate hwin hepsm

end YangMills
