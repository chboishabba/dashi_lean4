/-
# The expenditure ledger, the geometric tail, and the residence charge

Three pieces of *bookkeeping* machinery that the Navier–Stokes lane needs once
the analytic estimates are in place.  Each is stated here as an unconditional
theorem over the reals, so that the analytic producers can be plugged in
directly without re-deriving the algebra.

## 1. The expenditure split

The post-Caccioppoli algebra: the total escape expenditure splits as

  `E_total = E_coercive + E_absorbed`,

and if the replenishment of the potential is paid for by the absorbed
dissipation together with a fixed remainder, then the *coercive* part of the
expenditure — the part that must be paid by the mechanism itself — is bounded by
the initial potential plus that remainder:

  `E_coercive ≤ Φ(0) + E_remainder`.                     (`coercive_expenditure_le`)

Any sub-expenditure (a weighted shell, or the vorticity part) inherits the same
bound (`shell_expenditure_le`).

## 2. The geometric tail

A residual carrying a strictly positive scaling dimension produces, after
dyadic assembly, a tail of the form `ε(R) = C·2^{−αR}`.  The theorems here are
the two consequences that are actually used: the tail is summable over the
dyadic shells beyond any given one, with the sum again geometric
(`geoTail_tsum_eq`, `geoTail_tsum_le`), and it can therefore be made smaller
than *any* prescribed absorption budget by choosing the base scale
(`exists_scale_geoTail_tsum_le`).  This is the quantitative content of
"positive-dimension residual ⇒ arbitrarily small absorbable budget".

## 3. The residence charge

The finite-occupation mechanism: rather than controlling every bad cell
separately, one charges the *total* bad residence to the finite dissipation.
If on each cell of a finite disjoint family the supercritical amplitude obeys
`λA² ≤ C_B·D`, then

  `∑ Δt·λA² ≤ C_B·∑ Δt·D`,                              (`residence_charge_sum`)

and consequently, if every cell of the family is bad in the sense `A ≥ A₀ > 0`,
the total residence time is finite and explicitly bounded:

  `∑ Δt ≤ C_B·D_total/(λA₀²)`.                     (`residence_time_le_of_charge`)

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ClayPeriodic

open scoped BigOperators
open Filter

noncomputable section

namespace ClayNS

/-! ## 1. The expenditure split -/

/-- **The coercive expenditure bound.**  With the escape expenditure split into
its coercive and absorbed parts, a potential balance `Φ(T) + E_total ≤ Φ(0) +
E_replenish`, a nonnegative terminal potential, and a replenishment paid by the
absorbed dissipation plus a remainder, the coercive expenditure obeys
`E_coercive ≤ Φ(0) + E_remainder`. -/
theorem coercive_expenditure_le
    {Phi0 PhiT Etotal Ecoercive Eabsorbed Ereplenish Eremainder : ℝ}
    (hsplit : Etotal = Ecoercive + Eabsorbed)
    (hPhiT : 0 ≤ PhiT)
    (hbalance : PhiT + Etotal ≤ Phi0 + Ereplenish)
    (hpay : Ereplenish ≤ Eabsorbed + Eremainder) :
    Ecoercive ≤ Phi0 + Eremainder := by
  linarith [hsplit, hPhiT, hbalance, hpay]

/-- **Sub-expenditures inherit the bound.**  A weighted-shell expenditure, or the
vorticity expenditure, bounded by the coercive expenditure, obeys the same
`Φ(0) + E_remainder` bound. -/
theorem shell_expenditure_le
    {Phi0 PhiT Etotal Ecoercive Eabsorbed Ereplenish Eremainder Eshell : ℝ}
    (hsplit : Etotal = Ecoercive + Eabsorbed)
    (hPhiT : 0 ≤ PhiT)
    (hbalance : PhiT + Etotal ≤ Phi0 + Ereplenish)
    (hpay : Ereplenish ≤ Eabsorbed + Eremainder)
    (hshell : Eshell ≤ Ecoercive) :
    Eshell ≤ Phi0 + Eremainder :=
  hshell.trans (coercive_expenditure_le hsplit hPhiT hbalance hpay)

/-! ## 2. The geometric tail -/

/-- The dyadic tail `ε(R) = C·2^{−αR}` produced by a residual of positive
scaling dimension `α`. -/
def geoTail (C alpha R : ℝ) : ℝ := C * (2 : ℝ) ^ (-(alpha * R))

lemma geoTail_nonneg {C : ℝ} (hC : 0 ≤ C) (alpha R : ℝ) : 0 ≤ geoTail C alpha R :=
  mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)

/-- The tail is decreasing in the base scale. -/
lemma geoTail_antitone {C alpha : ℝ} (hC : 0 ≤ C) (halpha : 0 ≤ alpha) {R R' : ℝ}
    (h : R ≤ R') : geoTail C alpha R' ≤ geoTail C alpha R := by
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  nlinarith [mul_le_mul_of_nonneg_left h halpha]

/-- The shell decomposition of the tail: `ε(R+n) = ε(R)·q^n` with `q = 2^{−α}`. -/
lemma geoTail_shift (C alpha R : ℝ) (n : ℕ) :
    geoTail C alpha (R + n) = geoTail C alpha R * ((2 : ℝ) ^ (-alpha)) ^ n := by
  unfold geoTail
  rw [mul_assoc, ← Real.rpow_natCast ((2 : ℝ) ^ (-alpha)) n, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  ring_nf

lemma two_rpow_neg_lt_one {alpha : ℝ} (halpha : 0 < alpha) : (2 : ℝ) ^ (-alpha) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma two_rpow_neg_pos (alpha : ℝ) : 0 < (2 : ℝ) ^ (-alpha) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- **The assembled tail is again geometric.**  Summing the tail over all dyadic
shells beyond `R` gives `ε(R)/(1 − 2^{−α})`. -/
theorem geoTail_tsum_eq {C alpha : ℝ} (halpha : 0 < alpha) (R : ℝ) :
    (∑' n : ℕ, geoTail C alpha (R + n)) = geoTail C alpha R / (1 - (2 : ℝ) ^ (-alpha)) := by
  have hq1 : (2 : ℝ) ^ (-alpha) < 1 := two_rpow_neg_lt_one halpha
  have hq0 : 0 < (2 : ℝ) ^ (-alpha) := two_rpow_neg_pos alpha
  have hgeom : (∑' n : ℕ, ((2 : ℝ) ^ (-alpha)) ^ n) = (1 - (2 : ℝ) ^ (-alpha))⁻¹ :=
    tsum_geometric_of_lt_one hq0.le hq1
  calc (∑' n : ℕ, geoTail C alpha (R + n))
      = ∑' n : ℕ, geoTail C alpha R * ((2 : ℝ) ^ (-alpha)) ^ n := by
        exact tsum_congr fun n => geoTail_shift C alpha R n
    _ = geoTail C alpha R * (1 - (2 : ℝ) ^ (-alpha))⁻¹ := by
        rw [tsum_mul_left, hgeom]
    _ = geoTail C alpha R / (1 - (2 : ℝ) ^ (-alpha)) := by rw [div_eq_mul_inv]

/-- The assembled tail tends to zero as the base scale grows. -/
theorem geoTail_tendsto_zero {C alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun R : ℝ => geoTail C alpha R) atTop (nhds 0) := by
  have hlog : (0:ℝ) < alpha * Real.log 2 := by
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h1 : Tendsto (fun R : ℝ => alpha * Real.log 2 * R) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hlog tendsto_id
  have h2 : Tendsto (fun R : ℝ => -(alpha * Real.log 2 * R)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h3 : Tendsto (fun R : ℝ => Real.exp (-(alpha * Real.log 2 * R))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h2
  have hrw : ∀ R : ℝ, geoTail C alpha R = C * Real.exp (-(alpha * Real.log 2 * R)) := by
    intro R
    rw [geoTail, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 2
    ring
  simpa [hrw] using h3.const_mul C

/-- **Positive-dimension residual ⇒ arbitrarily small absorbable budget.**  For
any prescribed budget `b > 0` there is a base scale beyond which the *entire*
assembled dyadic tail is smaller than `b`. -/
theorem exists_scale_geoTail_tsum_le {C alpha b : ℝ} (halpha : 0 < alpha)
    (hb : 0 < b) :
    ∃ R : ℝ, (∑' n : ℕ, geoTail C alpha (R + n)) ≤ b := by
  have hq1 : (2 : ℝ) ^ (-alpha) < 1 := two_rpow_neg_lt_one halpha
  have hden : 0 < 1 - (2 : ℝ) ^ (-alpha) := by linarith
  have htend := geoTail_tendsto_zero (C := C) (alpha := alpha) halpha
  have hgoal : ∀ᶠ R : ℝ in atTop, geoTail C alpha R < b * (1 - (2 : ℝ) ^ (-alpha)) := by
    have hpos : 0 < b * (1 - (2 : ℝ) ^ (-alpha)) := by positivity
    have := htend.eventually (eventually_lt_nhds hpos)
    exact this
  obtain ⟨R, hR⟩ := hgoal.exists
  refine ⟨R, ?_⟩
  rw [geoTail_tsum_eq halpha R, div_le_iff₀ hden]
  linarith

/-! ## 3. The residence charge -/

/-- **The residence charge.**  If on every cell of a finite family the
supercritical amplitude is charged to the local dissipation, `λA² ≤ C_B·D`, then
the total weighted residence is charged to the total dissipation. -/
theorem residence_charge_sum {ι : Type*} (s : Finset ι) {dt A D : ι → ℝ} {lam CB : ℝ}
    (hdt : ∀ i ∈ s, 0 ≤ dt i)
    (hcell : ∀ i ∈ s, lam * (A i) ^ 2 ≤ CB * D i) :
    ∑ i ∈ s, dt i * (lam * (A i) ^ 2) ≤ CB * ∑ i ∈ s, dt i * D i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have := mul_le_mul_of_nonneg_left (hcell i hi) (hdt i hi)
  calc dt i * (lam * (A i) ^ 2) ≤ dt i * (CB * D i) := this
    _ = CB * (dt i * D i) := by ring

/-- **Finite occupation.**  If in addition every cell of the family is *bad*,
`A ≥ A₀ > 0`, and the total dissipation over the family is at most `D_total`,
then the total residence time of the bad set is finite and bounded by
`C_B·D_total/(λA₀²)`: the bad epochs cannot occupy more than that. -/
theorem residence_time_le_of_charge {ι : Type*} (s : Finset ι) {dt A D : ι → ℝ}
    {lam CB A0 Dtot : ℝ}
    (hdt : ∀ i ∈ s, 0 ≤ dt i)
    (hcell : ∀ i ∈ s, lam * (A i) ^ 2 ≤ CB * D i)
    (hbad : ∀ i ∈ s, A0 ≤ A i) (hA0 : 0 < A0) (hlam : 0 < lam)
    (hDtot : ∑ i ∈ s, dt i * D i ≤ Dtot) (hCB : 0 ≤ CB) :
    ∑ i ∈ s, dt i ≤ CB * Dtot / (lam * A0 ^ 2) := by
  have hlow : (lam * A0 ^ 2) * ∑ i ∈ s, dt i ≤ ∑ i ∈ s, dt i * (lam * (A i) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hsq : A0 ^ 2 ≤ (A i) ^ 2 := by nlinarith [hbad i hi, hA0]
    have : lam * A0 ^ 2 ≤ lam * (A i) ^ 2 := by nlinarith
    calc lam * A0 ^ 2 * dt i ≤ lam * (A i) ^ 2 * dt i :=
          mul_le_mul_of_nonneg_right this (hdt i hi)
      _ = dt i * (lam * (A i) ^ 2) := by ring
  have hcharge := residence_charge_sum s hdt hcell
  have hfinal : (lam * A0 ^ 2) * ∑ i ∈ s, dt i ≤ CB * Dtot := by
    have : CB * ∑ i ∈ s, dt i * D i ≤ CB * Dtot := mul_le_mul_of_nonneg_left hDtot hCB
    linarith [hlow, hcharge]
  have hpos : 0 < lam * A0 ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  linarith [hfinal]

end ClayNS
