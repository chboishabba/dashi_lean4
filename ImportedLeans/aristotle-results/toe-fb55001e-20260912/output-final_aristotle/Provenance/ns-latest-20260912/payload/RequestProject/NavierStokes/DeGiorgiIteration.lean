/-
# The De Giorgi iteration lemma, and the hole-filling iteration lemma

These are the two purely quantitative engines behind `C_localDG`, the proposed
local oscillation improvement for the increment energy density
`q = ½|δ_h u|²` (`IncrementLocalEnergy.lean`).  Neither is specific to
Navier–Stokes: they are the abstract statements that a level-set energy
inequality and a Caccioppoli inequality are fed into.

## What is proved here

* `ClayNS.deGiorgi_fast_convergence` — the **fast geometric convergence
  lemma**: a nonnegative sequence with the superlinear recursion
  `Y_{n+1} ≤ C·b^n·Y_n^{1+α}`   (`C > 0`, `b > 1`, `α > 0`)
  and small initial value `Y₀ ≤ C^{-1/α} b^{-1/α²}` satisfies
  `Y_n ≤ Y₀·b^{-n/α}`, hence `Y_n → 0` (`ClayNS.deGiorgi_tendsto_zero`).
  This is exactly the step that converts a level-set energy inequality into
  local boundedness / oscillation decay.
* `ClayNS.holeFilling_iteration` — the **Giaquinta–Giusti iteration lemma**:
  if a nonnegative bounded function of the radius satisfies
  `Φ(r) ≤ θ·Φ(R) + A/(R−r)^β + B`  for all `ρ ≤ r < R ≤ ρ₀`, with `θ < 1`,
  then the bad term can be absorbed:
  `Φ(ρ) ≤ c(θ,β)·(A/(ρ₀−ρ)^β + B)`.
  This is the mechanism by which a Caccioppoli inequality whose right-hand side
  still contains the quantity being estimated (the "hole") is closed.

Both are stated in the exact form the increment programme needs, and both are
proved from scratch.

No `sorry`, no postulates.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace ClayNS

/-! ## De Giorgi's fast geometric convergence lemma -/

/-- **Fast geometric convergence.**  If `Y ≥ 0` satisfies the superlinear
recursion `Y_{n+1} ≤ C·b^n·Y_n^{1+α}` with `C > 0`, `b > 1`, `α > 0`, and the
initial value obeys the smallness threshold `Y₀ ≤ C^{-1/α}·b^{-1/α²}`, then
`Y_n ≤ Y₀·b^{-n/α}` for every `n`. -/
theorem deGiorgi_fast_convergence {Y : ℕ → ℝ} {C b alpha : ℝ}
    (hC : 0 < C) (hb : 1 < b) (halpha : 0 < alpha)
    (hnn : ∀ n, 0 ≤ Y n)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ (n : ℝ) * Y n ^ (1 + alpha))
    (hY0 : Y 0 ≤ C ^ (-1 / alpha) * b ^ (-1 / alpha ^ 2)) :
    ∀ n, Y n ≤ Y 0 * b ^ (-(n : ℝ) / alpha) := by
  have hb0 : (0:ℝ) < b := lt_trans one_pos hb
  -- the smallness threshold in multiplicative form: `C·Y₀^α·b^{1/α} ≤ 1`
  have hkey : C * Y 0 ^ alpha * b ^ (1 / alpha) ≤ 1 := by
    have hpow : Y 0 ^ alpha ≤ (C ^ (-1 / alpha) * b ^ (-1 / alpha ^ 2)) ^ alpha :=
      Real.rpow_le_rpow (hnn 0) hY0 halpha.le
    have hsplit : (C ^ (-1 / alpha) * b ^ (-1 / alpha ^ 2)) ^ alpha
        = C⁻¹ * b ^ (-1 / alpha) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hb0.le _),
        ← Real.rpow_mul hC.le, ← Real.rpow_mul hb0.le]
      have h1 : -1 / alpha * alpha = -1 := by field_simp
      have h2 : -1 / alpha ^ 2 * alpha = -1 / alpha := by
        field_simp
      rw [h1, h2, Real.rpow_neg_one]
    rw [hsplit] at hpow
    have hbinv : b ^ (-1 / alpha) * b ^ (1 / alpha) = 1 := by
      rw [← Real.rpow_add hb0, show -1 / alpha + 1 / alpha = 0 by ring, Real.rpow_zero]
    have hbpos : (0:ℝ) < b ^ (1 / alpha) := Real.rpow_pos_of_pos hb0 _
    calc C * Y 0 ^ alpha * b ^ (1 / alpha)
        ≤ C * (C⁻¹ * b ^ (-1 / alpha)) * b ^ (1 / alpha) := by
          have := mul_le_mul_of_nonneg_left hpow hC.le
          exact mul_le_mul_of_nonneg_right this hbpos.le
      _ = (b ^ (-1 / alpha) * b ^ (1 / alpha)) := by field_simp
      _ = 1 := hbinv
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hbn : (0:ℝ) < b ^ (-(n : ℝ) / alpha) := Real.rpow_pos_of_pos hb0 _
      have hstep1 : Y (n + 1) ≤ C * b ^ (n : ℝ) * (Y 0 * b ^ (-(n : ℝ) / alpha)) ^ (1 + alpha) := by
        refine le_trans (hrec n) ?_
        have hmono : Y n ^ (1 + alpha) ≤ (Y 0 * b ^ (-(n : ℝ) / alpha)) ^ (1 + alpha) :=
          Real.rpow_le_rpow (hnn n) ih (by linarith)
        have hcoef : (0:ℝ) ≤ C * b ^ (n : ℝ) :=
          mul_nonneg hC.le (Real.rpow_pos_of_pos hb0 _).le
        exact mul_le_mul_of_nonneg_left hmono hcoef
      have hexpand : (Y 0 * b ^ (-(n : ℝ) / alpha)) ^ (1 + alpha)
          = Y 0 ^ (1 + alpha) * b ^ (-(n : ℝ) * (1 + alpha) / alpha) := by
        rw [Real.mul_rpow (hnn 0) hbn.le, ← Real.rpow_mul hb0.le]
        congr 1
        field_simp
      have hY0split : Y 0 ^ (1 + alpha) = Y 0 * Y 0 ^ alpha := by
        rw [Real.rpow_add' (hnn 0) (by positivity), Real.rpow_one]
      have hstep2 : C * b ^ (n : ℝ) * (Y 0 ^ (1 + alpha) * b ^ (-(n : ℝ) * (1 + alpha) / alpha))
          = (C * Y 0 ^ alpha * b ^ (1 / alpha)) * (Y 0 * b ^ (-((n : ℝ) + 1) / alpha)) := by
        rw [hY0split]
        have hb1 : b ^ (n : ℝ) * b ^ (-(n : ℝ) * (1 + alpha) / alpha)
            = b ^ (1 / alpha) * b ^ (-((n : ℝ) + 1) / alpha) := by
          rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
          congr 1
          field_simp
          ring
        calc C * b ^ (n : ℝ) * (Y 0 * Y 0 ^ alpha * b ^ (-(n : ℝ) * (1 + alpha) / alpha))
            = (C * Y 0 ^ alpha) * (b ^ (n : ℝ) * b ^ (-(n : ℝ) * (1 + alpha) / alpha)) * Y 0 := by
              ring
          _ = (C * Y 0 ^ alpha) * (b ^ (1 / alpha) * b ^ (-((n : ℝ) + 1) / alpha)) * Y 0 := by
              rw [hb1]
          _ = (C * Y 0 ^ alpha * b ^ (1 / alpha)) * (Y 0 * b ^ (-((n : ℝ) + 1) / alpha)) := by
              ring
      have hfinal : Y (n + 1) ≤ (C * Y 0 ^ alpha * b ^ (1 / alpha))
          * (Y 0 * b ^ (-((n : ℝ) + 1) / alpha)) := by
        rw [← hstep2, ← hexpand]
        exact hstep1
      have hpos : (0:ℝ) ≤ Y 0 * b ^ (-((n : ℝ) + 1) / alpha) :=
        mul_nonneg (hnn 0) (Real.rpow_pos_of_pos hb0 _).le
      have := mul_le_mul_of_nonneg_right hkey hpos
      have hcast : (((n : ℝ) + 1)) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [one_mul] at this
      calc Y (n + 1) ≤ (C * Y 0 ^ alpha * b ^ (1 / alpha))
              * (Y 0 * b ^ (-((n : ℝ) + 1) / alpha)) := hfinal
        _ ≤ Y 0 * b ^ (-((n : ℝ) + 1) / alpha) := this
        _ = Y 0 * b ^ (-((n + 1 : ℕ) : ℝ) / alpha) := by rw [hcast]

/-- The conclusion of the De Giorgi iteration: the level-set quantity vanishes
in the limit. -/
theorem deGiorgi_tendsto_zero {Y : ℕ → ℝ} {C b alpha : ℝ}
    (hC : 0 < C) (hb : 1 < b) (halpha : 0 < alpha)
    (hnn : ∀ n, 0 ≤ Y n)
    (hrec : ∀ n, Y (n + 1) ≤ C * b ^ (n : ℝ) * Y n ^ (1 + alpha))
    (hY0 : Y 0 ≤ C ^ (-1 / alpha) * b ^ (-1 / alpha ^ 2)) :
    Tendsto Y atTop (𝓝 0) := by
  have hb0 : (0:ℝ) < b := lt_trans one_pos hb
  have hbound := deGiorgi_fast_convergence hC hb halpha hnn hrec hY0
  have hmaj : Tendsto (fun n : ℕ => Y 0 * b ^ (-(n : ℝ) / alpha)) atTop (𝓝 0) := by
    have hq : Tendsto (fun n : ℕ => (b ^ (-1 / alpha)) ^ n) atTop (𝓝 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_pos_of_pos hb0 _).le ?_
      exact Real.rpow_lt_one_of_one_lt_of_neg hb
        (div_neg_of_neg_of_pos (by norm_num) halpha)
    have hcongr : ∀ n : ℕ, (b ^ (-1 / alpha)) ^ n = b ^ (-(n : ℝ) / alpha) := by
      intro n
      rw [← Real.rpow_natCast (b ^ (-1 / alpha)) n, ← Real.rpow_mul hb0.le]
      congr 1
      field_simp
    have := hq.const_mul (Y 0)
    simpa [hcongr] using this
  refine squeeze_zero hnn hbound ?_
  simpa using hmaj

/-! ## The hole-filling / absorption iteration lemma -/

/-- The partial sums of a geometric series with ratio in `[0,1)` are bounded by
`(1−q)⁻¹`. -/
lemma geomSum_le_inv_one_sub (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, q ^ i ≤ (1 - q)⁻¹ := by
  have h := geom_sum_eq (by linarith : q ≠ 1) k
  have hqk : (0:ℝ) ≤ q ^ k := pow_nonneg h0 k
  have hne : (1:ℝ) - q ≠ 0 := by linarith
  rw [h, div_le_iff_of_neg (by linarith : q - 1 < 0)]
  have hid : (1 - q)⁻¹ * (q - 1) = -1 := by
    rw [inv_mul_eq_div, div_eq_iff hne]; ring
  rw [hid]
  linarith


/-- **Giaquinta–Giusti iteration lemma** (the absorption/hole-filling engine).
Let `Φ` be bounded above by `Mb` on `[ρ, ρ₀]` and satisfy, for all
`ρ ≤ r < R ≤ ρ₀`,

`Φ(r) ≤ θ·Φ(R) + A/(R−r)^β + B`,

where the "hole" `θ·Φ(R)` still contains the quantity being estimated.  If some
geometric ratio `λ ∈ (0,1)` makes `q = θ·λ^{-β} < 1`, then the hole can be
absorbed and

`Φ(ρ) ≤ A/(((1−λ)(ρ₀−ρ))^β·(1−q)) + B/(1−θ)`,

with no dependence on `Mb`.  This is what turns a Caccioppoli inequality with a
bad right-hand side into a genuine estimate. -/
theorem holeFilling_iteration {Phi : ℝ → ℝ} {rho rho0 theta A B beta lam Mb : ℝ}
    (hrho : rho < rho0) (hth0 : 0 ≤ theta) (hbeta : 0 ≤ beta)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hq : theta * lam ^ (-beta) < 1)
    (hMb : ∀ r ∈ Set.Icc rho rho0, Phi r ≤ Mb)
    (hineq : ∀ r R, rho ≤ r → r < R → R ≤ rho0 →
      Phi r ≤ theta * Phi R + A / (R - r) ^ beta + B) :
    Phi rho ≤ A / (((1 - lam) * (rho0 - rho)) ^ beta * (1 - theta * lam ^ (-beta)))
              + B / (1 - theta) := by
  have hgap : 0 < rho0 - rho := by linarith
  set mu : ℝ := lam ^ beta with hmu
  have hmu0 : 0 < mu := Real.rpow_pos_of_pos hlam0 beta
  have hmu1 : mu ≤ 1 := Real.rpow_le_one hlam0.le hlam1.le hbeta
  have hqmu : theta * lam ^ (-beta) = theta / mu := by
    rw [hmu, Real.rpow_neg hlam0.le, div_eq_mul_inv]
  have hq1' : theta / mu < 1 := by rw [← hqmu]; exact hq
  have hq0' : 0 ≤ theta / mu := div_nonneg hth0 hmu0.le
  have hth1 : theta < 1 := by
    have hle : theta ≤ theta / mu := by
      rw [le_div_iff₀ hmu0]
      nlinarith
    linarith
  set q : ℝ := theta / mu with hqdef
  have hq1 : q < 1 := hq1'
  have hq0 : 0 ≤ q := hq0'
  set C0 : ℝ := ((1 - lam) * (rho0 - rho)) ^ beta with hC0
  have hC0pos : 0 < C0 := Real.rpow_pos_of_pos (mul_pos (by linarith) hgap) beta
  -- the geometric sequence of radii
  set rad : ℕ → ℝ := fun i => rho + (1 - lam ^ i) * (rho0 - rho) with hrad
  have hradval : ∀ i : ℕ, rad i = rho + (1 - lam ^ i) * (rho0 - rho) := fun _ => rfl
  have hlampow : ∀ i : ℕ, 0 < lam ^ i := fun i => pow_pos hlam0 i
  have hlampow1 : ∀ i : ℕ, lam ^ i ≤ 1 := fun i => pow_le_one₀ hlam0.le hlam1.le
  have hrad0 : rad 0 = rho := by rw [hradval 0]; simp
  have hradge : ∀ i, rho ≤ rad i := by
    intro i
    have h1 := hlampow1 i
    have h2 : 0 ≤ (1 - lam ^ i) * (rho0 - rho) := by nlinarith [hlampow i]
    rw [hradval i]
    linarith
  have hradle : ∀ i, rad i ≤ rho0 := by
    intro i
    have h1 : 0 < lam ^ i := hlampow i
    rw [hradval i]
    nlinarith
  have hraddiff : ∀ i, rad (i + 1) - rad i = lam ^ i * ((1 - lam) * (rho0 - rho)) := by
    intro i
    rw [hradval i, hradval (i + 1), pow_succ]
    ring
  have hradlt : ∀ i, rad i < rad (i + 1) := by
    intro i
    have h1 : 0 < lam ^ i * ((1 - lam) * (rho0 - rho)) :=
      mul_pos (hlampow i) (mul_pos (by linarith) hgap)
    have := hraddiff i
    linarith
  -- the per-step term, computed exactly
  have hterm : ∀ i : ℕ, theta ^ i * (A / (rad (i + 1) - rad i) ^ beta + B)
      = (A / C0) * q ^ i + B * theta ^ i := by
    intro i
    have hpos : (0:ℝ) < lam ^ i * ((1 - lam) * (rho0 - rho)) :=
      mul_pos (hlampow i) (mul_pos (by linarith) hgap)
    have hsplit : (rad (i + 1) - rad i) ^ beta = mu ^ i * C0 := by
      rw [hraddiff i, Real.mul_rpow (hlampow i).le
        (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hgap.le)]
      congr 1
      rw [hmu, ← Real.rpow_natCast lam i, ← Real.rpow_mul hlam0.le,
        ← Real.rpow_natCast (lam ^ beta) i, ← Real.rpow_mul hlam0.le]
      ring_nf
    have hmui : (0:ℝ) < mu ^ i := pow_pos hmu0 i
    have hqi : q ^ i = theta ^ i / mu ^ i := by
      rw [hqdef, div_pow]
    rw [hsplit, hqi]
    field_simp
  -- the iteration
  have hiter : ∀ k : ℕ, Phi rho ≤ theta ^ k * Phi (rad k)
      + ∑ i ∈ Finset.range k, theta ^ i * (A / (rad (i + 1) - rad i) ^ beta + B) := by
    intro k
    induction k with
    | zero => simp [hrad0]
    | succ k ih =>
        have hstep := hineq (rad k) (rad (k + 1)) (hradge k) (hradlt k) (hradle (k + 1))
        have hthk : (0:ℝ) ≤ theta ^ k := pow_nonneg hth0 k
        have hmul := mul_le_mul_of_nonneg_left hstep hthk
        rw [Finset.sum_range_succ]
        have : theta ^ k * Phi (rad k) ≤ theta ^ (k + 1) * Phi (rad (k + 1))
            + theta ^ k * (A / (rad (k + 1) - rad k) ^ beta + B) := by
          calc theta ^ k * Phi (rad k)
              ≤ theta ^ k * (theta * Phi (rad (k + 1))
                  + A / (rad (k + 1) - rad k) ^ beta + B) := hmul
            _ = theta ^ (k + 1) * Phi (rad (k + 1))
                  + theta ^ k * (A / (rad (k + 1) - rad k) ^ beta + B) := by ring
        linarith
  -- summing the geometric series
  have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range k, theta ^ i * (A / (rad (i + 1) - rad i) ^ beta + B)
      ≤ A / (C0 * (1 - q)) + B / (1 - theta) := by
    intro k
    have hrw : ∑ i ∈ Finset.range k, theta ^ i * (A / (rad (i + 1) - rad i) ^ beta + B)
        = (A / C0) * ∑ i ∈ Finset.range k, q ^ i + B * ∑ i ∈ Finset.range k, theta ^ i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hterm i
    have h1 : (A / C0) * ∑ i ∈ Finset.range k, q ^ i ≤ (A / C0) * (1 - q)⁻¹ :=
      mul_le_mul_of_nonneg_left (geomSum_le_inv_one_sub q hq0 hq1 k) (div_nonneg hA hC0pos.le)
    have h2 : B * ∑ i ∈ Finset.range k, theta ^ i ≤ B * (1 - theta)⁻¹ :=
      mul_le_mul_of_nonneg_left (geomSum_le_inv_one_sub theta hth0 hth1 k) hB
    have e1 : A / (C0 * (1 - q)) = (A / C0) * (1 - q)⁻¹ := by
      field_simp
    have e2 : B / (1 - theta) = B * (1 - theta)⁻¹ := by
      rw [div_eq_mul_inv]
    rw [hrw, e1, e2]
    linarith
  -- passing to the limit: the `Mb` term disappears
  have hall : ∀ k : ℕ, Phi rho ≤ theta ^ k * Mb + (A / (C0 * (1 - q)) + B / (1 - theta)) := by
    intro k
    have hthk : (0:ℝ) ≤ theta ^ k := pow_nonneg hth0 k
    have hb : Phi (rad k) ≤ Mb := hMb (rad k) ⟨hradge k, hradle k⟩
    have h1 : theta ^ k * Phi (rad k) ≤ theta ^ k * Mb := mul_le_mul_of_nonneg_left hb hthk
    have h2 := hiter k
    have h3 := hsum k
    linarith
  have hlim : Filter.Tendsto
      (fun k : ℕ => theta ^ k * Mb + (A / (C0 * (1 - q)) + B / (1 - theta))) atTop
      (𝓝 (0 * Mb + (A / (C0 * (1 - q)) + B / (1 - theta)))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hth0 hth1).mul_const Mb).add_const _
  have hfin := ge_of_tendsto' hlim hall
  rw [hqmu]
  simpa using hfin

end ClayNS
