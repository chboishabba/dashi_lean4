/-
# `C_a`: absorption of the pressure pairing

`incr_pressure_localized_split` (`IncrementLocalizedLevelSet.lean`) shows that,
with the weight `W = Φ·β'(q)`, the pressure enters the localized level-set
inequality only through

`−δ_h p · (δ_h u · ∇W) = −δ_h p·(δ_h u·∇Φ)β'(q) − δ_h p·Φβ''(q)(δ_h u·∇q)`,

up to a divergence.  This file closes the quantitative half.

Three ingredients, all proved here or in the two preceding files:

* **gauge freedom** — `∫ δ_h u·∇W = 0` because the increment is divergence free,
  so the pressure may be replaced by `δ_h p − c` for *any* constant `c`;
* **`L²` control of the oscillation** — with `c` the cell mean,
  `∫|δ_h p − c|² ≤ 12A²∫|∇u|²` (`cellInt_incrPres_oscillation_le`); this is the
  elementary periodic substitute for the Calderón–Zygmund/John–Nirenberg step,
  and `L²` is exactly what the absorption consumes;
* **Young's inequality with the convexity weight** — the `β''(q)∇q` pairing is
  split as `ab ≤ ηνa² + (1/4ην)b²` with `a = |∇q|` weighted by `Φβ''(q)`, so the
  first half is absorbed by the dissipation `νΦβ''(q)|∇q|²` of the localized
  inequality and the second half is an `L²` pressure oscillation.

## What is proved here

* `ClayNS.cellInt_incrDrift_eq_zero` — the gauge identity.
* `ClayNS.cellInt_incr_pressure_pairing` — the integrated pressure split with an
  arbitrary constant subtracted from the pressure.
* `ClayNS.increment_pressure_absorption` — **`C_a`**:
  `|∫ Φβ'(q) δ_hu·∇δ_hp| ≤ ην ∫ Φβ''(q)|∇q|² + (D²B/4ην)·Osc + DGK·√Osc`,
  with `Osc = 12A²∫|∇u|²` the pressure oscillation budget, `D` a bound for
  `|δ_h u|`, `G` for `|∇Φ|`, `K` for `β'(q)` and `B` for `Φβ''(q)`.  The second
  and third terms are of the level-set/cutoff-energy type already used by the
  De Giorgi iteration: they involve only `∇Φ`, the cutoff and the velocity
  dissipation.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PressureL2Oscillation

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The cell has unit volume. -/
lemma cellInt_one : cellInt (fun _ : E3 => (1 : ℝ)) = 1 := by
  rw [cellInt, cell]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc_pi]
  simp

/-- The squared spatial gradient of the increment density `q = ½|δ_h u|²`. -/
def incrGradQsq (h : E3) (V : STime → E3) (z : STime) : ℝ :=
  ∑ a, (dvec (0, ee a) (incrQuad h V) z) ^ 2

lemma incrGradQsq_nonneg (h : E3) (V : STime → E3) (z : STime) : 0 ≤ incrGradQsq h V z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## The gauge identity -/

/-- **Gauge freedom.**  For any smooth periodic weight `W`, the cell integral of
`δ_h u·∇W` vanishes, because the increment is divergence free.  Consequently an
arbitrary constant may be subtracted from the pressure in the pairing below. -/
theorem cellInt_incrDrift_eq_zero {V : STime → E3} {W : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hVper : SpacePeriodic V) (hWper : SpacePeriodic W)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    cellInt (fun x => ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) = 0 := by
  have hincr : ContDiff ℝ (⊤ : ℕ∞) (incrVec h V) := contDiff_incrVec h hV
  have hflux : ContDiff ℝ (⊤ : ℕ∞) (fun w => W w • incrVec h V w) := hW.smul hincr
  have hfluxper : SpacePeriodic (fun w => W w • incrVec h V w) := by
    intro z j
    simp only [hWper z j, spacePeriodic_incrVec h hVper z j]
  have hid : ∀ z : STime,
      divg (fun w => W w • incrVec h V w) z
        = ∑ a, incrComp h V a z * dvec (0, ee a) W z := by
    intro z
    rw [divg_smul W (incrVec h V) hW hincr z, divg_incrVec h hV hdiv z, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun a _ => by rw [incrVec_coord]; ring
  have hzero := cellInt_divg_eq_zero (fun w => W w • incrVec h V w) hflux hfluxper t
  rwa [cellInt_congr (fun x => hid (t, x))] at hzero

/-- **The integrated pressure pairing, gauge fixed.**  For any smooth periodic
weight `W` and any constant `c`,
`∫ W (δ_h u·∇δ_h p) = −∫ (δ_h p − c)(δ_h u·∇W)`. -/
theorem cellInt_incr_pressure_pairing {V : STime → E3} {P W : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hWper : SpacePeriodic W)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) (c : ℝ) :
    cellInt (fun x => W (t, x)
        * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))
      = - cellInt (fun x => (incrPres h P (t, x) - c)
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
  classical
  have hincr : ContDiff ℝ (⊤ : ℕ∞) (incrVec h V) := contDiff_incrVec h hV
  have hdP : ContDiff ℝ (⊤ : ℕ∞) (incrPres h P) := contDiff_incrPres h hP
  -- continuity of the two densities
  have hcDrift : Continuous (fun x : E3 =>
      ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
    refine continuous_finset_sum _ fun a _ => ?_
    exact (((contDiff_incrComp h hV a).continuous).comp
        (continuous_const.prodMk continuous_id)).mul
      ((continuous_dvec W hW (0, ee a)).comp (continuous_const.prodMk continuous_id))
  have hcPres : Continuous (fun x : E3 => incrPres h P (t, x)) :=
    hdP.continuous.comp (continuous_const.prodMk continuous_id)
  -- the pointwise weighted split
  have hsplit := fun z => incr_pressure_weighted_divergence (P := P) (W := W) h hV hP hW hdiv z
  -- the divergence integrates to zero
  have hfluxper : SpacePeriodic (fun w => (W w * incrPres h P w) • incrVec h V w) := by
    intro z j
    simp only [hWper z j, spacePeriodic_incrPres h hPper z j,
      spacePeriodic_incrVec h hVper z j]
  have hdivzero := cellInt_divg_eq_zero (fun w => (W w * incrPres h P w) • incrVec h V w)
    ((hW.mul hdP).smul hincr) hfluxper t
  -- integrate the split
  have hcLHS : Continuous (fun x : E3 => W (t, x)
      * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))) := by
    refine (hW.continuous.comp (continuous_const.prodMk continuous_id)).mul ?_
    refine continuous_finset_sum _ fun a _ => ?_
    exact (((contDiff_incrComp h hV a).continuous).comp
        (continuous_const.prodMk continuous_id)).mul
      ((continuous_dvec _ hdP (0, ee a)).comp (continuous_const.prodMk continuous_id))
  have hcdivg : Continuous (fun x : E3 =>
      divg (fun w => (W w * incrPres h P w) • incrVec h V w) (t, x)) :=
    (continuous_divg ((hW.mul hdP).smul hincr)).comp
      (continuous_const.prodMk continuous_id)
  have hcprod : Continuous (fun x : E3 => incrPres h P (t, x)
      * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := hcPres.mul hcDrift
  have hint : cellInt (fun x => W (t, x)
        * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))
      = - cellInt (fun x => incrPres h P (t, x)
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
    rw [cellInt_congr (fun x => hsplit (t, x)), cellInt_sub hcdivg hcprod, hdivzero, zero_sub]
  -- subtract the constant, which costs nothing
  have hgauge := cellInt_incrDrift_eq_zero h hV hW hVper hWper hdiv t
  have hsub : cellInt (fun x => (incrPres h P (t, x) - c)
        * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
      = cellInt (fun x => incrPres h P (t, x)
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
    have hrw : ∀ x : E3, (incrPres h P (t, x) - c)
        * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
        = incrPres h P (t, x) * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
          - c * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
      intro x; ring
    rw [cellInt_congr hrw,
      cellInt_sub (f := fun x : E3 => incrPres h P (t, x)
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
        (g := fun x : E3 => c * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
        hcprod (continuous_const.mul hcDrift),
      cellInt_const_mul c (fun x => ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)),
      hgauge, mul_zero, sub_zero]
  rw [hint, hsub]

/-! ## The absorption estimate -/

/-- **`C_a`: the pressure pairing is absorbed.**  For a smooth periodic solution,
a nonnegative cutoff `Φ` and a smooth convex `β` with `β' = b₁`, `β'' = b₂ ≥ 0`,

`|∫ Φβ'(q)·(δ_hu·∇δ_hp)| ≤ ην∫Φβ''(q)|∇q|² + (D²B/4ην)·Osc + DGK·√Osc`,

where `D` bounds `|δ_hu|`, `G` bounds `|∇Φ|`, `K` bounds `|β'(q)|`, `B` bounds
`Φβ''(q)` and `Osc = 12A²∫|∇u|²` is the `L²` pressure-oscillation budget of
`cellInt_incrPres_oscillation_le`.  The first term is absorbed by the
dissipation of the localized level-set inequality; the remaining two are
cutoff/level-set energy terms. -/
theorem increment_pressure_absorption (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hb2c : Continuous b2)
    (hPhinn : ∀ z : STime, 0 ≤ Phi z) (hb2nn : ∀ x : ℝ, 0 ≤ b2 x)
    {A D G K B eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta)
    (hA : ∀ z : STime, ∑ i, (V z i) ^ 2 ≤ A ^ 2)
    (hD : ∀ z : STime, ∑ a, (incrComp h V a z) ^ 2 ≤ D ^ 2) (hD0 : 0 ≤ D)
    (hG : ∀ z : STime, ∑ a, (dvec (0, ee a) Phi z) ^ 2 ≤ G ^ 2) (hG0 : 0 ≤ G)
    (hK : ∀ z : STime, |b1 (incrQuad h V z)| ≤ K)
    (hB : ∀ z : STime, Phi z * b2 (incrQuad h V z) ≤ B) (t : ℝ) :
    |cellInt (fun x => (Phi (t, x) * b1 (incrQuad h V (t, x)))
        * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))|
      ≤ eta * nu * cellInt (fun x => (Phi (t, x) * b2 (incrQuad h V (t, x)))
            * incrGradQsq h V (t, x))
        + (D ^ 2 * B / (4 * eta * nu))
            * (12 * (A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x))))
        + D * G * K
            * Real.sqrt (12 * (A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x)))) := by
  classical
  set q : STime → ℝ := incrQuad h V with hqdef
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := contDiff_incrQuad h hV
  have hqper : SpacePeriodic q := spacePeriodic_incrQuad h hVper
  set W : STime → ℝ := fun z => Phi z * b1 (q z) with hWdef
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun z => b1 (q z)) := hb1c.comp hq
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hPhi.mul hb1q
  have hWper : SpacePeriodic W := by
    intro z j
    simp only [hWdef, hPhiper z j, hqper z j]
  -- the weight derivative
  have hWderiv : ∀ (a : Fin 3) (z : STime),
      dvec (0, ee a) W z
        = dvec (0, ee a) Phi z * b1 (q z) + Phi z * (b2 (q z) * dvec (0, ee a) q z) := by
    intro a z
    rw [hWdef, dvec_mul Phi (fun w => b1 (q w)) z ((differentiable_of_contDiffTop hPhi) z)
      (differentiableAt_comp_scalar hq hb2 z) (0, ee a),
      dvec_comp_scalar hq hb2 (0, ee a) z]
  -- the pressure oscillation
  set c : ℝ := cellInt (fun y => incrPres h P (t, y)) with hcdef
  set R : E3 → ℝ := fun x => incrPres h P (t, x) - c with hRdef
  set Osc : ℝ := 12 * (A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x))) with hOscdef
  have hOsc : cellInt (fun x => (R x) ^ 2) ≤ Osc :=
    cellInt_incrPres_oscillation_le nu V P hV hP hVper hPper hdiv hmom hA t h
  have hOscnn : 0 ≤ Osc := le_trans (cellInt_nonneg fun x => sq_nonneg _) hOsc
  have hcR : Continuous R :=
    ((contDiff_incrPres h hP).continuous.comp
      (continuous_const.prodMk continuous_id)).sub continuous_const
  -- the identity
  have hid := cellInt_incr_pressure_pairing (P := P) (W := W) h hV hP hW hVper hPper hWper hdiv t c
  -- pointwise bound for the integrand of the right-hand side
  have hDrift : ∀ x : E3,
      |R x * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)|
        ≤ (D * G * K) * |R x|
          + (Phi (t, x) * b2 (q (t, x)))
              * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|)) := by
    intro x
    have hsplit : (∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))
        = (∑ a, incrComp h V a (t, x) * (dvec (0, ee a) Phi (t, x) * b1 (q (t, x))))
          + (Phi (t, x) * b2 (q (t, x)))
              * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) q (t, x) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [hWderiv a (t, x)]; ring
    -- the cutoff pairing
    have hcs1 : |∑ a, incrComp h V a (t, x) * dvec (0, ee a) Phi (t, x)| ≤ D * G := by
      have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun a => incrComp h V a (t, x)) (fun a => dvec (0, ee a) Phi (t, x))
      have h1 := hD (t, x)
      have h2 := hG (t, x)
      have hbound : (∑ a, incrComp h V a (t, x) * dvec (0, ee a) Phi (t, x)) ^ 2
          ≤ (D * G) ^ 2 := by
        have hnn1 : (0:ℝ) ≤ ∑ a, (incrComp h V a (t, x)) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hnn2 : (0:ℝ) ≤ ∑ a, (dvec (0, ee a) Phi (t, x)) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        nlinarith [hsq, h1, h2, hnn1, hnn2, sq_nonneg D, sq_nonneg G]
      have hsqrt := Real.sqrt_le_sqrt hbound
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg hD0 hG0)] at hsqrt
    have hterm1 : |∑ a, incrComp h V a (t, x) * (dvec (0, ee a) Phi (t, x) * b1 (q (t, x)))|
        ≤ D * G * K := by
      have hfac : (∑ a, incrComp h V a (t, x) * (dvec (0, ee a) Phi (t, x) * b1 (q (t, x))))
          = (∑ a, incrComp h V a (t, x) * dvec (0, ee a) Phi (t, x)) * b1 (q (t, x)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hfac, abs_mul]
      have hKnn : 0 ≤ K := le_trans (abs_nonneg _) (hK (t, x))
      exact mul_le_mul hcs1 (hK (t, x)) (abs_nonneg _) (mul_nonneg hD0 hG0)
    -- the dissipation pairing
    have hcs2 : |∑ a, incrComp h V a (t, x) * dvec (0, ee a) q (t, x)|
        ≤ D * Real.sqrt (incrGradQsq h V (t, x)) := by
      have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun a => incrComp h V a (t, x)) (fun a => dvec (0, ee a) q (t, x))
      have hgq : ∑ a, (dvec (0, ee a) q (t, x)) ^ 2 = incrGradQsq h V (t, x) := rfl
      have hnn : (0:ℝ) ≤ incrGradQsq h V (t, x) := incrGradQsq_nonneg h V (t, x)
      have hbound : (∑ a, incrComp h V a (t, x) * dvec (0, ee a) q (t, x)) ^ 2
          ≤ (D * Real.sqrt (incrGradQsq h V (t, x))) ^ 2 := by
        have hs : (Real.sqrt (incrGradQsq h V (t, x))) ^ 2 = incrGradQsq h V (t, x) :=
          Real.sq_sqrt hnn
        have h1 := hD (t, x)
        rw [hgq] at hsq
        nlinarith [hsq, h1, hnn, hs, sq_nonneg D]
      have hsqrt := Real.sqrt_le_sqrt hbound
      rwa [Real.sqrt_sq_eq_abs,
        Real.sqrt_sq (mul_nonneg hD0 (Real.sqrt_nonneg _))] at hsqrt
    have hwnn : 0 ≤ Phi (t, x) * b2 (q (t, x)) := mul_nonneg (hPhinn _) (hb2nn _)
    calc |R x * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)|
        = |R x| * |∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)| := abs_mul _ _
      _ ≤ |R x| * (D * G * K
            + (Phi (t, x) * b2 (q (t, x))) * (D * Real.sqrt (incrGradQsq h V (t, x)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          have h2 : |(Phi (t, x) * b2 (q (t, x)))
              * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) q (t, x)|
              ≤ (Phi (t, x) * b2 (q (t, x))) * (D * Real.sqrt (incrGradQsq h V (t, x))) := by
            rw [abs_mul, abs_of_nonneg hwnn]
            exact mul_le_mul_of_nonneg_left hcs2 hwnn
          linarith [hterm1, h2]
      _ = (D * G * K) * |R x|
            + (Phi (t, x) * b2 (q (t, x)))
              * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|)) := by ring
  -- integrate the pointwise bound
  have hcW : Continuous (fun x : E3 => ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := by
    refine continuous_finset_sum _ fun a _ => ?_
    exact (((contDiff_incrComp h hV a).continuous).comp
        (continuous_const.prodMk continuous_id)).mul
      ((continuous_dvec W hW (0, ee a)).comp (continuous_const.prodMk continuous_id))
  have hcgq : Continuous (fun x : E3 => incrGradQsq h V (t, x)) := by
    refine continuous_finset_sum _ fun a _ => ?_
    exact (((continuous_dvec _ hq (0, ee a)).comp
      (continuous_const.prodMk continuous_id)).pow 2)
  have hcsqrt : Continuous (fun x : E3 => Real.sqrt (incrGradQsq h V (t, x))) :=
    Real.continuous_sqrt.comp hcgq
  have hcweight : Continuous (fun x : E3 => Phi (t, x) * b2 (q (t, x))) :=
    (hPhi.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hb2c.comp (hq.continuous.comp (continuous_const.prodMk continuous_id)))
  have hcbound : Continuous (fun x : E3 => (D * G * K) * |R x|
      + (Phi (t, x) * b2 (q (t, x)))
        * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|))) :=
    (continuous_const.mul hcR.abs).add
      (hcweight.mul (hcsqrt.mul (continuous_const.mul hcR.abs)))
  have hstep1 : |cellInt (fun x => R x
        * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))|
      ≤ cellInt (fun x => (D * G * K) * |R x|
        + (Phi (t, x) * b2 (q (t, x)))
          * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|))) := by
    refine le_trans (abs_cellInt_le (hcR.mul hcW)) ?_
    exact cellInt_mono (hcR.mul hcW).abs hcbound hDrift
  have hsplit2 : cellInt (fun x => (D * G * K) * |R x|
        + (Phi (t, x) * b2 (q (t, x)))
          * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|)))
      = (D * G * K) * cellInt (fun x => |R x|)
        + cellInt (fun x => (Phi (t, x) * b2 (q (t, x)))
            * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|))) := by
    rw [cellInt_add (f := fun x : E3 => (D * G * K) * |R x|)
        (g := fun x : E3 => (Phi (t, x) * b2 (q (t, x)))
          * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|)))
        (continuous_const.mul hcR.abs)
        (hcweight.mul (hcsqrt.mul (continuous_const.mul hcR.abs))),
      cellInt_const_mul (D * G * K) (fun x => |R x|)]
  -- Young absorption of the dissipation pairing
  have hwnn : ∀ x : E3, 0 ≤ Phi (t, x) * b2 (q (t, x)) := fun x =>
    mul_nonneg (hPhinn _) (hb2nn _)
  have hyoung0 := cellInt_mul_le_young (w := fun x : E3 => Phi (t, x) * b2 (q (t, x)))
    (a := fun x : E3 => Real.sqrt (incrGradQsq h V (t, x)))
    (b := fun x : E3 => D * |R x|) hcweight hcsqrt (continuous_const.mul hcR.abs) hwnn
    (eta := eta * nu) (by positivity)
  have hsq1 : ∀ x : E3, (Real.sqrt (incrGradQsq h V (t, x))) ^ 2 = incrGradQsq h V (t, x) :=
    fun x => Real.sq_sqrt (incrGradQsq_nonneg h V (t, x))
  have hyoung : cellInt (fun x => (Phi (t, x) * b2 (q (t, x)))
        * (Real.sqrt (incrGradQsq h V (t, x)) * (D * |R x|)))
      ≤ eta * nu * cellInt (fun x => (Phi (t, x) * b2 (q (t, x))) * incrGradQsq h V (t, x))
        + (1 / (4 * (eta * nu))) * cellInt (fun x => (Phi (t, x) * b2 (q (t, x)))
            * (D * |R x|) ^ 2) := by
    have hrw : cellInt (fun x : E3 => (Phi (t, x) * b2 (q (t, x)))
          * (Real.sqrt (incrGradQsq h V (t, x))) ^ 2)
        = cellInt (fun x : E3 => (Phi (t, x) * b2 (q (t, x))) * incrGradQsq h V (t, x)) :=
      cellInt_congr fun x => by rw [hsq1 x]
    exact hrw ▸ hyoung0
  -- the residual pressure term
  have hBnn : 0 ≤ B := le_trans (hwnn 0) (hB (t, 0))
  have hres : cellInt (fun x => (Phi (t, x) * b2 (q (t, x))) * (D * |R x|) ^ 2)
      ≤ D ^ 2 * B * Osc := by
    have hpt : ∀ x : E3, (Phi (t, x) * b2 (q (t, x))) * (D * |R x|) ^ 2
        ≤ (D ^ 2 * B) * (R x) ^ 2 := by
      intro x
      have hRsq : (D * |R x|) ^ 2 = D ^ 2 * (R x) ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [hRsq]
      have hw := hB (t, x)
      nlinarith [sq_nonneg (R x), sq_nonneg D, hwnn x]
    have hc1 : Continuous (fun x : E3 => (Phi (t, x) * b2 (q (t, x))) * (D * |R x|) ^ 2) :=
      hcweight.mul ((continuous_const.mul hcR.abs).pow 2)
    have hc2 : Continuous (fun x : E3 => (D ^ 2 * B) * (R x) ^ 2) :=
      continuous_const.mul (hcR.pow 2)
    have hmono := cellInt_mono hc1 hc2 hpt
    rw [cellInt_const_mul (D ^ 2 * B) (fun x => (R x) ^ 2)] at hmono
    have : (D ^ 2 * B) * cellInt (fun x => (R x) ^ 2) ≤ (D ^ 2 * B) * Osc :=
      mul_le_mul_of_nonneg_left hOsc (by positivity)
    linarith
  -- the cutoff term
  have habsR : cellInt (fun x => |R x|) ≤ Real.sqrt Osc := by
    have hCS := cellInt_cauchy_schwarz hcR.abs (continuous_const : Continuous fun _ : E3 => (1:ℝ))
    have hone : cellInt (fun _ : E3 => (1:ℝ) ^ 2) = 1 := by
      simp
    have hRsq : cellInt (fun x => |R x| ^ 2) = cellInt (fun x => (R x) ^ 2) :=
      cellInt_congr fun x => sq_abs _
    rw [hone, mul_one, hRsq] at hCS
    have hmul : cellInt (fun x => |R x| * 1) = cellInt (fun x => |R x|) :=
      cellInt_congr fun x => mul_one _
    rw [hmul] at hCS
    have hnn : 0 ≤ cellInt (fun x => |R x|) := cellInt_nonneg fun x => abs_nonneg _
    have hle : (cellInt (fun x => |R x|)) ^ 2 ≤ Osc := le_trans hCS hOsc
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hnn] at this
  -- assemble
  have hDGK : 0 ≤ D * G * K := by
    have hKnn : 0 ≤ K := le_trans (abs_nonneg _) (hK (t, 0))
    positivity
  have hfinal : |cellInt (fun x => R x
        * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x))|
      ≤ eta * nu * cellInt (fun x => (Phi (t, x) * b2 (q (t, x))) * incrGradQsq h V (t, x))
        + (D ^ 2 * B / (4 * eta * nu)) * Osc
        + D * G * K * Real.sqrt Osc := by
    have hcut : (D * G * K) * cellInt (fun x => |R x|) ≤ D * G * K * Real.sqrt Osc :=
      mul_le_mul_of_nonneg_left habsR hDGK
    have hcoef : (1 / (4 * (eta * nu))) * cellInt (fun x =>
          (Phi (t, x) * b2 (q (t, x))) * (D * |R x|) ^ 2)
        ≤ (D ^ 2 * B / (4 * eta * nu)) * Osc := by
      have hstep : (1 / (4 * (eta * nu))) * cellInt (fun x =>
            (Phi (t, x) * b2 (q (t, x))) * (D * |R x|) ^ 2)
          ≤ (1 / (4 * (eta * nu))) * (D ^ 2 * B * Osc) :=
        mul_le_mul_of_nonneg_left hres (by positivity)
      have hrw : (1 / (4 * (eta * nu))) * (D ^ 2 * B * Osc)
          = (D ^ 2 * B / (4 * eta * nu)) * Osc := by
        field_simp
      linarith [hstep, hrw ▸ hstep]
    linarith [hstep1, hsplit2 ▸ hstep1, hyoung, hcut, hcoef]
  have hLHS : cellInt (fun x => (Phi (t, x) * b1 (q (t, x)))
      * (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))
      = - cellInt (fun x => R x
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) W (t, x)) := hid
  rw [hLHS, abs_neg]
  exact hfinal

end ClayNS
