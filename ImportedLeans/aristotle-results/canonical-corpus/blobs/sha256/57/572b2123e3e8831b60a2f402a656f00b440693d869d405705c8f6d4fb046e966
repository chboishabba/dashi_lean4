/-
# `L²` control of the pressure oscillation

The quantitative half of `C_a` needs an integrable bound on the *oscillation* of
the pressure increment `δ_h p` on the cell — the pressure never appears
undifferentiated against `q` (see `incr_pressure_localized_split`), only against
`∇Φ` and `β''(q)∇q`, so a bound modulo constants is exactly what is required.

The usual route to such a bound is Calderón–Zygmund theory for
`−Δp = ∂_i∂_j(u_iu_j)` followed by John–Nirenberg.  On the periodic cell there
is a completely elementary substitute at the `L²` level, and `L²` is all the
Young absorption consumes.  Testing the pressure Poisson equation with `p`
itself gives

`∫_cell |∇p|² = −∫_cell ∇p·(u·∇)u ≤ ‖∇p‖₂ ‖(u·∇)u‖₂`,

hence `‖∇p‖₂ ≤ ‖(u·∇)u‖₂ ≤ ‖u‖_∞ ‖∇u‖₂`, and the cell Poincaré inequality
(`cellInt_poincare`) converts this into an `L²` bound for `p` minus its mean.
Translation invariance of the cell integral (`cellInt_shift`) upgrades it to the
increment `δ_h p`, with the constant `12` in place of `3`.

## What is proved here

* `ClayNS.gradPsq`, `ClayNS.advSq` — the two densities.
* `ClayNS.cellInt_gradPsq_eq_neg_pairing` — the exact identity
  `∫|∇p|² = −∫∇p·(u·∇)u`, obtained from the pressure Poisson equation and two
  applications of the divergence theorem on the torus.
* `ClayNS.cellInt_gradPsq_le_advSq` — `∫|∇p|² ≤ ∫|(u·∇)u|²`.
* `ClayNS.cellInt_advSq_le` — `∫|(u·∇)u|² ≤ A²∫|∇u|²` for `|u|² ≤ A²`.
* `ClayNS.cellInt_pressure_oscillation_le` — `∫|p−⟨p⟩|² ≤ 3A²∫|∇u|²`.
* `ClayNS.cellInt_incrPres_oscillation_le` — `∫|δ_hp−⟨δ_hp⟩|² ≤ 12A²∫|∇u|²`,
  the form the absorption lemma uses.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CellL2

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The squared spatial gradient `∑_i (∂_i p)²` of a scalar field. -/
def gradPsq (P : STime → ℝ) (z : STime) : ℝ := ∑ i, (dvec (0, ee i) P z) ^ 2

/-- The squared advective term `∑_a ((u·∇)u)_a²`. -/
def advSq (V : STime → E3) (z : STime) : ℝ := ∑ a, (adv V z a) ^ 2

lemma gradPsq_nonneg (P : STime → ℝ) (z : STime) : 0 ≤ gradPsq P z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma advSq_nonneg (V : STime → E3) (z : STime) : 0 ≤ advSq V z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_gradPsq {P : STime → ℝ} (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    Continuous (gradPsq P) :=
  continuous_finset_sum _ fun i _ => (continuous_dvec P hP (0, ee i)).pow 2

lemma contDiff_advVec {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => adv V w) :=
  ContDiff.sum fun i _ => (contDiff_coord V hV i).smul (contDiff_dvec V hV (0, ee i))

lemma continuous_advSq {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Continuous (advSq V) :=
  continuous_finset_sum _ fun a _ =>
    ((contDiff_coord _ (contDiff_advVec hV) a).continuous).pow 2

lemma continuous_divg_adv {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Continuous (fun z : STime => divg (fun w => adv V w) z) :=
  continuous_divg (contDiff_advVec hV)

lemma continuous_gradSqV {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Continuous (fun z : STime => gradSq (fun a w => V w a) z) :=
  continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun a _ =>
    (continuous_dvec _ (contDiff_coord V hV a) (0, ee k)).mul
      (continuous_dvec _ (contDiff_coord V hV a) (0, ee k))

lemma spacePeriodic_gradPsq {P : STime → ℝ} (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hper : SpacePeriodic P) : SpacePeriodic (gradPsq P) := by
  intro z j
  have hd : ∀ i : Fin 3, dvec (0, ee i) P (z.1, z.2 + ee j) = dvec (0, ee i) P z := fun i =>
    spacePeriodic_dvec (differentiable_of_contDiffTop hP) hper (0, ee i) z j
  simp only [gradPsq, hd]

/-! ## The pressure energy identity -/

/-- The cell integral of `|∇p|²` equals minus the pairing of `∇p` with the
advective term.  This is the pressure Poisson equation tested with `p`. -/
theorem cellInt_gradPsq_eq_neg_pairing (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z) (t : ℝ) :
    cellInt (fun x => gradPsq P (t, x))
      = - cellInt (fun x => ∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a) := by
  classical
  have hgradP : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad P w) := contDiff_grad hP
  have hadv : ContDiff ℝ (⊤ : ℕ∞) (fun w => adv V w) := contDiff_advVec hV
  -- periodicity of the two fluxes
  have hgradPper : SpacePeriodic (fun w => grad P w) := by
    intro z j
    have hd : ∀ i : Fin 3, dspace P i (z.1, z.2 + ee j) = dspace P i z := fun i =>
      spacePeriodic_dvec (differentiable_of_contDiffTop hP) hPper (0, ee i) z j
    simp only [grad, hd]
  have hadvper : SpacePeriodic (fun w => adv V w) := by
    intro z j
    have hV0 : V (z.1, z.2 + ee j) = V z := hVper z j
    have hd : ∀ i : Fin 3, dspace V i (z.1, z.2 + ee j) = dspace V i z := fun i =>
      spacePeriodic_dvec (differentiable_of_contDiffTop hV) hVper (0, ee i) z j
    simp only [adv, hd, hV0]
  have hflux1per : SpacePeriodic (fun w => P w • grad P w) := by
    intro z j
    simp only [hPper z j, hgradPper z j]
  have hflux2per : SpacePeriodic (fun w => P w • adv V w) := by
    intro z j
    simp only [hPper z j, hadvper z j]
  -- the two divergence identities
  have hid1 : ∀ z : STime,
      divg (fun w => P w • grad P w) z = gradPsq P z + P z * lap P z := by
    intro z
    rw [divg_smul P (fun w => grad P w) hP hgradP z, divg_grad P hP z]
    simp only [grad_coord, gradPsq, sq]
  have hid2 : ∀ z : STime,
      divg (fun w => P w • adv V w) z
        = (∑ a, dvec (0, ee a) P z * adv V z a) + P z * divg (fun w => adv V w) z := by
    intro z
    rw [divg_smul P (fun w => adv V w) hP hadv z]
  -- the Poisson equation in divergence form
  have hpois : ∀ z : STime, lap P z = - divg (fun w => adv V w) z := by
    intro z
    have h1 := pressure_poisson nu V P hV hP hdiv hmom z
    have h2 := divg_adv V hV z
    have hzero : ∀ j : Fin 3, dvec (0, ee j) (fun w => divg V w) z = 0 := by
      intro j
      have : (fun w => divg V w) = fun _ : STime => (0 : ℝ) := funext hdiv
      rw [this]; simp [dvec]
    rw [h1, h2]
    simp [hzero]
  -- integrate the two divergences
  have hcgradPsq : Continuous (fun x : E3 => gradPsq P (t, x)) :=
    (continuous_gradPsq hP).comp (continuous_const.prodMk continuous_id)
  have hcPlap : Continuous (fun x : E3 => P (t, x) * lap P (t, x)) := by
    have hlapc : Continuous (fun z : STime => lap P z) :=
      continuous_finset_sum _ fun i _ =>
        continuous_dvec (dvec (0, ee i) P) (contDiff_dvec P hP (0, ee i)) (0, ee i)
    exact ((hP.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hlapc.comp (continuous_const.prodMk continuous_id)))
  have hcpair : Continuous (fun x : E3 => ∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a) := by
    refine continuous_finset_sum _ fun a _ => ?_
    exact ((continuous_dvec P hP (0, ee a)).comp
      (continuous_const.prodMk continuous_id)).mul
      (((contDiff_coord _ hadv a).continuous).comp
        (continuous_const.prodMk continuous_id))
  have hcPdivadv : Continuous (fun x : E3 => P (t, x) * divg (fun w => adv V w) (t, x)) := by
    have hdivc : Continuous (fun z : STime => divg (fun w => adv V w) z) :=
      continuous_divg_adv hV
    exact ((hP.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hdivc.comp (continuous_const.prodMk continuous_id)))
  have hzero1 : cellInt (fun x => gradPsq P (t, x)) + cellInt (fun x => P (t, x) * lap P (t, x))
      = 0 := by
    have h := cellInt_divg_eq_zero (fun w => P w • grad P w) (hP.smul hgradP) hflux1per t
    rw [cellInt_congr (fun x => hid1 (t, x)), cellInt_add hcgradPsq hcPlap] at h
    exact h
  have hzero2 : cellInt (fun x => ∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a)
      + cellInt (fun x => P (t, x) * divg (fun w => adv V w) (t, x)) = 0 := by
    have h := cellInt_divg_eq_zero (fun w => P w • adv V w) (hP.smul hadv) hflux2per t
    rw [cellInt_congr (fun x => hid2 (t, x)), cellInt_add hcpair hcPdivadv] at h
    exact h
  have hswap : cellInt (fun x => P (t, x) * lap P (t, x))
      = - cellInt (fun x => P (t, x) * divg (fun w => adv V w) (t, x)) := by
    rw [← cellInt_neg]
    refine cellInt_congr fun x => ?_
    rw [hpois (t, x)]
    ring
  rw [hswap] at hzero1
  linarith [hzero1, hzero2]

/-! ## The `L²` bound on the pressure gradient -/

/-- `∫_cell |∇p|² ≤ ∫_cell |(u·∇)u|²`. -/
theorem cellInt_gradPsq_le_advSq (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z) (t : ℝ) :
    cellInt (fun x => gradPsq P (t, x)) ≤ cellInt (fun x => advSq V (t, x)) := by
  classical
  have hadv : ContDiff ℝ (⊤ : ℕ∞) (fun w => adv V w) := contDiff_advVec hV
  set X := cellInt (fun x => gradPsq P (t, x)) with hX
  set Y := cellInt (fun x => advSq V (t, x)) with hY
  set S := cellInt (fun x => ∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a) with hS
  have hXeq : X = -S := cellInt_gradPsq_eq_neg_pairing nu V P hV hP hVper hPper hdiv hmom t
  -- the two square-root densities
  set f : E3 → ℝ := fun x => Real.sqrt (gradPsq P (t, x)) with hf
  set g : E3 → ℝ := fun x => Real.sqrt (advSq V (t, x)) with hg
  have hcf : Continuous f :=
    Real.continuous_sqrt.comp ((continuous_gradPsq hP).comp (continuous_const.prodMk continuous_id))
  have hcg : Continuous g :=
    Real.continuous_sqrt.comp ((continuous_advSq hV).comp (continuous_const.prodMk continuous_id))
  have hf2 : ∀ x : E3, (f x) ^ 2 = gradPsq P (t, x) := fun x =>
    Real.sq_sqrt (gradPsq_nonneg _ _)
  have hg2 : ∀ x : E3, (g x) ^ 2 = advSq V (t, x) := fun x =>
    Real.sq_sqrt (advSq_nonneg _ _)
  -- pointwise Cauchy–Schwarz in the three components
  have hpt : ∀ x : E3,
      |∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a| ≤ f x * g x := by
    intro x
    have hsum1 : ∑ a, (dvec (0, ee a) P (t, x)) ^ 2 = gradPsq P (t, x) := rfl
    have hsum2 : ∑ a, (adv V (t, x) a) ^ 2 = advSq V (t, x) := rfl
    calc |∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a|
        ≤ Real.sqrt (∑ a, (dvec (0, ee a) P (t, x)) ^ 2)
            * Real.sqrt (∑ a, (adv V (t, x) a) ^ 2) := by
          have hsq : (∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a) ^ 2
              ≤ (∑ a, (dvec (0, ee a) P (t, x)) ^ 2) * (∑ a, (adv V (t, x) a) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
          have h1 : (0:ℝ) ≤ ∑ a, (dvec (0, ee a) P (t, x)) ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have h2 : (0:ℝ) ≤ ∑ a, (adv V (t, x) a) ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have := Real.sqrt_le_sqrt hsq
          rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul h1] at this
      _ = f x * g x := by rw [hf, hg, hsum1, hsum2]
  -- integrate
  have hcpair : Continuous (fun x : E3 => ∑ a, dvec (0, ee a) P (t, x) * adv V (t, x) a) := by
    refine continuous_finset_sum _ fun a _ => ?_
    exact ((continuous_dvec P hP (0, ee a)).comp
      (continuous_const.prodMk continuous_id)).mul
      (((contDiff_coord _ hadv a).continuous).comp
        (continuous_const.prodMk continuous_id))
  have hT : |S| ≤ cellInt (fun x => f x * g x) := by
    refine le_trans (abs_cellInt_le hcpair) ?_
    exact cellInt_mono hcpair.abs (hcf.mul hcg) hpt
  have hCS : (cellInt (fun x => f x * g x)) ^ 2 ≤ X * Y := by
    have h := cellInt_cauchy_schwarz hcf hcg
    rw [cellInt_congr hf2, cellInt_congr hg2] at h
    exact h
  have hXnn : 0 ≤ X := cellInt_nonneg fun x => gradPsq_nonneg _ _
  have hYnn : 0 ≤ Y := cellInt_nonneg fun x => advSq_nonneg _ _
  have hXle : X ≤ cellInt (fun x => f x * g x) := by
    have : X ≤ |S| := by rw [hXeq]; exact neg_le_abs S
    linarith [hT]
  have hX2 : X ^ 2 ≤ X * Y := le_trans (by nlinarith [hXle, hXnn]) hCS
  rcases eq_or_lt_of_le hXnn with h0 | hpos
  · linarith
  · nlinarith [hX2, hpos]

/-- `∫_cell |(u·∇)u|² ≤ A² ∫_cell |∇u|²` when `|u|² ≤ A²` pointwise. -/
theorem cellInt_advSq_le {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) {A : ℝ}
    (hA : ∀ z : STime, ∑ i, (V z i) ^ 2 ≤ A ^ 2) (t : ℝ) :
    cellInt (fun x => advSq V (t, x))
      ≤ A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x)) := by
  classical
  have hpt : ∀ z : STime, advSq V z ≤ A ^ 2 * gradSq (fun a w => V w a) z := by
    intro z
    have hcomp : ∀ a : Fin 3, adv V z a = ∑ i, (V z i) * (dvec (0, ee i) (fun w => V w a) z) := by
      intro a
      simp only [adv, dspace_eq_dvec]
      rw [show ((∑ i, (V z i) • dvec (0, ee i) V z) : E3) a
          = ∑ i, ((V z i) • dvec (0, ee i) V z) a from by simp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ((V z i) • dvec (0, ee i) V z) a = (V z i) * (dvec (0, ee i) V z a) from rfl,
        dvec_coord V z (differentiable_of_contDiffTop hV z) (0, ee i) a]
    have hterm : ∀ a : Fin 3,
        (adv V z a) ^ 2 ≤ A ^ 2 * ∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2 := by
      intro a
      have hcs : (∑ i, (V z i) * (dvec (0, ee i) (fun w => V w a) z)) ^ 2
          ≤ (∑ i, (V z i) ^ 2) * (∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      have hnn : (0:ℝ) ≤ ∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc (adv V z a) ^ 2 = (∑ i, (V z i) * (dvec (0, ee i) (fun w => V w a) z)) ^ 2 := by
            rw [hcomp a]
        _ ≤ (∑ i, (V z i) ^ 2) * (∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2) := hcs
        _ ≤ A ^ 2 * ∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2 :=
            mul_le_mul_of_nonneg_right (hA z) hnn
    calc advSq V z = ∑ a, (adv V z a) ^ 2 := rfl
      _ ≤ ∑ a, A ^ 2 * ∑ i, (dvec (0, ee i) (fun w => V w a) z) ^ 2 :=
          Finset.sum_le_sum fun a _ => hterm a
      _ = A ^ 2 * gradSq (fun a w => V w a) z := by
          rw [← Finset.mul_sum]
          congr 1
          rw [gradSq, Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => pow_two _
  have hc1 : Continuous (fun x : E3 => advSq V (t, x)) :=
    (continuous_advSq hV).comp (continuous_const.prodMk continuous_id)
  have hc2 : Continuous (fun x : E3 => A ^ 2 * gradSq (fun a w => V w a) (t, x)) :=
    continuous_const.mul ((continuous_gradSqV hV).comp (continuous_const.prodMk continuous_id))
  have := cellInt_mono hc1 hc2 (fun x => hpt (t, x))
  rwa [cellInt_const_mul (A ^ 2) (fun x => gradSq (fun a w => V w a) (t, x))] at this

/-! ## The Poincaré step -/

/-- The cell Poincaré inequality in the `gradPsq` notation. -/
theorem cellInt_poincare_gradPsq {f : STime → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    cellInt (fun x => (f (t, x) - cellInt (fun y => f (t, y))) ^ 2)
      ≤ 3 * cellInt (fun x => gradPsq f (t, x)) := by
  classical
  have hslice : ContDiff ℝ 1 (fun y : E3 => f (t, y)) :=
    (contDiff_slice f hf t).of_le (by exact_mod_cast le_top)
  have hkey := cellInt_poincare (fun y : E3 => f (t, y)) hslice
  have hconv : ∀ (i : Fin 3) (x : E3),
      fderiv ℝ (fun y : E3 => f (t, y)) x (ee i) = dvec (0, ee i) f (t, x) := fun i x =>
    fderiv_slice_apply f (differentiable_of_contDiffTop hf) t x (ee i)
  simp only [hconv] at hkey
  have hsum : ∑ i, cellInt (fun x => (dvec (0, ee i) f (t, x)) ^ 2)
      = cellInt (fun x => gradPsq f (t, x)) := by
    rw [← cellInt_sum Finset.univ (fun i x => (dvec (0, ee i) f (t, x)) ^ 2)
      (fun i => ((continuous_dvec f hf (0, ee i)).comp
        (continuous_const.prodMk continuous_id)).pow 2)]
    rfl
  rw [hsum] at hkey
  exact hkey

/-- **`L²` oscillation bound for the pressure.**  `∫|p−⟨p⟩|² ≤ 3A²∫|∇u|²`. -/
theorem cellInt_pressure_oscillation_le (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {A : ℝ} (hA : ∀ z : STime, ∑ i, (V z i) ^ 2 ≤ A ^ 2) (t : ℝ) :
    cellInt (fun x => (P (t, x) - cellInt (fun y => P (t, y))) ^ 2)
      ≤ 3 * (A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x))) := by
  have h1 := cellInt_poincare_gradPsq hP t
  have h2 := cellInt_gradPsq_le_advSq nu V P hV hP hVper hPper hdiv hmom t
  have h3 := cellInt_advSq_le hV hA t
  linarith

/-! ## The increment -/

/-- **`L²` oscillation bound for the pressure increment.**
`∫|δ_hp−⟨δ_hp⟩|² ≤ 12A²∫|∇u|²`. -/
theorem cellInt_incrPres_oscillation_le (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {A : ℝ} (hA : ∀ z : STime, ∑ i, (V z i) ^ 2 ≤ A ^ 2) (t : ℝ) (h : E3) :
    cellInt (fun x => (incrPres h P (t, x)
        - cellInt (fun y => incrPres h P (t, y))) ^ 2)
      ≤ 12 * (A ^ 2 * cellInt (fun x => gradSq (fun a w => V w a) (t, x))) := by
  classical
  have hincr : ContDiff ℝ (⊤ : ℕ∞) (incrPres h P) := contDiff_incrPres h hP
  have hstep := cellInt_poincare_gradPsq hincr t
  -- the increment gradient density is bounded by twice the shifted plus twice the original
  have hpt : ∀ x : E3, gradPsq (incrPres h P) (t, x)
      ≤ 2 * gradPsq P (t, x + h) + 2 * gradPsq P (t, x) := by
    intro x
    have hd : ∀ i : Fin 3, dvec (0, ee i) (incrPres h P) (t, x)
        = dvec (0, ee i) P (t, x + h) - dvec (0, ee i) P (t, x) := by
      intro i
      have hsplit : dvec (0, ee i) (incrPres h P) (t, x)
          = dvec (0, ee i) (shift h P) (t, x) - dvec (0, ee i) P (t, x) := by
        have hdiff1 : DifferentiableAt ℝ (shift h P) (t, x) :=
          (differentiable_of_contDiffTop (contDiff_shift h hP)) (t, x)
        have hdiff2 : DifferentiableAt ℝ P (t, x) :=
          (differentiable_of_contDiffTop hP) (t, x)
        simpa [incrPres, dvec] using
          (fderiv_sub (𝕜 := ℝ) hdiff1 hdiff2) ▸ rfl
      rw [hsplit, dvec_shift]
      congr 1
      simp
    simp only [gradPsq, hd]
    have hterm : ∀ i : Fin 3,
        (dvec (0, ee i) P (t, x + h) - dvec (0, ee i) P (t, x)) ^ 2
          ≤ 2 * (dvec (0, ee i) P (t, x + h)) ^ 2 + 2 * (dvec (0, ee i) P (t, x)) ^ 2 := by
      intro i; nlinarith [sq_nonneg (dvec (0, ee i) P (t, x + h) + dvec (0, ee i) P (t, x))]
    calc ∑ i, (dvec (0, ee i) P (t, x + h) - dvec (0, ee i) P (t, x)) ^ 2
        ≤ ∑ i, (2 * (dvec (0, ee i) P (t, x + h)) ^ 2 + 2 * (dvec (0, ee i) P (t, x)) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * gradPsq P (t, x + h) + 2 * gradPsq P (t, x) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          rfl
  -- integrate, using translation invariance of the cell integral
  have hcont1 : Continuous (fun x : E3 => gradPsq (incrPres h P) (t, x)) :=
    (continuous_gradPsq hincr).comp (continuous_const.prodMk continuous_id)
  have hcont2 : Continuous (fun x : E3 => 2 * gradPsq P (t, x + h) + 2 * gradPsq P (t, x)) := by
    have hb : Continuous (fun x : E3 => gradPsq P (t, x + h)) :=
      (continuous_gradPsq hP).comp (continuous_const.prodMk (continuous_id.add continuous_const))
    have hc : Continuous (fun x : E3 => gradPsq P (t, x)) :=
      (continuous_gradPsq hP).comp (continuous_const.prodMk continuous_id)
    exact (continuous_const.mul hb).add (continuous_const.mul hc)
  have hint := cellInt_mono hcont1 hcont2 hpt
  have hshift : cellInt (fun x => gradPsq P (t, x + h)) = cellInt (fun x => gradPsq P (t, x)) :=
    cellInt_shift (gradPsq P) (by
      have hd : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee i) P) :=
        fun i => contDiff_dvec P hP (0, ee i)
      exact ContDiff.sum fun i _ => (hd i).pow 2) (spacePeriodic_gradPsq hP hPper) t h
  have hsplit : cellInt (fun x => 2 * gradPsq P (t, x + h) + 2 * gradPsq P (t, x))
      = 4 * cellInt (fun x => gradPsq P (t, x)) := by
    have hb : Continuous (fun x : E3 => 2 * gradPsq P (t, x + h)) :=
      continuous_const.mul
        ((continuous_gradPsq hP).comp (continuous_const.prodMk (continuous_id.add continuous_const)))
    have hc : Continuous (fun x : E3 => 2 * gradPsq P (t, x)) :=
      continuous_const.mul ((continuous_gradPsq hP).comp (continuous_const.prodMk continuous_id))
    rw [cellInt_add (f := fun x : E3 => 2 * gradPsq P (t, x + h))
        (g := fun x : E3 => 2 * gradPsq P (t, x)) hb hc,
      cellInt_const_mul 2 (fun x => gradPsq P (t, x + h)),
      cellInt_const_mul 2 (fun x => gradPsq P (t, x)), hshift]
    ring
  rw [hsplit] at hint
  have h2 := cellInt_gradPsq_le_advSq nu V P hV hP hVper hPper hdiv hmom t
  have h3 := cellInt_advSq_le hV hA t
  linarith [hstep, hint, h2, h3]

end ClayNS
