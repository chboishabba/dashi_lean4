/-
# The De Giorgi level-set recurrence

`DeGiorgiIteration.lean` proves the two engines: the fast geometric convergence
lemma `Y_{n+1} ≤ C b^n Y_n^{1+α} ⇒ Y_n → 0` and the hole-filling iteration.
What the increment programme still has to supply is the *recurrence itself*:
the extraction of `Y_{n+1} ≤ C b^n Y_n^{1+α}` from the localized level-set
inequality by choosing levels `k_n ↑ k_∞` and radii `r_n ↓ r_∞`.

This file proves the two level-set steps that are not specific to
Navier–Stokes, in a general measure space, and then assembles the recurrence.

* `ClayNS.levelSet`, `ClayNS.levelEnergy`, `ClayNS.levelMeasure` — the level-set
  data `A_k = {w > k}`, `Y(k) = ∫_{A_k}(w−k)²`, `m(k) = |A_k|`.
* `ClayNS.chebyshev_levelMeasure` — the measure estimate
  `(k'−k)² m(k') ≤ Y(k)`, i.e. `1_{w>k'} ≤ (k'−k)^{-2}(w−k)_+²` integrated.
* `ClayNS.hoelder_levelEnergy` — the Hölder step
  `Y(k') ≤ (∫_{A_{k'}}((w−k')²)^{5/3})^{3/5} m(k')^{2/5}`, the exponent pair
  matching the three-dimensional parabolic `L^{10/3}` gain.
* `ClayNS.deGiorgi_level_step` — the two combined: with a bound `S` for the
  higher-integrability integral, `Y(k') ≤ S^{3/5}((k'−k)^{-2}Y(k))^{2/5}`.
* `ClayNS.deGiorgi_recurrence_extraction` — **the recurrence**: with the
  standard energy/embedding input `S_n ≤ C_S(4^n Y_n)^{5/3}` and the Chebyshev
  bound `m_{n+1} ≤ 4^{n+1}κ^{-2}Y_n` coming from the dyadic level choice
  `k_n = k_∞(1−2^{-n})`, one gets exactly
  `Y_{n+1} ≤ C·b^n·Y_n^{1+2/5}` with `b = 4^{7/5} > 1` and `α = 2/5`.
* `ClayNS.deGiorgi_recurrence_tendsto_zero` — chaining it to the already-proved
  `deGiorgi_fast_convergence`.
* `ClayNS.deGiorgiLevel`, `ClayNS.chebyshev_deGiorgiLevel`,
  `ClayNS.deGiorgi_level_step_measure`, `ClayNS.deGiorgi_dyadic_recurrence` — the
  same recurrence stated for the *actual* dyadic level sequence
  `k_n = k_∞(1−2^{-n})` and the actual level-set energies of a bounded
  measurable density, with the parabolic embedding as the only hypothesis.

The exponent `α = 2/5` is the three-dimensional parabolic one.  What this file
does **not** do is derive the energy/embedding input `S_n ≤ C_S(4^nY_n)^{5/3}`
for the increment density `q = ½|δ_hu|²` from the localized inequality: that is
the Sobolev/Gagliardo–Nirenberg half of `C_c`, and it is stated here as an
explicit hypothesis, not proved.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.DeGiorgiIteration

open MeasureTheory Filter Topology

open scoped BigOperators ENNReal

noncomputable section

namespace ClayNS

variable {X : Type*} [MeasurableSpace X]

/-- The level set `A_k = {w > k}`. -/
def levelSet (w : X → ℝ) (k : ℝ) : Set X := {x | k < w x}

/-- The level-set energy `Y(k) = ∫_{A_k}(w−k)²`. -/
def levelEnergy (mu : Measure X) (w : X → ℝ) (k : ℝ) : ℝ :=
  ∫ x in levelSet w k, (w x - k) ^ 2 ∂mu

/-- The measure `m(k) = |A_k|` of the level set. -/
def levelMeasure (mu : Measure X) (w : X → ℝ) (k : ℝ) : ℝ := (mu (levelSet w k)).toReal

lemma measurableSet_levelSet {w : X → ℝ} (hw : Measurable w) (k : ℝ) :
    MeasurableSet (levelSet w k) := measurableSet_lt measurable_const hw

omit [MeasurableSpace X] in
lemma levelSet_subset {w : X → ℝ} {k k' : ℝ} (hkk' : k ≤ k') :
    levelSet w k' ⊆ levelSet w k := fun _x hx => lt_of_le_of_lt hkk' hx

lemma levelMeasure_nonneg (mu : Measure X) (w : X → ℝ) (k : ℝ) :
    0 ≤ levelMeasure mu w k := ENNReal.toReal_nonneg

lemma levelEnergy_nonneg (mu : Measure X) (w : X → ℝ) (k : ℝ) :
    0 ≤ levelEnergy mu w k :=
  setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun _x => sq_nonneg _)

/-- Boundedness and measurability give integrability of every power of the
truncation on a finite measure space. -/
lemma memLp_sub_sq {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ} (hw : Measurable w)
    {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) (k : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => (w x - k) ^ 2) p mu := by
  have hmeas : AEStronglyMeasurable (fun x => (w x - k) ^ 2) mu :=
    ((hw.sub measurable_const).pow_const 2).aestronglyMeasurable
  refine memLp_of_bounded (a := 0) (b := (Mb + |k|) ^ 2) ?_ hmeas p
  filter_upwards with x
  refine ⟨sq_nonneg _, ?_⟩
  have habs : |w x - k| ≤ Mb + |k| :=
    le_trans (abs_sub _ _) (by linarith [hb x])
  have h0 : 0 ≤ |w x - k| := abs_nonneg _
  calc (w x - k) ^ 2 = |w x - k| ^ 2 := (sq_abs _).symm
    _ ≤ (Mb + |k|) ^ 2 := by nlinarith [habs, h0]

/-! ## The Chebyshev measure estimate -/

/-- **Chebyshev.**  `(k'−k)²·m(k') ≤ Y(k)` — the measure of the higher level set
is controlled by the level-set energy at the lower level, with the gain
`(k'−k)^{-2}`.  This is the integrated form of
`1_{w>k'} ≤ (k'−k)^{-2}(w−k)_+²`. -/
theorem chebyshev_levelMeasure {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {k k' : ℝ} (hkk' : k ≤ k') :
    (k' - k) ^ 2 * levelMeasure mu w k' ≤ levelEnergy mu w k := by
  have hsub : levelSet w k' ⊆ levelSet w k := levelSet_subset hkk'
  have hint : IntegrableOn (fun x => (w x - k) ^ 2) (levelSet w k) mu :=
    ((memLp_sub_sq hw hb k 1).integrable (le_refl 1)).integrableOn
  -- the constant is below the integrand on the higher level set
  have hconst : ∫ _x in levelSet w k', (k' - k) ^ 2 ∂mu
      ≤ ∫ x in levelSet w k', (w x - k) ^ 2 ∂mu := by
    refine setIntegral_mono_on integrableOn_const
      (hint.mono_set hsub) (measurableSet_levelSet hw k') ?_
    intro x hx
    have hx' : k' < w x := hx
    nlinarith [hx', hkk']
  have hmono : ∫ x in levelSet w k', (w x - k) ^ 2 ∂mu
      ≤ ∫ x in levelSet w k, (w x - k) ^ 2 ∂mu := by
    refine setIntegral_mono_set hint ?_ (HasSubset.Subset.eventuallyLE hsub)
    exact Filter.Eventually.of_forall fun x => sq_nonneg _
  have hval : ∫ _x in levelSet w k', (k' - k) ^ 2 ∂mu
      = (k' - k) ^ 2 * levelMeasure mu w k' := by
    rw [setIntegral_const, measureReal_def, levelMeasure, smul_eq_mul]
    ring
  rw [hval] at hconst
  exact le_trans hconst hmono

/-! ## The Hölder step -/

/-- **Hölder.**  `Y(k') ≤ (∫_{A_{k'}}((w−k')²)^{5/3})^{3/5}·m(k')^{2/5}`.  The
exponent pair `(5/3, 5/2)` is the one produced by the three-dimensional
parabolic `L^{10/3}` embedding. -/
theorem hoelder_levelEnergy {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) (k' : ℝ) :
    levelEnergy mu w k'
      ≤ (∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu) ^ (3 / 5 : ℝ)
        * (levelMeasure mu w k') ^ (2 / 5 : ℝ) := by
  have hconj : (5 / 3 : ℝ).HolderConjugate (5 / 2) := by constructor <;> norm_num
  have hf : MemLp (fun x => (w x - k') ^ 2) (ENNReal.ofReal (5 / 3 : ℝ))
      (mu.restrict (levelSet w k')) := (memLp_sub_sq hw hb k' _).restrict _
  have hg : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal (5 / 2 : ℝ))
      (mu.restrict (levelSet w k')) := memLp_const 1
  have hfnn : 0 ≤ᵐ[mu.restrict (levelSet w k')] fun x => (w x - k') ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hgnn : 0 ≤ᵐ[mu.restrict (levelSet w k')] fun _ : X => (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => zero_le_one
  have hkey := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu.restrict (levelSet w k')) hconj hfnn hgnn hf hg
  have hlhs : ∫ x in levelSet w k', ((w x - k') ^ 2) * (1 : ℝ) ∂mu = levelEnergy mu w k' := by
    simp [levelEnergy]
  have hrhs : (∫ _x in levelSet w k', (1 : ℝ) ^ (5 / 2 : ℝ) ∂mu) = levelMeasure mu w k' := by
    simp [levelMeasure, measureReal_def]
  rw [hlhs, hrhs] at hkey
  have he1 : (1 / (5 / 3 : ℝ)) = 3 / 5 := by norm_num
  have he2 : (1 / (5 / 2 : ℝ)) = 2 / 5 := by norm_num
  rw [he1, he2] at hkey
  exact hkey

/-- **One De Giorgi level step.**  With `S` a bound for the higher-integrability
integral at level `k'`, the two previous results combine to
`Y(k') ≤ S^{3/5}·((k'−k)^{-2}Y(k))^{2/5}`. -/
theorem deGiorgi_level_step {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {k k' S : ℝ} (hkk' : k < k')
    (hS0 : 0 ≤ S)
    (hS : (∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu) ≤ S) :
    levelEnergy mu w k'
      ≤ S ^ (3 / 5 : ℝ) * ((k' - k) ^ (-2 : ℝ) * levelEnergy mu w k) ^ (2 / 5 : ℝ) := by
  have hgap : (0:ℝ) < k' - k := by linarith
  have hcheb := chebyshev_levelMeasure (mu := mu) hw hb hkk'.le
  have hmle : levelMeasure mu w k' ≤ (k' - k) ^ (-2 : ℝ) * levelEnergy mu w k := by
    have hpos : (0:ℝ) < (k' - k) ^ 2 := by positivity
    have hrw : (k' - k) ^ (-2 : ℝ) = ((k' - k) ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hgap.le,
        Real.rpow_natCast]
    rw [hrw, inv_mul_eq_div, le_div_iff₀ hpos]
    linarith [hcheb]
  have hhold := hoelder_levelEnergy (mu := mu) hw hb k'
  have hInt0 : 0 ≤ ∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu :=
    setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (sq_nonneg _) _)
  have h1 : (∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu) ^ (3 / 5 : ℝ)
      ≤ S ^ (3 / 5 : ℝ) := Real.rpow_le_rpow hInt0 hS (by norm_num)
  have h2 : (levelMeasure mu w k') ^ (2 / 5 : ℝ)
      ≤ ((k' - k) ^ (-2 : ℝ) * levelEnergy mu w k) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow (levelMeasure_nonneg mu w k') hmle (by norm_num)
  calc levelEnergy mu w k'
      ≤ (∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu) ^ (3 / 5 : ℝ)
          * (levelMeasure mu w k') ^ (2 / 5 : ℝ) := hhold
    _ ≤ S ^ (3 / 5 : ℝ) * ((k' - k) ^ (-2 : ℝ) * levelEnergy mu w k) ^ (2 / 5 : ℝ) := by
        refine mul_le_mul h1 h2 (Real.rpow_nonneg (levelMeasure_nonneg mu w k') _)
          (Real.rpow_nonneg hS0 _)

/-! ## The recurrence -/

/-- **Recurrence extraction.**  Suppose the level-set energies `Y n` and level
measures `M n` of a De Giorgi sequence satisfy

* the step estimate `Y(n+1) ≤ (C_S(4ⁿY n)^{5/3})^{3/5}·M(n+1)^{2/5}`
  (Hölder plus the parabolic energy/embedding input), and
* the Chebyshev estimate `M(n+1) ≤ 4^{n+1}κ^{-2}Y n`
  (the dyadic level choice `k_n = k_∞(1−2^{-n})`).

Then the sequence obeys exactly the fast-convergence recursion

`Y(n+1) ≤ C·b^n·Y(n)^{1+2/5}`,  `C = C_S^{3/5}4^{2/5}κ^{-4/5}`, `b = 4^{7/5}`.

`α = 2/5` is the three-dimensional parabolic exponent. -/
theorem deGiorgi_recurrence_extraction {Y M : ℕ → ℝ} {CS kappa : ℝ}
    (hYnn : ∀ n, 0 ≤ Y n) (hMnn : ∀ n, 0 ≤ M n) (hCS : 0 < CS) (hkappa : 0 < kappa)
    (hstep : ∀ n, Y (n + 1)
      ≤ (CS * ((4 : ℝ) ^ (n : ℝ) * Y n) ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) * (M (n + 1)) ^ (2 / 5 : ℝ))
    (hcheb : ∀ n, M (n + 1) ≤ (4 : ℝ) ^ ((n : ℝ) + 1) * kappa ^ (-2 : ℝ) * Y n) (n : ℕ) :
    Y (n + 1)
      ≤ (CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kappa ^ (-4 / 5 : ℝ))
        * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (n : ℝ) * (Y n) ^ (1 + (2 / 5 : ℝ)) := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have h4n : (0:ℝ) < (4 : ℝ) ^ (n : ℝ) := Real.rpow_pos_of_pos h4 _
  have hYn := hYnn n
  -- the first factor
  have hfac1 : (CS * ((4 : ℝ) ^ (n : ℝ) * Y n) ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ)
      = CS ^ (3 / 5 : ℝ) * ((4 : ℝ) ^ (n : ℝ) * Y n) := by
    rw [Real.mul_rpow hCS.le (Real.rpow_nonneg (mul_nonneg h4n.le hYn) _),
      ← Real.rpow_mul (mul_nonneg h4n.le hYn)]
    norm_num
  -- the second factor
  have hfac2 : (M (n + 1)) ^ (2 / 5 : ℝ)
      ≤ ((4 : ℝ) ^ ((n : ℝ) + 1) * kappa ^ (-2 : ℝ) * Y n) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow (hMnn (n + 1)) (hcheb n) (by norm_num)
  have hexp2 : ((4 : ℝ) ^ ((n : ℝ) + 1) * kappa ^ (-2 : ℝ) * Y n) ^ (2 / 5 : ℝ)
      = (4 : ℝ) ^ ((2 / 5 : ℝ) * ((n : ℝ) + 1)) * kappa ^ (-4 / 5 : ℝ)
        * (Y n) ^ (2 / 5 : ℝ) := by
    have hk : (0:ℝ) ≤ kappa ^ (-2 : ℝ) := Real.rpow_nonneg hkappa.le _
    have h1 : (0:ℝ) ≤ (4 : ℝ) ^ ((n : ℝ) + 1) := (Real.rpow_pos_of_pos h4 _).le
    rw [Real.mul_rpow (mul_nonneg h1 hk) hYn, Real.mul_rpow h1 hk,
      ← Real.rpow_mul h4.le, ← Real.rpow_mul hkappa.le,
      mul_comm ((n : ℝ) + 1) (2 / 5 : ℝ)]
    norm_num
  -- combine
  have hstepn := hstep n
  rw [hfac1] at hstepn
  have hnn1 : 0 ≤ CS ^ (3 / 5 : ℝ) * ((4 : ℝ) ^ (n : ℝ) * Y n) :=
    mul_nonneg (Real.rpow_nonneg hCS.le _) (mul_nonneg h4n.le hYn)
  have hchain : Y (n + 1)
      ≤ (CS ^ (3 / 5 : ℝ) * ((4 : ℝ) ^ (n : ℝ) * Y n))
        * ((4 : ℝ) ^ ((2 / 5 : ℝ) * ((n : ℝ) + 1)) * kappa ^ (-4 / 5 : ℝ)
          * (Y n) ^ (2 / 5 : ℝ)) := by
    refine le_trans hstepn ?_
    refine mul_le_mul_of_nonneg_left ?_ hnn1
    exact le_trans hfac2 (le_of_eq hexp2)
  refine le_trans hchain (le_of_eq ?_)
  have hYsplit : Y n * (Y n) ^ (2 / 5 : ℝ) = (Y n) ^ (1 + (2 / 5 : ℝ)) := by
    rw [Real.rpow_add_of_nonneg hYn (by norm_num) (by norm_num), Real.rpow_one]
  have h4split : (4 : ℝ) ^ (n : ℝ) * (4 : ℝ) ^ ((2 / 5 : ℝ) * ((n : ℝ) + 1))
      = (4 : ℝ) ^ (2 / 5 : ℝ) * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (n : ℝ) := by
    rw [← Real.rpow_add h4, ← Real.rpow_mul h4.le, ← Real.rpow_add h4]
    ring_nf
  calc (CS ^ (3 / 5 : ℝ) * ((4 : ℝ) ^ (n : ℝ) * Y n))
        * ((4 : ℝ) ^ ((2 / 5 : ℝ) * ((n : ℝ) + 1)) * kappa ^ (-4 / 5 : ℝ)
          * (Y n) ^ (2 / 5 : ℝ))
      = CS ^ (3 / 5 : ℝ) * kappa ^ (-4 / 5 : ℝ)
          * ((4 : ℝ) ^ (n : ℝ) * (4 : ℝ) ^ ((2 / 5 : ℝ) * ((n : ℝ) + 1)))
          * (Y n * (Y n) ^ (2 / 5 : ℝ)) := by ring
    _ = (CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kappa ^ (-4 / 5 : ℝ))
          * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (n : ℝ) * (Y n) ^ (1 + (2 / 5 : ℝ)) := by
        rw [h4split, hYsplit]; ring

/-- **The recurrence feeds the fast convergence lemma.**  Under the hypotheses of
`deGiorgi_recurrence_extraction` and the corresponding smallness of `Y 0`, the
level-set energies converge to zero geometrically. -/
theorem deGiorgi_recurrence_tendsto_zero {Y M : ℕ → ℝ} {CS kappa : ℝ}
    (hYnn : ∀ n, 0 ≤ Y n) (hMnn : ∀ n, 0 ≤ M n) (hCS : 0 < CS) (hkappa : 0 < kappa)
    (hstep : ∀ n, Y (n + 1)
      ≤ (CS * ((4 : ℝ) ^ (n : ℝ) * Y n) ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) * (M (n + 1)) ^ (2 / 5 : ℝ))
    (hcheb : ∀ n, M (n + 1) ≤ (4 : ℝ) ^ ((n : ℝ) + 1) * kappa ^ (-2 : ℝ) * Y n)
    (hsmall : Y 0
      ≤ (CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kappa ^ (-4 / 5 : ℝ)) ^ (-1 / (2 / 5 : ℝ))
        * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (-1 / (2 / 5 : ℝ) ^ 2)) :
    Tendsto Y atTop (nhds 0) := by
  have hCpos : 0 < CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kappa ^ (-4 / 5 : ℝ) := by
    have h1 : 0 < CS ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hCS _
    have h2 : 0 < (4 : ℝ) ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < kappa ^ (-4 / 5 : ℝ) := Real.rpow_pos_of_pos hkappa _
    positivity
  have hb : (1:ℝ) < (4 : ℝ) ^ (7 / 5 : ℝ) := by
    have := Real.one_lt_rpow_iff_of_pos (x := (4:ℝ)) (y := (7/5 : ℝ)) (by norm_num)
    rw [this]
    norm_num
  exact deGiorgi_tendsto_zero hCpos hb (by norm_num) hYnn
    (fun n => deGiorgi_recurrence_extraction hYnn hMnn hCS hkappa hstep hcheb n) hsmall

/-! ## The recurrence for an actual dyadic level sequence -/

/-- The dyadic De Giorgi levels `k_n = k_∞(1 − 2^{-n})`, increasing to `k_∞`. -/
def deGiorgiLevel (kinf : ℝ) (n : ℕ) : ℝ := kinf * (1 - (2 : ℝ) ^ (-(n : ℝ)))

lemma four_rpow_eq_two_rpow_sq (c : ℝ) : (4 : ℝ) ^ c = ((2 : ℝ) ^ c) ^ 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), sq]

/-- The gap between two consecutive dyadic levels. -/
lemma deGiorgiLevel_gap (kinf : ℝ) (n : ℕ) :
    deGiorgiLevel kinf (n + 1) - deGiorgiLevel kinf n = kinf * (2 : ℝ) ^ (-((n : ℝ) + 1)) := by
  have h2 : (2 : ℝ) ^ (-(n : ℝ)) = (2 : ℝ) ^ (-((n : ℝ) + 1)) * 2 := by
    rw [show (-(n : ℝ)) = (-((n : ℝ) + 1)) + 1 by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  simp only [deGiorgiLevel, Nat.cast_add, Nat.cast_one]
  rw [h2]
  ring

/-- **Chebyshev along the dyadic levels.**  `m_{n+1} ≤ 4^{n+1}k_∞^{-2}Y_n`. -/
theorem chebyshev_deGiorgiLevel {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {kinf : ℝ} (hk : 0 < kinf) (n : ℕ) :
    levelMeasure mu w (deGiorgiLevel kinf (n + 1))
      ≤ (4 : ℝ) ^ ((n : ℝ) + 1) * kinf ^ (-2 : ℝ)
        * levelEnergy mu w (deGiorgiLevel kinf n) := by
  have hgap := deGiorgiLevel_gap kinf n
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) + 1)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmono : deGiorgiLevel kinf n ≤ deGiorgiLevel kinf (n + 1) := by
    have : (0 : ℝ) ≤ kinf * (2 : ℝ) ^ (-((n : ℝ) + 1)) := by positivity
    linarith [hgap]
  have hch := chebyshev_levelMeasure (mu := mu) hw hb hmono
  rw [hgap] at hch
  set A : ℝ := (4 : ℝ) ^ ((n : ℝ) + 1) with hA
  set K : ℝ := kinf ^ 2 with hK
  have hApos : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hKpos : 0 < K := by positivity
  have hsq : (kinf * (2 : ℝ) ^ (-((n : ℝ) + 1))) ^ 2 = K * A⁻¹ := by
    rw [mul_pow, ← four_rpow_eq_two_rpow_sq, hA, hK,
      show (-((n : ℝ) + 1)) = -((n : ℝ) + 1) from rfl,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
  rw [hsq] at hch
  have hkinv : kinf ^ (-2 : ℝ) = K⁻¹ := by
    rw [hK, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hk.le,
      Real.rpow_natCast]
  rw [hkinv]
  have hAK : (0 : ℝ) < A * K⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hch hAK.le
  calc levelMeasure mu w (deGiorgiLevel kinf (n + 1))
      = A * K⁻¹ * (K * A⁻¹ * levelMeasure mu w (deGiorgiLevel kinf (n + 1))) := by
        field_simp
    _ ≤ A * K⁻¹ * levelEnergy mu w (deGiorgiLevel kinf n) := hmul

/-- **Hölder step in level-measure form.**  With `S` a bound for the
higher-integrability integral at level `k'`, `Y(k') ≤ S^{3/5}·m(k')^{2/5}`. -/
theorem deGiorgi_level_step_measure {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {k' S : ℝ}
    (hS : (∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu) ≤ S) :
    levelEnergy mu w k' ≤ S ^ (3 / 5 : ℝ) * (levelMeasure mu w k') ^ (2 / 5 : ℝ) := by
  have hInt0 : 0 ≤ ∫ x in levelSet w k', ((w x - k') ^ 2) ^ (5 / 3 : ℝ) ∂mu :=
    setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun _x => Real.rpow_nonneg (sq_nonneg _) _)
  refine le_trans (hoelder_levelEnergy (mu := mu) hw hb k') ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hInt0 hS (by norm_num))
    (Real.rpow_nonneg (levelMeasure_nonneg mu w k') _)

/-- **The De Giorgi recurrence for the actual dyadic level sequence.**

Let `w` be a bounded measurable density on a finite measure space, `k_n` the
dyadic levels `k_∞(1−2^{-n})`, and `Y_n = ∫_{w>k_n}(w−k_n)²`.  Assume the
parabolic energy/embedding input

`∫_{w>k_{n+1}}((w−k_{n+1})²)^{5/3} ≤ C_S·(4ⁿ Y_n)^{5/3}`

(the `L^{10/3}` gain of the localized Caccioppoli inequality, whose constant is
the one produced by the level-set energy at the previous stage).  Then

`Y_{n+1} ≤ C·b^n·Y_n^{1+2/5}`,  `C = C_S^{3/5}4^{2/5}k_∞^{-4/5}`, `b = 4^{7/5}`,

which is exactly the hypothesis of `deGiorgi_fast_convergence` with the
three-dimensional parabolic exponent `α = 2/5`. -/
theorem deGiorgi_dyadic_recurrence {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {kinf CS : ℝ} (hk : 0 < kinf)
    (hCS : 0 < CS)
    (hEmb : ∀ n : ℕ,
      (∫ x in levelSet w (deGiorgiLevel kinf (n + 1)),
          ((w x - deGiorgiLevel kinf (n + 1)) ^ 2) ^ (5 / 3 : ℝ) ∂mu)
        ≤ CS * ((4 : ℝ) ^ (n : ℝ) * levelEnergy mu w (deGiorgiLevel kinf n)) ^ (5 / 3 : ℝ))
    (n : ℕ) :
    levelEnergy mu w (deGiorgiLevel kinf (n + 1))
      ≤ (CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kinf ^ (-4 / 5 : ℝ))
        * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (n : ℝ)
        * (levelEnergy mu w (deGiorgiLevel kinf n)) ^ (1 + (2 / 5 : ℝ)) := by
  refine deGiorgi_recurrence_extraction
    (Y := fun n => levelEnergy mu w (deGiorgiLevel kinf n))
    (M := fun n => levelMeasure mu w (deGiorgiLevel kinf n))
    (fun n => levelEnergy_nonneg mu w _) (fun n => levelMeasure_nonneg mu w _) hCS hk
    (fun n => ?_) (fun n => chebyshev_deGiorgiLevel hw hb hk n) n
  exact deGiorgi_level_step_measure hw hb (hEmb n)

end ClayNS
