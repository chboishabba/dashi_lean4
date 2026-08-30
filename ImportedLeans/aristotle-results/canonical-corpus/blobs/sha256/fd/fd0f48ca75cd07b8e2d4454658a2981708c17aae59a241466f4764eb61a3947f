/-
# `C52`: is the concentrated weight a *detector*?

The proposal for `C52` (`GaussianModulusDefectPropagation`) is that the
concentrated weight might do more than localize: because `Φ_a(x₀) = 1` while
its total cell mass is `O(a^{3/2})`, a weighted functional is overwhelmingly
determined by what happens at the defect point, and one might hope to convert a
pointwise excess `r(x₀,t₀) ≥ λ+δ` into a definite transverse dissipation bill,
bypassing the full level-set De Giorgi recurrence.

Two things have to be true for that hope to survive, and this file settles both
— one positively, one negatively.

## 1.  The weight really is a detector (positive)

The concentration ratio is not merely *at most* `O(a^{3/2})`; it is *exactly* of
that order:

  `8e^{−3/4}·a^{3/2} ≤ ∫_cell Φ_a ≤ π³√(π³)·a^{3/2}`.

`ClayNS.cellInt_torusGauss_ge` is the lower bound.  So the weight does not
silently degenerate to `0`: the mass it retains is comparable to the mass a
genuine Gaussian of width `√a` retains, and a *lower* bound on a weighted
functional is therefore available at the same order as the upper bound.  This
is the property a detector needs.

## 2.  Concentration alone does not close the argument (negative)

`GaussianLinearBudgetAudit.lean` produced the unconditional budget in which the
only `a`-dependent constants are

  adjoint error  `O(a) + O(ν√a)`  and  gradient constant `1/(4πa)`.

The gradient constant multiplies `K₀ = ∫_cell β′(q)`, which carries **no**
weight.  `ClayNS.gaussian_gradient_term_blows_up` records the consequence
precisely: whenever that unweighted quantity is bounded below by a positive
number, the term `9AB²·(1/(4πa))·K₀` exceeds any prescribed bound for all
sufficiently small `a`.  So there is **no** choice of concentration scale that
makes the whole right-hand side small on its own, and the detector cannot
replace an estimate on `K₀`.

That is a genuine no-go for the "just concentrate harder" route, and it
identifies the surviving frontier exactly: an estimate for the *unweighted*
level-set quantity `K₀` — the smoothing-annulus remainder — is still required.
`ClayNS.GaussianModulusDefectPropagation` records the target statement itself;
it is **not** proved here, and nothing in the development assumes it.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianLinearBudgetAudit

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The Gaussian minorant of the periodic profile -/

/-- `ψ(s) ≤ s²`: the periodic profile is dominated by the Euclidean one. -/
lemma tgProfile_le_sq (s : ℝ) : tgProfile s ≤ s ^ 2 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have h : |Real.sin (π * s)| ≤ |π * s| := Real.abs_sin_le_abs
  have hsq : Real.sin (π * s) ^ 2 ≤ (π * s) ^ 2 := by
    nlinarith [sq_abs (Real.sin (π * s)), sq_abs (π * s),
      abs_nonneg (Real.sin (π * s)), abs_nonneg (π * s)]
  rw [tgProfile, div_le_iff₀ (by positivity)]
  nlinarith

/-- The one-dimensional factor dominates a genuine Gaussian of width `2√a`. -/
lemma tgFac_ge_gauss {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.exp (-(u ^ 2 / (4 * a))) ≤ tgFac a u := by
  rw [tgFac]
  refine Real.exp_le_exp.2 ?_
  have h := tgProfile_le_sq u
  have h4 : (0:ℝ) < 1 / (4 * a) := by positivity
  have := mul_le_mul_of_nonneg_left h h4.le
  have heq : 1 / (4 * a) * u ^ 2 = u ^ 2 / (4 * a) := by field_simp
  rw [heq] at this
  nlinarith

/-! ## The two-sided concentration ratio -/

/-- The one-dimensional mass is at least `2√a·e^{−1/4}`. -/
lemma integral_tgFac_ge {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) :
    2 * Real.sqrt a * Real.exp (-(1 / 4)) ≤ ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgFac a u := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hshalf : Real.sqrt a ≤ 1 / 2 := by
    nlinarith [Real.sqrt_nonneg a]
  -- lower bound on the small box
  have hbox : 2 * Real.sqrt a * Real.exp (-(1 / 4))
      ≤ ∫ u in Set.Icc (-Real.sqrt a) (Real.sqrt a), tgFac a u := by
    have hconst : ∫ _u in Set.Icc (-Real.sqrt a) (Real.sqrt a), Real.exp (-(1 / 4) : ℝ)
        = 2 * Real.sqrt a * Real.exp (-(1 / 4)) := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
        show Real.sqrt a - -Real.sqrt a = 2 * Real.sqrt a by ring,
        ENNReal.toReal_ofReal (by positivity)]
      simp [smul_eq_mul]
    rw [← hconst]
    refine setIntegral_mono_on (continuous_const.integrableOn_Icc)
      ((continuous_tgFac a).integrableOn_Icc) measurableSet_Icc fun u hu => ?_
    have hu2 : u ^ 2 ≤ a := by
      have h1 : -Real.sqrt a ≤ u := hu.1
      have h2 : u ≤ Real.sqrt a := hu.2
      nlinarith
    refine le_trans ?_ (tgFac_ge_gauss ha u)
    refine Real.exp_le_exp.2 ?_
    have hle : u ^ 2 / (4 * a) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * a)]
      nlinarith
    linarith
  -- and the small box sits inside the fundamental interval
  have hsub : Set.Icc (-Real.sqrt a) (Real.sqrt a) ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) :=
    Set.Icc_subset_Icc (by linarith) hshalf
  have hmono : ∫ u in Set.Icc (-Real.sqrt a) (Real.sqrt a), tgFac a u
      ≤ ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgFac a u :=
    setIntegral_mono_set ((continuous_tgFac a).integrableOn_Icc)
      (Filter.Eventually.of_forall fun u => (tgFac_nonneg a u))
      (Filter.Eventually.of_forall fun u hu => hsub hu)
  linarith

/-- **The separable cell lower bound.** -/
theorem cellInt_prod_ge {f : Fin 3 → ℝ → ℝ} {c : Fin 3 → ℝ} (b : E3)
    (hc : ∀ j, 0 ≤ c j) (hper : ∀ j, Function.Periodic (f j) 1)
    (hge : ∀ j, c j ≤ ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f j u) :
    (∏ j, c j) ≤ cellInt (fun x : E3 => ∏ j, f j (x j - b j)) := by
  rw [cellInt_prod]
  have hcongr : (∏ j, ∫ u in Set.Icc (0 : ℝ) 1, f j (u - b j))
      = ∏ j, ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f j u :=
    Finset.prod_congr rfl fun j _ => integral_Icc01_periodic_shift (hper j) (b j)
  rw [hcongr]
  exact Finset.prod_le_prod (fun j _ => hc j) fun j _ => hge j

/-- **`C52`, positive half.  The weight really concentrates — and no more.**
The cell mass of `Φ_a` is bounded *below* by `8e^{−3/4}a^{3/2}`, matching the
upper bound `π³√(π³)a^{3/2}` in order.  So the concentration ratio is exactly
of order `a^{3/2}`: the weight is a genuine detector, not a vanishing one. -/
theorem cellInt_torusGauss_ge {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (x0 : E3) (t : ℝ) :
    8 * Real.exp (-(3 / 4)) * (a * Real.sqrt a)
      ≤ cellInt (fun x => torusGauss a x0 (t, x)) := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hcong : cellInt (fun x : E3 => torusGauss a x0 (t, x))
      = cellInt (fun x : E3 => ∏ j, tgFac a (x j - x0 j)) :=
    cellInt_congr fun x => torusGauss_eq_prod a x0 (t, x)
  rw [hcong]
  have h := cellInt_prod_ge (f := fun _ => tgFac a)
    (c := fun _ => 2 * Real.sqrt a * Real.exp (-(1 / 4))) x0
    (fun _ => by positivity) (fun _ => tgFac_periodic a) fun _ => integral_tgFac_ge ha ha4
  refine le_trans (le_of_eq ?_) h
  have hexp : Real.exp (-(3 / 4) : ℝ) = Real.exp (-(1 / 4)) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hcube : a * Real.sqrt a = Real.sqrt a * Real.sqrt a * Real.sqrt a := by
    have hmm : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    rw [hmm]
  rw [Fin.prod_univ_three, hexp, hcube]
  ring

/-! ## The no-go: concentration alone cannot close the budget -/

/-- **`C52`, negative half.**  This is a no-go for the *sup-unweighted* estimate
only: see `ClayNS.gaussianGradientWeightedAbsorption`, where keeping the
Gaussian through Young's inequality replaces this term by weighted terms of size
`O(a^{3/2}) + O(√a)`.

The unweighted gradient term of the linear budget
is amplified by exactly `a^{-1}`.  So if the unweighted level-set quantity `K₀`
stays bounded below by a positive number, that term exceeds any prescribed
bound for all sufficiently small concentration scales — no choice of `a` makes
the whole budget small by concentration alone. -/
theorem gaussian_gradient_term_blows_up {A B K0 M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hK0 : 0 < K0) (hM : 0 < M) :
    ∃ a0 : ℝ, 0 < a0 ∧ ∀ a : ℝ, 0 < a → a < a0 →
      M < 9 * A * B ^ 2 * (1 / (4 * π * a)) * K0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set c := 9 * A * B ^ 2 * K0 / (4 * π) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨c / M, by positivity, fun a ha hlt => ?_⟩
  have hrw : 9 * A * B ^ 2 * (1 / (4 * π * a)) * K0 = c / a := by
    rw [hc]; field_simp
  rw [hrw, lt_div_iff₀ ha]
  have h2 : M * (c / M) = c := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hM)]
  linarith [mul_lt_mul_of_pos_left hlt hM]

/-! ## The target statement for `C52`, recorded but not proved -/

/-- **`GaussianModulusDefectPropagation`.**  The statement the tranche proposes:
a pointwise excess of the increment modulus at the defect point forces, over a
backward window of length comparable to the concentration scale, a definite
weighted transverse dissipation bill, up to an error that vanishes with the
scale.

This is recorded as a `Prop` in the vocabulary of the development.  It is
**not** proved, and nothing else in this development assumes it.  The no-go
above shows why the concentrated weight alone does not deliver it: the missing
input is control of the *unweighted* level-set quantity. -/
def GaussianModulusDefectPropagation (nu lam delta : ℝ) : Prop :=
  ∀ V : STime → E3, ContDiff ℝ (⊤ : ℕ∞) V → SpacePeriodic V →
    (∀ z : STime, divg V z = 0) →
    ∀ (h : E3) (z₀ : STime), lam + delta ≤ incrQuad h V z₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
        c * (a * Real.sqrt a)
          ≤ cellInt (fun x => torusGauss a z₀.2 (z₀.1, x) * incrDissip h V (z₀.1, x))
            + nu * (tgLapC * Real.sqrt a)

end ClayNS
