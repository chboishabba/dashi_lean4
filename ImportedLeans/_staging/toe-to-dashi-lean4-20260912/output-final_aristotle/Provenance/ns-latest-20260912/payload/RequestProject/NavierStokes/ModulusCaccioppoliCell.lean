/-
# The integrated modulus Caccioppoli budget

`IncrementModulusGram.lean` and `IncrementModulusCancellation.lean` produced the
pointwise picture in the modulus variable `r = |δ_hu|`:

* the radial (marginal) stretching channel cancels exactly for the modulus
  entropy, and
* the surviving transverse channel is absorbed by the transverse viscous
  surplus, leaving a source **linear** in `r`.

This file integrates that picture over the periodicity cell.  On the cell the
transfer flux is an exact divergence and integrates away
(`ClayNS.cellInt_divg_eq_zero`), so the whole weighted stretching source obeys

`∫_cell r^{-1}·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell (|∇δ_hu|²−|∇|δ_hu||²)/r + (1/2ν)∫_cell r|u|²`
                                     (`ClayNS.modulus_caccioppoli_cell_budget`)

with **no** bound on `∇u`, **no** critical `L^{5/2}` norm of the strain and
**no** level-set exponent `θ`: the two ingredients that the `q`-variable route
needed (`ClayNS.IncrementStretchingDepletionGate`) are replaced by the exact
Gram geometry of the increment.

The one hypothesis added is the non-degeneracy `δ_hu ≠ 0`, i.e.
`0 < q = ½|δ_hu|²` everywhere: the modulus entropy `r = √(2q)` is singular
exactly where the increment vanishes, and only there.  Removing this hypothesis
is the remaining technical step of the modulus route
(`ClayNS.incrModEpsWeight` is the regularization it calls for).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementModulusCancellation

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The modulus weight of a non-degenerate increment -/

/-- The exact modulus-entropy weight `W = β'(q) = 1/r`. -/
def incrModWeight (h : E3) (V : STime → E3) : STime → ℝ :=
  fun w => modEntropyDeriv (incrQuad h V w)

lemma incrModWeight_apply (h : E3) (V : STime → E3) (z : STime) :
    incrModWeight h V z = 1 / incrMod h V z := rfl

/-- The modulus of a non-vanishing increment is smooth. -/
theorem contDiff_incrMod {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hpos : ∀ z : STime, 0 < incrQuad h V z) : ContDiff ℝ (⊤ : ℕ∞) (incrMod h V) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => 2 * incrQuad h V w) z :=
    (contDiff_const.mul (contDiff_incrQuad h hV)).contDiffAt
  have hgpos : 0 < 2 * incrQuad h V z := by have := hpos z; linarith
  exact (Real.contDiffAt_sqrt (ne_of_gt hgpos)).comp z hg

/-- The modulus weight of a non-vanishing increment is smooth. -/
theorem contDiff_incrModWeight {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hpos : ∀ z : STime, 0 < incrQuad h V z) :
    ContDiff ℝ (⊤ : ℕ∞) (incrModWeight h V) := by
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrMod h V) := contDiff_incrMod hV hpos
  have hform : incrModWeight h V = fun w => (incrMod h V w)⁻¹ := by
    funext w; simp [incrModWeight, modEntropyDeriv, incrMod, one_div]
  rw [hform, contDiff_iff_contDiffAt]
  intro z
  exact hmod.contDiffAt.inv (ne_of_gt (incrMod_pos (hpos z)))

/-- Gradient of the modulus weight: `∇W = β''(q)∇q`. -/
lemma incrModWeight_grad {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hpos : ∀ z : STime, 0 < incrQuad h V z) (z : STime) (a : STime) :
    dvec a (incrModWeight h V) z
      = modEntropySecond (incrQuad h V z) * dvec a (incrQuad h V) z :=
  dvec_comp_scalar_at (contDiff_incrQuad h hV) (modEntropy_deriv_hasDerivAt (hpos z)) a

lemma spacePeriodic_incrModWeight {h : E3} {V : STime → E3} (hVper : SpacePeriodic V) :
    SpacePeriodic (incrModWeight h V) := by
  intro z j
  simp only [incrModWeight]
  rw [spacePeriodic_incrQuad h hVper z j]

/-! ## The pointwise budget for the exact modulus weight -/

/-- With the exact modulus weight the stretching source, minus the exact
divergence of the transfer flux, is bounded by half the transverse dissipation
plus a source linear in the modulus. -/
theorem modulus_weight_pointwise_bound {nu : ℝ} (hnu : 0 < nu) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0)
    (hpos : ∀ z : STime, 0 < incrQuad h V z) (z : STime) :
    |incrModWeight h V z * incrStretch h V z
        - divg (fun w => (incrModWeight h V w * incrPair h V w) • incrVec h V w) z|
      ≤ nu / 2 * (incrTransDissip h V z / incrMod h V z)
        + incrMod h V z * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (incrModWeight h V) := contDiff_incrModWeight hV hpos
  have hODE : modEntropySecond (incrQuad h V z)
      + (1 / incrMod h V z) / (2 * incrQuad h V z) = 0 := by
    have h0 := modulus_entropy_ode (hpos z)
    have hval : modEntropyDeriv (incrQuad h V z) = 1 / incrMod h V z := rfl
    rwa [hval] at h0
  exact adjoint_modulus_caccioppoli_pointwise hnu hV hW hdiv (hpos z)
    (incrModWeight_apply h V z) (fun j => incrModWeight_grad hV hpos z (0, ee j)) hODE

/-! ## The integrated budget on the periodicity cell -/

/-- **The modulus Caccioppoli budget on the cell.**  For a smooth periodic
divergence-free velocity whose increment never vanishes,

`∫_cell r^{-1}·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell (|∇δ_hu|² − |∇|δ_hu||²)/r + (1/2ν)∫_cell r|u|²`.

The stretching obstruction is therefore controlled by half of the transverse
dissipation plus a source **linear** in the De Giorgi variable `r = |δ_hu|`.
No bound on `∇u`, no critical strain norm and no level-set exponent `θ` are
used: the exponent gate of the `q`-variable route is not needed in the modulus
variable. -/
theorem modulus_caccioppoli_cell_budget {nu : ℝ} (hnu : 0 < nu) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0) (hpos : ∀ z : STime, 0 < incrQuad h V z) (t : ℝ) :
    cellInt (fun x => incrModWeight h V (t, x) * incrStretch h V (t, x))
      ≤ nu / 2 * cellInt (fun x => incrTransDissip h V (t, x) / incrMod h V (t, x))
        + 1 / (2 * nu) * cellInt (fun x => incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := by
  classical
  have hW : ContDiff ℝ (⊤ : ℕ∞) (incrModWeight h V) := contDiff_incrModWeight hV hpos
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrMod h V) := contDiff_incrMod hV hpos
  have hstretch : ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) := contDiff_incrStretch h hV
  set F : STime → E3 :=
    fun w => (incrModWeight h V w * incrPair h V w) • incrVec h V w with hF
  have hFC : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hW.mul (contDiff_incrPair h hV)).smul (contDiff_incrVec h hV)
  have hFper : SpacePeriodic F := by
    intro z j
    simp only [hF]
    rw [spacePeriodic_incrModWeight (h := h) hVper z j,
      spacePeriodic_incrPair h hVper z j, spacePeriodic_incrVec h hVper z j]
  -- continuity of the slices
  have hslice : Continuous (fun x : E3 => ((t, x) : STime)) :=
    continuous_const.prodMk continuous_id
  have hc1 : Continuous (fun x : E3 => incrModWeight h V (t, x) * incrStretch h V (t, x)) :=
    (hW.continuous.comp hslice).mul (hstretch.continuous.comp hslice)
  have hcdiv : Continuous (fun x : E3 => divg F (t, x)) :=
    (contDiff_divgFun hFC).continuous.comp hslice
  have hg : Continuous (fun x : E3 => incrModWeight h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x)) := hc1.sub hcdiv
  have hcT : Continuous (fun x : E3 => incrTransDissip h V (t, x)) := by
    have hdis : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
    have hrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => ∑ j, (dvec (0, ee j) (incrMod h V) w) ^ 2) :=
      ContDiff.sum fun j _ => (contDiff_dvec _ hmod _).pow 2
    exact ((hdis.sub hrad).continuous).comp hslice
  have hcr : Continuous (fun x : E3 => incrMod h V (t, x)) := hmod.continuous.comp hslice
  have hcRHS : Continuous (fun x : E3 =>
      nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))
        + incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)) := by
    have hne : ∀ x : E3, incrMod h V (t, x) ≠ 0 := fun x => ne_of_gt (incrMod_pos (hpos (t, x)))
    have hcU : Continuous (fun x : E3 => ∑ a, (V (t, x) a) ^ 2) :=
      continuous_finset_sum _ fun a _ =>
        (((contDiff_coord V hV a).continuous).comp hslice).pow 2
    exact (continuous_const.mul (hcT.div hcr hne)).add ((hcr.mul hcU).div_const _)
  -- the divergence integrates away
  have hdivzero : cellInt (fun x => divg F (t, x)) = 0 := cellInt_divg_eq_zero F hFC hFper t
  have hsplit : cellInt (fun x => incrModWeight h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x))
      = cellInt (fun x => incrModWeight h V (t, x) * incrStretch h V (t, x)) := by
    rw [cellInt_sub hc1 hcdiv, hdivzero, sub_zero]
  -- the pointwise bound, integrated
  have hbound : |cellInt (fun x => incrModWeight h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x))|
      ≤ cellInt (fun x => nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))
          + incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)) :=
    abs_cellInt_le hg hcRHS fun x =>
      modulus_weight_pointwise_bound hnu hV hdiv hpos (t, x)
  rw [hsplit] at hbound
  have hle := (abs_le.mp hbound).2
  have hRHS : cellInt (fun x => nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))
        + incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu))
      = nu / 2 * cellInt (fun x => incrTransDissip h V (t, x) / incrMod h V (t, x))
        + 1 / (2 * nu) * cellInt (fun x => incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := by
    have hne : ∀ x : E3, incrMod h V (t, x) ≠ 0 := fun x => ne_of_gt (incrMod_pos (hpos (t, x)))
    have hcT' : Continuous (fun x : E3 => incrTransDissip h V (t, x) / incrMod h V (t, x)) :=
      hcT.div hcr hne
    have hcU : Continuous (fun x : E3 => ∑ a, (V (t, x) a) ^ 2) :=
      continuous_finset_sum _ fun a _ =>
        (((contDiff_coord V hV a).continuous).comp hslice).pow 2
    have h1 : Continuous (fun x : E3 =>
        nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))) :=
      continuous_const.mul hcT'
    have h2 : Continuous (fun x : E3 =>
        1 / (2 * nu) * (incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2))) :=
      continuous_const.mul (hcr.mul hcU)
    have hcongr : ∀ x : E3, nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))
        + incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
        = nu / 2 * (incrTransDissip h V (t, x) / incrMod h V (t, x))
          + 1 / (2 * nu) * (incrMod h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := fun x => by
      ring
    rw [cellInt_congr hcongr, cellInt_add h1 h2, cellInt_const_mul, cellInt_const_mul]
  rw [hRHS] at hle
  exact hle

end ClayNS
