/-
# Choosing the truncation level: `C55` applied to the modulus residual

`ModulusLevelSplit.lean` shows that the only surviving marginal (radial)
stretching channel of the profile entropy `β(q) = ζ(r_ε)` is

  `Res_ζ = (u·δ_hu)·(Σ_j δ_hu_j ∂_jq)·ζ″(r_ε)/r_ε²`   (`ClayNS.modProfileResidual`),

which vanishes wherever the profile is affine.  For a *smoothed* truncation
`ζ_{λ,δ}` the residual lives in the level annulus `λ < r_ε < λ+δ` and its size
there is `O(δ^{-1})`.

This file applies the level-annulus pigeonhole `C55` to that residual.  Since
the density

  `D_ε = |u·δ_hu|·|Σ_j δ_hu_j ∂_jq|/r_ε²`

does **not** depend on the level, the pigeonhole selects a level `λ_*` in any
prescribed window at which the whole residual costs at most the *average* of the
density:

  `∫_cell |Res_{ζ_{λ_*,δ}}| ≤ (λ₁−λ₀)^{-1}∫_cell D_ε`,

uniformly in the smoothing width `δ`.  This is exactly what the De Giorgi
iteration needs: it never requires *every* level, only one level in a prescribed
range.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ModulusLevelSplit
import RequestProject.NavierStokes.LevelAnnulusPigeonhole

open Real MeasureTheory Set

noncomputable section

namespace ClayNS

/-- The level-independent density of the marginal modulus residual. -/
def modResidualDensity (eps : ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => |incrPair h V z| * |∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z|
      / (incrModEps eps h V z) ^ 2

lemma modResidualDensity_nonneg {eps : ℝ} (heps : 0 < eps) (h : E3) (V : STime → E3)
    (z : STime) : 0 ≤ modResidualDensity eps h V z := by
  have hr : (0:ℝ) < incrModEps eps h V z := incrModEps_pos' heps h V z
  unfold modResidualDensity
  positivity

lemma contDiff_modResidualBase {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => incrPair h V z * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  exact (contDiff_incrPair h hV).mul
    (ContDiff.sum fun j _ => (contDiff_incrComp h hV j).mul (contDiff_dvec _ hq _))

lemma continuous_modResidualDensity {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    Continuous fun x : E3 => modResidualDensity eps h V (t, x) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (incrPair h V) := contDiff_incrPair h hV
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z) :=
    ContDiff.sum fun j _ => (contDiff_incrComp h hV j).mul (contDiff_dvec _ hq _)
  have hcont : Continuous fun z : STime => modResidualDensity eps h V z := by
    refine ((hnum.continuous.abs).mul (hsum.continuous.abs)).div
      ((hmod.continuous).pow 2) fun z => ?_
    exact pow_ne_zero 2 (ne_of_gt (incrModEps_pos' heps h V z))
  exact hcont.comp (by fun_prop)

/-- The residual factorises as the level-independent density times the profile's
second derivative evaluated at the modulus. -/
lemma abs_modProfileResidual_eq {eps : ℝ} (heps : 0 < eps) (z2 : ℝ → ℝ) (h : E3)
    (V : STime → E3) (z : STime) :
    |modProfileResidual eps z2 h V z|
      = modResidualDensity eps h V z * |z2 (incrModEps eps h V z)| := by
  have hr : (0:ℝ) < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hr2 : (0:ℝ) < (incrModEps eps h V z) ^ 2 := by positivity
  unfold modProfileResidual modResidualDensity
  rw [abs_mul, abs_mul, abs_div, abs_of_pos hr2]
  ring

/-- **`C55` for the marginal modulus residual.**  For a family of smoothed
truncation profiles whose second derivatives are dominated by the annulus kernel
of width `δ`, there is a level `λ_*` in the prescribed window at which the
marginal residual of the modulus split costs at most the level average of the
(level-independent) residual density.  No power of `δ` is lost. -/
theorem exists_level_modulus_residual_bound {eps : ℝ} (heps : 0 < eps)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {delta : ℝ} (hd : 0 < delta) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) (hw1 : ∫ u, w u ≤ 1)
    {Z : ℝ → ℝ → ℝ} (hZc : ∀ l, Continuous (Z l))
    (hdom : ∀ l s, |Z l s| ≤ annulusKernel delta w l s)
    {lam0 lam1 : ℝ} (hlt : lam0 < lam1) (t : ℝ) :
    ∃ lams ∈ Set.Icc lam0 lam1,
      cellInt (fun x => |modProfileResidual eps (Z lams) h V (t, x)|)
        ≤ cellInt (fun x => modResidualDensity eps h V (t, x)) / (lam1 - lam0) := by
  have hrc : Continuous fun x : E3 => incrModEps eps h V (t, x) :=
    continuous_slice (contDiff_incrModEps heps hV) t
  obtain ⟨lams, hmem, hle⟩ := exists_level_smoothing_annulus_bound
    (G := fun x : E3 => modResidualDensity eps h V (t, x))
    (r := fun x : E3 => incrModEps eps h V (t, x)) (Z := Z) hd hw hw0 hwi hw1
    (continuous_modResidualDensity heps hV t)
    (fun x => modResidualDensity_nonneg heps h V (t, x)) hrc
    (fun l => (hZc l).comp hrc) hdom hlt
  refine ⟨lams, hmem, ?_⟩
  refine le_trans (le_of_eq (cellInt_congr fun x => ?_)) hle
  exact abs_modProfileResidual_eq heps (Z lams) h V (t, x)

/-- **The modulus Caccioppoli budget at a selected level.**  Combining the
profile budget of `ClayNS.modulusEps_profile_cell_budget` with the level
selection above: for a family of smoothed truncations `ζ_λ` with nonnegative
derivative and second derivative dominated by the annulus kernel of width `δ`,
there is a level `λ_*` in the prescribed window at which the marginal residual
costs only the level average of the residual density — no `δ^{-1}`.  The two
good terms are unchanged. -/
theorem exists_level_modulusEps_profile_cell_budget {nu eps : ℝ} (hnu : 0 < nu)
    (heps : 0 < eps) {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hVper : SpacePeriodic V) (hdiv : ∀ z : STime, divg V z = 0)
    {zd Z : ℝ → ℝ → ℝ} (hzdc : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (zd l))
    (hZcd : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Z l))
    (hderiv : ∀ l s, HasDerivAt (zd l) (Z l s) s) (hzdnn : ∀ l s, 0 ≤ zd l s)
    {delta : ℝ} (hd : 0 < delta) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) (hw1 : ∫ u, w u ≤ 1)
    (hdom : ∀ l s, |Z l s| ≤ annulusKernel delta w l s)
    {lam0 lam1 : ℝ} (hlt : lam0 < lam1) (t : ℝ) :
    ∃ lams ∈ Set.Icc lam0 lam1,
      cellInt (fun x => modProfileWeight eps (zd lams) h V (t, x) * incrStretch h V (t, x))
        ≤ nu / 2 * cellInt (fun x =>
              zd lams (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
          + 1 / (2 * nu) * cellInt (fun x =>
              zd lams (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2))
          + cellInt (fun x => modResidualDensity eps h V (t, x)) / (lam1 - lam0) := by
  obtain ⟨lams, hmem, hle⟩ := exists_level_modulus_residual_bound (h := h) heps hV hd hw hw0
    hwi hw1 (Z := Z) (fun l => (hZcd l).continuous) hdom hlt t
  refine ⟨lams, hmem, ?_⟩
  have hbudget := modulusEps_profile_cell_budget (nu := nu) (eps := eps) (h := h) hnu heps
    (hzdc lams) (hZcd lams) (hderiv lams) (hzdnn lams) hV hVper hdiv t
  linarith [hbudget, hle]

end ClayNS
