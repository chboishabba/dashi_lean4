/-
# The level-set form of the modulus cancellation

`ModulusEpsCaccioppoli.lean` proves the exact cancellation of the marginal
radial stretching channel for the *modulus* entropy `ζ(r) = r`.  The De Giorgi
scheme, however, does not run on `r`; it runs on the truncated level function
`ζ_λ(r) = (r − λ)_+`.  This file identifies exactly how much of the cancellation
survives truncation.

The computation is a one-line consequence of the general split
`ClayNS.increment_stretching_radial_split_gen`.  For a scalar *profile*
`ζ : ℝ → ℝ` the associated entropy is `β(q) = ζ(r_ε)` with
`r_ε = √(2q + ε²)`, and the corresponding weight is

  `W = β'(q) = ζ'(r_ε)/r_ε`.

Its radial factor is

  `β'' + β'/r_ε² = ζ''(r_ε)/r_ε²`,

so the marginal channel is governed by the **second derivative of the profile
alone** (`ClayNS.increment_modulus_profile_split`).  Consequences:

* `ζ` affine ⟹ the radial channel cancels identically.  The modulus `ζ = id` is
  the case already treated; `ζ_λ(r) = r − λ` is affine too, so the cancellation
  is *unchanged by the truncation constant*.
* For a general profile the residual is
  `ClayNS.modProfileResidual`, and it is supported exactly on
  `{ζ''(r_ε) ≠ 0}` (`ClayNS.increment_modulus_profile_cancellation_of_flat`).
  For a smoothed truncation whose second derivative lives in a thin annulus
  `λ < r < λ + δ`, the marginal stretching therefore only sees that annulus.

The transverse channel behaves as before: with `ζ' ≥ 0` the surviving pairing is
absorbed by the transverse viscous surplus, with the profile derivative as the
only weight (`ClayNS.modulusEps_profile_transverse_absorption`), giving the
integrated budget `ClayNS.modulusEps_profile_cell_budget`

  `∫ (ζ'(r_ε)/r_ε)·δ_hu·(δ_hu·∇)u
      ≤ (ν/2)∫ ζ'(r_ε)·T_ε + (1/2ν)∫ ζ'(r_ε)|u|² + ∫ |Res_ζ|`,

which reduces to `ClayNS.modulusEps_caccioppoli_cell_budget` for `ζ = id`
(`Res_id = 0`).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ModulusEpsCaccioppoli

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The profile weight -/

/-- The weight attached to a scalar profile `ζ` with derivative `z1 = ζ'`:
`W = ζ'(r_ε)/r_ε`, i.e. `β'(q)` for the entropy `β(q) = ζ(r_ε)`. -/
def modProfileWeight (eps : ℝ) (z1 : ℝ → ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun w => z1 (incrModEps eps h V w) / incrModEps eps h V w

/-- The marginal residual left over by a non-affine profile: it carries the
factor `ζ''(r_ε)` and hence vanishes wherever the profile is affine. -/
def modProfileResidual (eps : ℝ) (z2 : ℝ → ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
      * (z2 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 2)

lemma contDiff_modProfileWeight {eps : ℝ} (heps : 0 < eps) {z1 : ℝ → ℝ}
    (hz1c : ContDiff ℝ (⊤ : ℕ∞) z1) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (modProfileWeight eps z1 h V) := by
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  exact (hz1c.comp hmod).div hmod fun z => ne_of_gt (incrModEps_pos' heps h V z)

lemma spacePeriodic_modProfileWeight {eps : ℝ} {z1 : ℝ → ℝ} {h : E3} {V : STime → E3}
    (hVper : SpacePeriodic V) : SpacePeriodic (modProfileWeight eps z1 h V) := by
  intro z j
  simp only [modProfileWeight]
  rw [spacePeriodic_incrModEps (eps := eps) (h := h) hVper z j]

/-- The gradient of the profile weight is proportional to `∇q`, with factor
`ζ''(r)/r² − ζ'(r)/r³`. -/
lemma modProfileWeight_grad {eps : ℝ} (heps : 0 < eps) {z1 z2 : ℝ → ℝ}
    (hz1 : ∀ s, HasDerivAt z1 (z2 s) s) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) (a : STime) :
    dvec a (modProfileWeight eps z1 h V) z
      = (z2 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 2
          - z1 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 3)
        * dvec a (incrQuad h V) z := by
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hrpos : 0 < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hrne : incrModEps eps h V z ≠ 0 := ne_of_gt hrpos
  have hG : HasDerivAt (fun s : ℝ => z1 s / s)
      ((z2 (incrModEps eps h V z) * incrModEps eps h V z - z1 (incrModEps eps h V z) * 1)
        / (incrModEps eps h V z) ^ 2) (incrModEps eps h V z) :=
    (hz1 _).div (hasDerivAt_id _) hrne
  have hchain := dvec_comp_scalar_at (Q := incrModEps eps h V) hmod
    (f := fun s : ℝ => z1 s / s) hG a
  have hdr : dvec a (incrModEps eps h V) z
      = dvec a (incrQuad h V) z / incrModEps eps h V z := by
    rw [dvec_incrModEps heps hV z a]
    congr 1
    exact (dvec_quad (incrComp h V) (fun i => contDiff_incrComp h hV i) a z).symm
  have hform : modProfileWeight eps z1 h V
      = fun w => (fun s : ℝ => z1 s / s) (incrModEps eps h V w) := rfl
  rw [hform, hchain, hdr]
  field_simp

/-! ## The split -/

/-- **The profile split.**  For the entropy `β(q) = ζ(r_ε)` the stretching
source is an exact divergence, the transverse pairing, and a marginal residual
carrying the factor `ζ''(r_ε)`. -/
theorem increment_modulus_profile_split {eps : ℝ} (heps : 0 < eps) {z1 z2 : ℝ → ℝ}
    (hz1c : ContDiff ℝ (⊤ : ℕ∞) z1) (hz1 : ∀ s, HasDerivAt z1 (z2 s) s)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    modProfileWeight eps z1 h V z * incrStretch h V z
      = divg (fun w => (modProfileWeight eps z1 h V w * incrPair h V w) • incrVec h V w) z
        - (z1 (incrModEps eps h V z) / incrModEps eps h V z) * incrPerpPairEps eps h V z
        - modProfileResidual eps z2 h V z := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (modProfileWeight eps z1 h V) :=
    contDiff_modProfileWeight heps hz1c hV
  have hR : (0:ℝ) < 2 * incrQuad h V z + eps ^ 2 := incrModEps_pos heps h V z
  have hrpos : 0 < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hrsq : (incrModEps eps h V z) ^ 2 = 2 * incrQuad h V z + eps ^ 2 :=
    incrModEps_sq heps h V z
  have hWz : modProfileWeight eps z1 h V z
      = z1 (incrModEps eps h V z) / incrModEps eps h V z := rfl
  have hdW := modProfileWeight_grad (h := h) heps hz1 hV z
  have hsplit := increment_stretching_radial_split_gen (W := modProfileWeight eps z1 h V)
    hV hW hdiv z (R := 2 * incrQuad h V z + eps ^ 2) (ne_of_gt hR) hWz
    (fun j => hdW (0, ee j))
  have hcoef : (z2 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 2
        - z1 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 3)
      + (z1 (incrModEps eps h V z) / incrModEps eps h V z)
          / (2 * incrQuad h V z + eps ^ 2)
      = z2 (incrModEps eps h V z) / (incrModEps eps h V z) ^ 2 := by
    rw [← hrsq]
    field_simp
    ring
  rw [hsplit, hcoef]
  simp only [incrPerpPairEps, modProfileResidual]

/-- **The cancellation survives on the flat part of the profile.**  Wherever
`ζ''(r_ε) = 0` — in particular for every affine profile, so for the truncation
`ζ_λ(r) = r − λ` on the whole active set — the marginal radial channel cancels
identically and only the transverse pairing remains. -/
theorem increment_modulus_profile_cancellation_of_flat {eps : ℝ} (heps : 0 < eps)
    {z1 z2 : ℝ → ℝ} (hz1c : ContDiff ℝ (⊤ : ℕ∞) z1) (hz1 : ∀ s, HasDerivAt z1 (z2 s) s)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hdiv : ∀ z : STime, divg V z = 0) {z : STime}
    (hflat : z2 (incrModEps eps h V z) = 0) :
    modProfileWeight eps z1 h V z * incrStretch h V z
      = divg (fun w => (modProfileWeight eps z1 h V w * incrPair h V w) • incrVec h V w) z
        - (z1 (incrModEps eps h V z) / incrModEps eps h V z)
            * incrPerpPairEps eps h V z := by
  rw [increment_modulus_profile_split heps hz1c hz1 hV hdiv z]
  simp [modProfileResidual, hflat]

/-! ## The transverse absorption for a profile -/

/-- **Young absorption with the profile derivative as weight.**  For `ζ' ≥ 0`
the surviving transverse pairing is absorbed by the transverse viscous surplus,
with a source *linear in* `ζ'(r_ε)` — no factor of `r_ε` and no bound on `∇u`. -/
theorem modulusEps_profile_transverse_absorption {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    {z1 : ℝ → ℝ} (hz1nn : ∀ s, 0 ≤ z1 s) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    (z1 (incrModEps eps h V z) / incrModEps eps h V z) * |incrPerpPairEps eps h V z|
      ≤ nu / 2 * (z1 (incrModEps eps h V z) * incrTransDissipEps eps h V z)
        + z1 (incrModEps eps h V z) * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  have hrpos : 0 < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hT : 0 ≤ incrTransDissipEps eps h V z := incrTransDissipEps_nonneg heps hV z
  have hU : (0:ℝ) ≤ ∑ a, (V z a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbase := incrPerpPairEps_abs_le (h := h) heps hV z
  set r := incrModEps eps h V z with hrdef
  set U := Real.sqrt (∑ a, (V z a) ^ 2) with hUdef
  set S := Real.sqrt (incrTransDissipEps eps h V z) with hSdef
  have hz1 : 0 ≤ z1 r := hz1nn r
  -- `(ζ'(r)/r)·|P| ≤ (ζ'(r)/r)·U·r·S = ζ'(r)·U·S`
  have hstep : (z1 r / r) * |incrPerpPairEps eps h V z| ≤ z1 r * (U * S) := by
    have hcoef : 0 ≤ z1 r / r := div_nonneg hz1 hrpos.le
    calc (z1 r / r) * |incrPerpPairEps eps h V z|
        ≤ (z1 r / r) * (U * (r * S)) := mul_le_mul_of_nonneg_left hbase hcoef
      _ = z1 r * (U * S) := by field_simp
  have hyoung : z1 r * (U * S) ≤ nu / 2 * (z1 r * S ^ 2) + z1 r * U ^ 2 / (2 * nu) := by
    have hid : nu / 2 * S ^ 2 + U ^ 2 / (2 * nu) - U * S = (nu * S - U) ^ 2 / (2 * nu) := by
      field_simp
      ring
    have hnn : 0 ≤ (nu * S - U) ^ 2 / (2 * nu) :=
      div_nonneg (sq_nonneg _) (by linarith)
    have hkey : U * S ≤ nu / 2 * S ^ 2 + U ^ 2 / (2 * nu) := by
      rw [← sub_nonneg, hid]; exact hnn
    have hmul := mul_le_mul_of_nonneg_left hkey hz1
    calc z1 r * (U * S) ≤ z1 r * (nu / 2 * S ^ 2 + U ^ 2 / (2 * nu)) := hmul
      _ = nu / 2 * (z1 r * S ^ 2) + z1 r * U ^ 2 / (2 * nu) := by ring
  have hS2 : S ^ 2 = incrTransDissipEps eps h V z := Real.sq_sqrt hT
  have hU2 : U ^ 2 = ∑ a, (V z a) ^ 2 := Real.sq_sqrt hU
  rw [hS2, hU2] at hyoung
  exact le_trans hstep hyoung

/-! ## The integrated profile budget -/

lemma contDiff_modProfileResidual {eps : ℝ} (heps : 0 < eps) {z2 : ℝ → ℝ}
    (hz2c : ContDiff ℝ (⊤ : ℕ∞) z2) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (modProfileResidual eps z2 h V) := by
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : STime => ∑ j, incrComp h V j w * dvec (0, ee j) (incrQuad h V) w) :=
    ContDiff.sum fun j _ => (contDiff_incrComp h hV j).mul (contDiff_dvec _ hQ _)
  have hfrac : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : STime => z2 (incrModEps eps h V w) / (incrModEps eps h V w) ^ 2) :=
    (hz2c.comp hmod).div (hmod.pow 2) fun z =>
      pow_ne_zero 2 (ne_of_gt (incrModEps_pos' heps h V z))
  exact ((contDiff_incrPair h hV).mul hsum).mul hfrac

/-- **The integrated profile budget on the cell.**  For any smooth profile `ζ`
with `ζ' ≥ 0`,

`∫_cell (ζ'(r_ε)/r_ε)·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell ζ'(r_ε)·T_ε + (1/2ν)∫_cell ζ'(r_ε)|u|² + ∫_cell |Res_ζ|`,

with `Res_ζ` carrying the factor `ζ''(r_ε)`.  For `ζ = id` the residual vanishes
identically; for a smoothed level truncation it is supported in the level
annulus. -/
theorem modulusEps_profile_cell_budget {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    {z1 z2 : ℝ → ℝ} (hz1c : ContDiff ℝ (⊤ : ℕ∞) z1) (hz2c : ContDiff ℝ (⊤ : ℕ∞) z2)
    (hz1 : ∀ s, HasDerivAt z1 (z2 s) s) (hz1nn : ∀ s, 0 ≤ z1 s)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    cellInt (fun x => modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x))
      ≤ nu / 2 * cellInt (fun x =>
            z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
        + 1 / (2 * nu) * cellInt (fun x =>
            z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2))
        + cellInt (fun x => |modProfileResidual eps z2 h V (t, x)|) := by
  classical
  have hslice : Continuous (fun x : E3 => ((t, x) : STime)) :=
    continuous_const.prodMk continuous_id
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hW : ContDiff ℝ (⊤ : ℕ∞) (modProfileWeight eps z1 h V) :=
    contDiff_modProfileWeight heps hz1c hV
  have hstretch : ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) := contDiff_incrStretch h hV
  have hRes : ContDiff ℝ (⊤ : ℕ∞) (modProfileResidual eps z2 h V) :=
    contDiff_modProfileResidual heps hz2c hV
  set F : STime → E3 :=
    fun w => (modProfileWeight eps z1 h V w * incrPair h V w) • incrVec h V w with hF
  have hFC : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hW.mul (contDiff_incrPair h hV)).smul (contDiff_incrVec h hV)
  have hFper : SpacePeriodic F := by
    intro z j
    simp only [hF]
    rw [spacePeriodic_modProfileWeight (eps := eps) (z1 := z1) (h := h) hVper z j,
      spacePeriodic_incrPair h hVper z j, spacePeriodic_incrVec h hVper z j]
  have hc1 : Continuous (fun x : E3 =>
      modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x)) :=
    (hW.continuous.comp hslice).mul (hstretch.continuous.comp hslice)
  have hcdiv : Continuous (fun x : E3 => divg F (t, x)) :=
    (contDiff_divgFun hFC).continuous.comp hslice
  have hg : Continuous (fun x : E3 =>
      modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x) - divg F (t, x)) :=
    hc1.sub hcdiv
  have hcz1 : Continuous (fun x : E3 => z1 (incrModEps eps h V (t, x))) :=
    (hz1c.continuous.comp hmod.continuous).comp hslice
  have hcT : Continuous (fun x : E3 => incrTransDissipEps eps h V (t, x)) := by
    have hdis : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
    have hrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => ∑ j, (dvec (0, ee j) (incrModEps eps h V) w) ^ 2) :=
      ContDiff.sum fun j _ => (contDiff_dvec _ hmod _).pow 2
    exact ((hdis.sub hrad).continuous).comp hslice
  have hcU : Continuous (fun x : E3 => ∑ a, (V (t, x) a) ^ 2) :=
    continuous_finset_sum _ fun a _ =>
      (((contDiff_coord V hV a).continuous).comp hslice).pow 2
  have hcRes : Continuous (fun x : E3 => |modProfileResidual eps z2 h V (t, x)|) :=
    (hRes.continuous.comp hslice).abs
  have hcRHS : Continuous (fun x : E3 =>
      nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
        + z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
        + |modProfileResidual eps z2 h V (t, x)|) :=
    ((continuous_const.mul (hcz1.mul hcT)).add ((hcz1.mul hcU).div_const _)).add hcRes
  have hdivzero : cellInt (fun x => divg F (t, x)) = 0 := cellInt_divg_eq_zero F hFC hFper t
  have hsplit : cellInt (fun x =>
      modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x) - divg F (t, x))
      = cellInt (fun x => modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x)) := by
    rw [cellInt_sub hc1 hcdiv, hdivzero, sub_zero]
  have hpt : ∀ x : E3, |modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x)|
      ≤ nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
        + z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
        + |modProfileResidual eps z2 h V (t, x)| := by
    intro x
    have hcanc := increment_modulus_profile_split (h := h) heps hz1c hz1 hV hdiv (t, x)
    have habs := modulusEps_profile_transverse_absorption (h := h) hnu heps hz1nn hV (t, x)
    have hrw : modProfileWeight eps z1 h V (t, x) * incrStretch h V (t, x) - divg F (t, x)
        = -((z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
              * incrPerpPairEps eps h V (t, x))
          - modProfileResidual eps z2 h V (t, x) := by
      rw [hF, hcanc]; ring
    have hcoefnn : 0 ≤ z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x) :=
      div_nonneg (hz1nn _) (incrModEps_pos' heps h V (t, x)).le
    have habsmul : |(z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
        * incrPerpPairEps eps h V (t, x)|
        = (z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
          * |incrPerpPairEps eps h V (t, x)| := by
      rw [abs_mul, abs_of_nonneg hcoefnn]
    rw [hrw]
    have hstep : |(-((z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
          * incrPerpPairEps eps h V (t, x)))
        - modProfileResidual eps z2 h V (t, x)|
        ≤ |(z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
              * incrPerpPairEps eps h V (t, x)|
          + |modProfileResidual eps z2 h V (t, x)| := by
      calc |(-((z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
            * incrPerpPairEps eps h V (t, x)))
          - modProfileResidual eps z2 h V (t, x)|
          ≤ |(-((z1 (incrModEps eps h V (t, x)) / incrModEps eps h V (t, x))
              * incrPerpPairEps eps h V (t, x)))|
            + |modProfileResidual eps z2 h V (t, x)| := abs_sub _ _
        _ = _ := by rw [abs_neg]
    rw [habsmul] at hstep
    linarith [hstep, habs]
  have hbound := abs_cellInt_le hg hcRHS hpt
  rw [hsplit] at hbound
  have hle := (abs_le.mp hbound).2
  have hRHS : cellInt (fun x =>
        nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
          + z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
          + |modProfileResidual eps z2 h V (t, x)|)
      = nu / 2 * cellInt (fun x =>
            z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
        + 1 / (2 * nu) * cellInt (fun x =>
            z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2))
        + cellInt (fun x => |modProfileResidual eps z2 h V (t, x)|) := by
    have h1 : Continuous (fun x : E3 =>
        nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))) :=
      continuous_const.mul (hcz1.mul hcT)
    have h2 : Continuous (fun x : E3 =>
        1 / (2 * nu) * (z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2))) :=
      continuous_const.mul (hcz1.mul hcU)
    have hcongr : ∀ x : E3,
        nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
          + z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
          + |modProfileResidual eps z2 h V (t, x)|
        = (nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
            + 1 / (2 * nu) * (z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2)))
          + |modProfileResidual eps z2 h V (t, x)| := fun x => by ring
    have h12 : Continuous (fun x : E3 =>
        nu / 2 * (z1 (incrModEps eps h V (t, x)) * incrTransDissipEps eps h V (t, x))
          + 1 / (2 * nu) * (z1 (incrModEps eps h V (t, x)) * (∑ a, (V (t, x) a) ^ 2))) :=
      h1.add h2
    rw [cellInt_congr hcongr, cellInt_add h12 hcRes, cellInt_add h1 h2,
      cellInt_const_mul, cellInt_const_mul]
  rw [hRHS] at hle
  exact hle

/-- For the identity profile `ζ = id` (`ζ' ≡ 1`, `ζ'' ≡ 0`) the marginal
residual vanishes identically: `ClayNS.modulusEps_profile_cell_budget` then
reduces to `ClayNS.modulusEps_caccioppoli_cell_budget`. -/
@[simp] lemma modProfileResidual_flat (eps : ℝ) (h : E3) (V : STime → E3) (z : STime) :
    modProfileResidual eps (fun _ => (0:ℝ)) h V z = 0 := by
  simp [modProfileResidual]

/-- The identity profile realizes the modulus weight `1/r_ε`. -/
lemma modProfileWeight_one (eps : ℝ) (h : E3) (V : STime → E3) (z : STime) :
    modProfileWeight eps (fun _ => (1:ℝ)) h V z = incrModEpsWeight eps h V z := by
  rw [modProfileWeight, incrModEpsWeight_value, incrModEps, one_div]

end ClayNS
