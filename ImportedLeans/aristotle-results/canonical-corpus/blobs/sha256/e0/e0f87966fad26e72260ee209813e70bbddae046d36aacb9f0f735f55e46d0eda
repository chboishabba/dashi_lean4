/-
# The regularized modulus budget: exact cancellation with **no** hypotheses

`ModulusCaccioppoliCell.lean` integrates the modulus picture under the
non-degeneracy hypothesis `δ_hu ≠ 0`, needed because the entropy `r = |δ_hu|` is
singular where the increment vanishes.  This file removes that hypothesis.

The observation is that the regularized entropy

  `β_ε(q) = √(2q + ε²)`,   `β_ε'(q) = 1/r_ε`,   `β_ε''(q) = −1/r_ε³`,
  `r_ε = √(2q + ε²) ≥ ε > 0`,

satisfies the radial ODE *exactly* — not approximately — provided the radial
direction is normalized by `r_ε²` rather than by `|δ_hu|² = 2q`:

  `β_ε'' + β_ε'/r_ε² = −1/r_ε³ + (1/r_ε)/r_ε² = 0`.

So the cancellation of the marginal radial stretching channel is available for a
**globally smooth**, everywhere-defined weight
(`ClayNS.increment_modulusEps_radial_cancellation`), and the transverse geometry
survives the regularization: the regularized transverse dissipation

  `T_ε = |∇δ_hu|² − |∇r_ε|²`

is nonnegative (`ClayNS.incrTransDissipEps_nonneg`), dominates the exact one, and
controls the transverse stretching remainder exactly as before
(`ClayNS.incrTransportPerpEps_sq_le`).

The result is the unconditional integrated budget
(`ClayNS.modulusEps_caccioppoli_cell_budget`)

  `∫_cell r_ε^{-1}·δ_hu·(δ_hu·∇)u
      ≤ (ν/2)∫_cell (|∇δ_hu|² − |∇r_ε|²)/r_ε + (1/2ν)∫_cell r_ε|u|²`,

valid for every `ε > 0`, every smooth periodic divergence-free `u` and every
increment step `h`, with no bound on `∇u`, no critical `L^{5/2}` strain norm, no
level-set exponent `θ` and no non-degeneracy assumption.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ModulusCaccioppoliCell

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The regularized modulus and its transverse dissipation -/

/-- The regularized modulus `r_ε = √(|δ_hu|² + ε²)`. -/
def incrModEps (eps : ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun w => Real.sqrt (2 * incrQuad h V w + eps ^ 2)

lemma incrModEps_pos' {eps : ℝ} (heps : 0 < eps) (h : E3) (V : STime → E3) (z : STime) :
    0 < incrModEps eps h V z :=
  Real.sqrt_pos.2 (incrModEps_pos heps h V z)

lemma incrModEps_sq {eps : ℝ} (heps : 0 < eps) (h : E3) (V : STime → E3) (z : STime) :
    (incrModEps eps h V z) ^ 2 = 2 * incrQuad h V z + eps ^ 2 :=
  Real.sq_sqrt (le_of_lt (incrModEps_pos heps h V z))

lemma contDiff_incrModEps {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => 2 * incrQuad h V w + eps ^ 2) z :=
    ((contDiff_const.mul (contDiff_incrQuad h hV)).add contDiff_const).contDiffAt
  exact (Real.contDiffAt_sqrt (ne_of_gt (incrModEps_pos heps h V z))).comp z hg

lemma spacePeriodic_incrModEps {eps : ℝ} {h : E3} {V : STime → E3}
    (hVper : SpacePeriodic V) : SpacePeriodic (incrModEps eps h V) := by
  intro z j
  simp only [incrModEps]
  rw [spacePeriodic_incrQuad h hVper z j]

/-- `d/ds √(2s + ε²) = 1/√(2s + ε²)`. -/
lemma hasDerivAt_sqrtAff {eps s : ℝ} (hpos : 0 < 2 * s + eps ^ 2) :
    HasDerivAt (fun y : ℝ => Real.sqrt (2 * y + eps ^ 2))
      (1 / Real.sqrt (2 * s + eps ^ 2)) s := by
  have haff : HasDerivAt (fun y : ℝ => 2 * y + eps ^ 2) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul (2:ℝ)).add_const (eps ^ 2)
  have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp s haff
  have hne : Real.sqrt (2 * s + eps ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp only [Function.comp_def] at hcomp
  convert hcomp using 1
  field_simp

/-- `∂ r_ε = (δ_hu·∂δ_hu)/r_ε`. -/
lemma dvec_incrModEps {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) (a : STime) :
    dvec a (incrModEps eps h V) z
      = (∑ i, incrComp h V i z * dvec a (incrComp h V i) z) / incrModEps eps h V z := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hchain := dvec_comp_scalar_at (Q := incrQuad h V) hQ
    (f := fun y : ℝ => Real.sqrt (2 * y + eps ^ 2))
    (hasDerivAt_sqrtAff (incrModEps_pos heps h V z)) a
  have hdq : dvec a (incrQuad h V) z = ∑ i, incrComp h V i z * dvec a (incrComp h V i) z :=
    dvec_quad (incrComp h V) (fun i => contDiff_incrComp h hV i) a z
  have hform : incrModEps eps h V = fun w => Real.sqrt (2 * incrQuad h V w + eps ^ 2) := rfl
  rw [hform, hchain, hdq]
  have hne : Real.sqrt (2 * incrQuad h V z + eps ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (incrModEps_pos heps h V z))
  field_simp

/-- The regularized transverse dissipation `T_ε = |∇δ_hu|² − |∇r_ε|²`. -/
def incrTransDissipEps (eps : ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => incrDissip h V z - ∑ j, (dvec (0, ee j) (incrModEps eps h V) z) ^ 2

lemma incrTransDissipEps_eq {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    incrTransDissipEps eps h V z
      = ∑ j, ((∑ a, (dvec (0, ee j) (incrComp h V a) z) ^ 2)
          - (∑ a, incrComp h V a z * dvec (0, ee j) (incrComp h V a) z) ^ 2
              / (2 * incrQuad h V z + eps ^ 2)) := by
  have hstep : ∀ j : Fin 3, (dvec (0, ee j) (incrModEps eps h V) z) ^ 2
      = (∑ a, incrComp h V a z * dvec (0, ee j) (incrComp h V a) z) ^ 2
          / (2 * incrQuad h V z + eps ^ 2) := by
    intro j
    rw [dvec_incrModEps heps hV z (0, ee j), div_pow, incrModEps_sq heps]
  simp only [incrTransDissipEps, incrDissip_eq_sq, hstep, Finset.sum_sub_distrib]

/-- The regularized transverse dissipation is nonnegative. -/
theorem incrTransDissipEps_nonneg {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) : 0 ≤ incrTransDissipEps eps h V z := by
  rw [incrTransDissipEps_eq heps hV z]
  refine Finset.sum_nonneg fun j _ => ?_
  have hR : (0:ℝ) < 2 * incrQuad h V z + eps ^ 2 := incrModEps_pos heps h V z
  have hnorm : ∑ a, (incrComp h V a z) ^ 2 ≤ 2 * incrQuad h V z + eps ^ 2 := by
    have h1 := two_incrQuad_eq h V z
    nlinarith [sq_nonneg eps]
  have hcs := gram_nonneg (fun a => incrComp h V a z)
    (fun a => dvec (0, ee j) (incrComp h V a) z)
  have hD : (0:ℝ) ≤ ∑ a, (dvec (0, ee j) (incrComp h V a) z) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (∑ a, incrComp h V a z * dvec (0, ee j) (incrComp h V a) z) ^ 2
      ≤ (2 * incrQuad h V z + eps ^ 2) * ∑ a, (dvec (0, ee j) (incrComp h V a) z) ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hnorm hD)
  rw [sub_nonneg, div_le_iff₀ hR]
  linarith [hbound]

/-! ## The regularized transverse stretching -/

/-- The regularized transverse transported derivative. -/
def incrTransportPerpEps (eps : ℝ) (h : E3) (V : STime → E3) (a : Fin 3) : STime → ℝ :=
  fun z => incrTransport h V a z
    - (∑ b, incrComp h V b z * incrTransport h V b z) / (2 * incrQuad h V z + eps ^ 2)
        * incrComp h V a z

/-- The regularized transverse stretching pairing. -/
def incrPerpPairEps (eps : ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => incrTransfer h V z
    - incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
        / (2 * incrQuad h V z + eps ^ 2)

lemma incrPerpPairEps_eq_pairing {eps : ℝ} {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    incrPerpPairEps eps h V z = ∑ a, V z a * incrTransportPerpEps eps h V a z := by
  have htr : incrTransfer h V z = ∑ a, V z a * incrTransport h V a z := by
    simp only [incrTransfer, incrTransport, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : incrPair h V z * (∑ b, incrComp h V b z * incrTransport h V b z)
        / (2 * incrQuad h V z + eps ^ 2)
      = ∑ a, V z a * ((∑ b, incrComp h V b z * incrTransport h V b z)
          / (2 * incrQuad h V z + eps ^ 2) * incrComp h V a z) := by
    rw [incrPair, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [incrPerpPairEps, htr, incr_radial_transport hV z, h2]
  simp only [incrTransportPerpEps, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The regularized transverse stretching is bounded by the regularized
transverse dissipation. -/
theorem incrTransportPerpEps_sq_le {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    ∑ a, (incrTransportPerpEps eps h V a z) ^ 2
      ≤ (2 * incrQuad h V z + eps ^ 2) * incrTransDissipEps eps h V z := by
  have hR : (0:ℝ) < 2 * incrQuad h V z + eps ^ 2 := incrModEps_pos heps h V z
  have hnorm : ∑ a, (fun b => incrComp h V b z) a ^ 2 ≤ 2 * incrQuad h V z + eps ^ 2 := by
    have h1 := two_incrQuad_eq h V z
    nlinarith [sq_nonneg eps]
  have hperp : ∀ a : Fin 3, incrTransportPerpEps eps h V a z
      = ∑ j, incrComp h V j z * (dvec (0, ee j) (incrComp h V a) z
          - ((∑ i, incrComp h V i z * dvec (0, ee j) (incrComp h V i) z)
              / (2 * incrQuad h V z + eps ^ 2)) * incrComp h V a z) := fun a =>
    perp_contraction_eq (fun b => incrComp h V b z)
      (fun j b => dvec (0, ee j) (incrComp h V b) z) (2 * incrQuad h V z + eps ^ 2) a
  calc ∑ a, (incrTransportPerpEps eps h V a z) ^ 2
      = ∑ a, (∑ j, (fun b => incrComp h V b z) j
          * ((fun j b => dvec (0, ee j) (incrComp h V b) z) j a
            - ((∑ i, (fun b => incrComp h V b z) i
                * (fun j b => dvec (0, ee j) (incrComp h V b) z) j i)
              / (2 * incrQuad h V z + eps ^ 2)) * (fun b => incrComp h V b z) a)) ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hperp a]
    _ ≤ (2 * incrQuad h V z + eps ^ 2)
          * ∑ j, ((∑ a, (fun j b => dvec (0, ee j) (incrComp h V b) z) j a ^ 2)
            - (∑ a, (fun b => incrComp h V b z) a
                * (fun j b => dvec (0, ee j) (incrComp h V b) z) j a) ^ 2
              / (2 * incrQuad h V z + eps ^ 2)) :=
        transverse_contraction_le_of_le _ _ hR hnorm
    _ = (2 * incrQuad h V z + eps ^ 2) * incrTransDissipEps eps h V z := by
        rw [incrTransDissipEps_eq heps hV z]

/-- `|u_⊥·d_⊥| ≤ |u|·r_ε·√T_ε` in the regularized geometry. -/
theorem incrPerpPairEps_abs_le {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    |incrPerpPairEps eps h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2)
          * (incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z)) := by
  have hT : 0 ≤ incrTransDissipEps eps h V z := incrTransDissipEps_nonneg heps hV z
  have hU : (0:ℝ) ≤ ∑ a, (V z a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := gram_nonneg (fun a => V z a) (fun a => incrTransportPerpEps eps h V a z)
  have hpair : incrPerpPairEps eps h V z = ∑ a, V z a * incrTransportPerpEps eps h V a z :=
    incrPerpPairEps_eq_pairing hV z
  have habs : |incrPerpPairEps eps h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2)
        * Real.sqrt (∑ a, (incrTransportPerpEps eps h V a z) ^ 2) := by
    rw [hpair, ← Real.sqrt_mul hU, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  have hmodT : Real.sqrt (∑ a, (incrTransportPerpEps eps h V a z) ^ 2)
      ≤ incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z) := by
    have hle := incrTransportPerpEps_sq_le (h := h) heps hV z
    have hsq : (incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z)) ^ 2
        = (2 * incrQuad h V z + eps ^ 2) * incrTransDissipEps eps h V z := by
      rw [mul_pow, incrModEps_sq heps, Real.sq_sqrt hT]
    have hnn : 0 ≤ incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z) :=
      mul_nonneg (le_of_lt (incrModEps_pos' heps h V z)) (Real.sqrt_nonneg _)
    rw [show incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z)
        = Real.sqrt ((incrModEps eps h V z
            * Real.sqrt (incrTransDissipEps eps h V z)) ^ 2) from (Real.sqrt_sq hnn).symm, hsq]
    exact Real.sqrt_le_sqrt hle
  calc |incrPerpPairEps eps h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2)
          * Real.sqrt (∑ a, (incrTransportPerpEps eps h V a z) ^ 2) := habs
    _ ≤ Real.sqrt (∑ a, (V z a) ^ 2)
          * (incrModEps eps h V z * Real.sqrt (incrTransDissipEps eps h V z)) :=
        mul_le_mul_of_nonneg_left hmodT (Real.sqrt_nonneg _)

/-- Young absorption in the regularized geometry. -/
theorem modulusEps_transverse_absorption {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    |incrPerpPairEps eps h V z| / incrModEps eps h V z
      ≤ nu / 2 * (incrTransDissipEps eps h V z / incrModEps eps h V z)
        + incrModEps eps h V z * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  have hr : 0 < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hT : 0 ≤ incrTransDissipEps eps h V z := incrTransDissipEps_nonneg heps hV z
  have hU : (0:ℝ) ≤ ∑ a, (V z a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set A : ℝ := Real.sqrt (incrTransDissipEps eps h V z) with hA
  set B : ℝ := Real.sqrt (∑ a, (V z a) ^ 2) with hB
  have hA2 : A ^ 2 = incrTransDissipEps eps h V z := Real.sq_sqrt hT
  have hB2 : B ^ 2 = ∑ a, (V z a) ^ 2 := Real.sq_sqrt hU
  have hkey : |incrPerpPairEps eps h V z| / incrModEps eps h V z ≤ B * A := by
    have hbnd := incrPerpPairEps_abs_le (h := h) heps hV z
    rw [div_le_iff₀ hr]
    calc |incrPerpPairEps eps h V z| ≤ B * (incrModEps eps h V z * A) := hbnd
      _ = B * A * incrModEps eps h V z := by ring
  have hyoung : B * A ≤ nu / 2 * (A ^ 2 / incrModEps eps h V z)
      + incrModEps eps h V z * B ^ 2 / (2 * nu) := by
    have hsq : 0 ≤ (nu * A / incrModEps eps h V z - B) ^ 2 := sq_nonneg _
    have hexp : (nu * A / incrModEps eps h V z - B) ^ 2
        = nu ^ 2 * A ^ 2 / (incrModEps eps h V z) ^ 2
          - 2 * (nu * A * B / incrModEps eps h V z) + B ^ 2 := by
      field_simp
      ring
    rw [hexp] at hsq
    have hmul : 0 ≤ incrModEps eps h V z / (2 * nu) := by positivity
    have hstep := mul_le_mul_of_nonneg_left
      (by linarith : 2 * (nu * A * B / incrModEps eps h V z)
        ≤ nu ^ 2 * A ^ 2 / (incrModEps eps h V z) ^ 2 + B ^ 2) hmul
    have hne : incrModEps eps h V z ≠ 0 := ne_of_gt hr
    have hnune : nu ≠ 0 := ne_of_gt hnu
    calc B * A
        = incrModEps eps h V z / (2 * nu) * (2 * (nu * A * B / incrModEps eps h V z)) := by
          field_simp
      _ ≤ incrModEps eps h V z / (2 * nu)
            * (nu ^ 2 * A ^ 2 / (incrModEps eps h V z) ^ 2 + B ^ 2) := hstep
      _ = nu / 2 * (A ^ 2 / incrModEps eps h V z)
            + incrModEps eps h V z * B ^ 2 / (2 * nu) := by field_simp
  rw [hA2, hB2] at hyoung
  linarith

/-! ## Exact cancellation for the regularized weight -/

/-- **The regularized radial cancellation.**  The weight `W_ε = 1/r_ε` is
globally smooth and satisfies the radial ODE `β'' + β'/r_ε² = 0` *exactly*, so
the marginal radial stretching channel cancels identically — with no
non-degeneracy hypothesis anywhere. -/
theorem increment_modulusEps_radial_cancellation {eps : ℝ} (heps : 0 < eps) {h : E3}
    {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0)
    (z : STime) :
    incrModEpsWeight eps h V z * incrStretch h V z
      = divg (fun w => (incrModEpsWeight eps h V w * incrPair h V w) • incrVec h V w) z
        - (1 / incrModEps eps h V z) * incrPerpPairEps eps h V z := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (incrModEpsWeight eps h V) := contDiff_incrModEpsWeight heps hV
  have hR : (0:ℝ) < 2 * incrQuad h V z + eps ^ 2 := incrModEps_pos heps h V z
  have hr : 0 < incrModEps eps h V z := incrModEps_pos' heps h V z
  have hWz : incrModEpsWeight eps h V z = 1 / incrModEps eps h V z := by
    rw [incrModEpsWeight_value, incrModEps, one_div]
  have hdW : ∀ j : Fin 3, dvec (0, ee j) (incrModEpsWeight eps h V) z
      = (-(((2 * incrQuad h V z + eps ^ 2)
            * Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹))
        * dvec (0, ee j) (incrQuad h V) z := fun j =>
    incrModEpsWeight_grad heps hV z (0, ee j)
  have hsplit := increment_stretching_radial_split_gen (W := incrModEpsWeight eps h V)
    hV hW hdiv z (R := 2 * incrQuad h V z + eps ^ 2) (ne_of_gt hR) hWz hdW
  have hODE : (-(((2 * incrQuad h V z + eps ^ 2)
        * Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹))
      + (1 / incrModEps eps h V z) / (2 * incrQuad h V z + eps ^ 2) = 0 := by
    rw [incrModEps]
    have hne : Real.sqrt (2 * incrQuad h V z + eps ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hR)
    have hRne : (2 * incrQuad h V z + eps ^ 2) ≠ 0 := ne_of_gt hR
    field_simp
    ring
  rw [hsplit, hODE]
  simp only [incrPerpPairEps]
  ring

/-! ## The unconditional integrated budget -/

/-- **The regularized modulus Caccioppoli budget on the cell.**  For every
`ε > 0`, every smooth periodic divergence-free velocity and every increment
step,

`∫_cell r_ε^{-1}·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell (|∇δ_hu|² − |∇r_ε|²)/r_ε + (1/2ν)∫_cell r_ε|u|²`.

No bound on `∇u`, no critical strain norm, no level-set exponent `θ` and no
non-degeneracy hypothesis: the marginal radial channel cancels exactly and the
transverse channel is absorbed by the transverse viscous surplus, leaving a
source linear in `r_ε`. -/
theorem modulusEps_caccioppoli_cell_budget {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    cellInt (fun x => incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x))
      ≤ nu / 2 * cellInt (fun x =>
            incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
        + 1 / (2 * nu)
            * cellInt (fun x => incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := by
  classical
  have hW : ContDiff ℝ (⊤ : ℕ∞) (incrModEpsWeight eps h V) := contDiff_incrModEpsWeight heps hV
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hstretch : ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) := contDiff_incrStretch h hV
  set F : STime → E3 :=
    fun w => (incrModEpsWeight eps h V w * incrPair h V w) • incrVec h V w with hF
  have hFC : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hW.mul (contDiff_incrPair h hV)).smul (contDiff_incrVec h hV)
  have hWper : SpacePeriodic (incrModEpsWeight eps h V) := by
    intro z j
    simp only [incrModEpsWeight]
    rw [spacePeriodic_incrQuad h hVper z j]
  have hFper : SpacePeriodic F := by
    intro z j
    simp only [hF]
    rw [hWper z j, spacePeriodic_incrPair h hVper z j, spacePeriodic_incrVec h hVper z j]
  have hslice : Continuous (fun x : E3 => ((t, x) : STime)) :=
    continuous_const.prodMk continuous_id
  have hc1 : Continuous (fun x : E3 =>
      incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x)) :=
    (hW.continuous.comp hslice).mul (hstretch.continuous.comp hslice)
  have hcdiv : Continuous (fun x : E3 => divg F (t, x)) :=
    (contDiff_divgFun hFC).continuous.comp hslice
  have hg : Continuous (fun x : E3 => incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x)) := hc1.sub hcdiv
  have hcT : Continuous (fun x : E3 => incrTransDissipEps eps h V (t, x)) := by
    have hdis : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
    have hrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => ∑ j, (dvec (0, ee j) (incrModEps eps h V) w) ^ 2) :=
      ContDiff.sum fun j _ => (contDiff_dvec _ hmod _).pow 2
    exact ((hdis.sub hrad).continuous).comp hslice
  have hcr : Continuous (fun x : E3 => incrModEps eps h V (t, x)) :=
    hmod.continuous.comp hslice
  have hne : ∀ x : E3, incrModEps eps h V (t, x) ≠ 0 :=
    fun x => ne_of_gt (incrModEps_pos' heps h V (t, x))
  have hcU : Continuous (fun x : E3 => ∑ a, (V (t, x) a) ^ 2) :=
    continuous_finset_sum _ fun a _ =>
      (((contDiff_coord V hV a).continuous).comp hslice).pow 2
  have hcRHS : Continuous (fun x : E3 =>
      nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
        + incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)) :=
    (continuous_const.mul (hcT.div hcr hne)).add ((hcr.mul hcU).div_const _)
  have hdivzero : cellInt (fun x => divg F (t, x)) = 0 := cellInt_divg_eq_zero F hFC hFper t
  have hsplit : cellInt (fun x =>
      incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x) - divg F (t, x))
      = cellInt (fun x => incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x)) := by
    rw [cellInt_sub hc1 hcdiv, hdivzero, sub_zero]
  have hpt : ∀ x : E3, |incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x)
      - divg F (t, x)|
      ≤ nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
        + incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu) := by
    intro x
    have hcanc := increment_modulusEps_radial_cancellation (h := h) heps hV hdiv (t, x)
    have habs := modulusEps_transverse_absorption (h := h) hnu heps hV (t, x)
    have hrw : incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x) - divg F (t, x)
        = -((1 / incrModEps eps h V (t, x)) * incrPerpPairEps eps h V (t, x)) := by
      rw [hF, hcanc]; ring
    rw [hrw, abs_neg, abs_mul,
      abs_of_nonneg (le_of_lt (one_div_pos.2 (incrModEps_pos' heps h V (t, x))))]
    calc 1 / incrModEps eps h V (t, x) * |incrPerpPairEps eps h V (t, x)|
        = |incrPerpPairEps eps h V (t, x)| / incrModEps eps h V (t, x) := by ring
      _ ≤ _ := habs
  have hbound := abs_cellInt_le hg hcRHS hpt
  rw [hsplit] at hbound
  have hle := (abs_le.mp hbound).2
  have hRHS : cellInt (fun x =>
        nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
          + incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu))
      = nu / 2 * cellInt (fun x =>
            incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
        + 1 / (2 * nu)
            * cellInt (fun x => incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := by
    have h1 : Continuous (fun x : E3 =>
        nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))) :=
      continuous_const.mul (hcT.div hcr hne)
    have h2 : Continuous (fun x : E3 =>
        1 / (2 * nu) * (incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2))) :=
      continuous_const.mul (hcr.mul hcU)
    have hcongr : ∀ x : E3,
        nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
          + incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2) / (2 * nu)
        = nu / 2 * (incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
          + 1 / (2 * nu) * (incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) :=
      fun x => by ring
    rw [cellInt_congr hcongr, cellInt_add h1 h2, cellInt_const_mul, cellInt_const_mul]
  rw [hRHS] at hle
  exact hle

end ClayNS
