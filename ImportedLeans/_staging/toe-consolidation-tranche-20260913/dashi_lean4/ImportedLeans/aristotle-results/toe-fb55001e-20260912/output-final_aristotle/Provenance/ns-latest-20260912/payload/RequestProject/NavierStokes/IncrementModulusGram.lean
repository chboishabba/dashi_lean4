/-
# The modulus variable and its exact Gram (transverse) surplus

This file changes the De Giorgi variable of the increment programme from the
quadratic density `q = ½|δ_hu|²` to the **modulus** `r = |δ_hu| = √(2q)` and
extracts the exact geometric structure that the change exposes.

* `ClayNS.lagrange_gram_three` — the Lagrange identity in `ℝ³`:
  `|a|²|b|² − ⟨a,b⟩² = |a∧b|²`, i.e. the Gram determinant of a pair of vectors
  is the squared area of the parallelogram they span;

* `ClayNS.increment_modulus_gram_decomposition` (**C₄₅**) — at every point where
  the increment does not vanish,
  `|∇δ_hu|² − |∇|δ_hu||² = |δ_hu|^{-2} ∑_j |δ_hu ∧ ∂_jδ_hu|² ≥ 0`.
  The diffusion of a *vector* increment therefore splits exactly into a radial
  part (the diffusion of the modulus) and a **nonnegative transverse/angular
  surplus** which the quadratic variable `q` never sees;

* `ClayNS.incrTransportPerp_sq_le`, `ClayNS.incrPerpPair_abs_le` and
  `ClayNS.modulus_transverse_absorption` (the analytic half of **C₄₇**) — the
  transverse part of the transported derivative `(δ_hu·∇)δ_hu` is controlled by
  *exactly* that surplus,
  `|P_⊥(δ_hu·∇)δ_hu|² ≤ |δ_hu|²·(|∇δ_hu|² − |∇|δ_hu||²)`,
  so that after Young's inequality the transverse stretching pairing is
  absorbed into `ν(|∇δ_hu|² − |∇|δ_hu||²)/|δ_hu|` — precisely the viscous term
  produced by the modulus chain rule — at the price of a source that is
  **linear** in the modulus, with coefficient `|u|²/2ν`.

No bound on `∇u`, no critical norm of the strain, and no level-set exponent
enters any statement of this file.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementStretchingTransfer

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The Lagrange/Gram identity in three dimensions -/

/-- The squared wedge (cross-product) of two vectors of `ℝ³`. -/
def wedgeSq (a b : Fin 3 → ℝ) : ℝ :=
  (a 0 * b 1 - a 1 * b 0) ^ 2 + (a 0 * b 2 - a 2 * b 0) ^ 2 + (a 1 * b 2 - a 2 * b 1) ^ 2

lemma wedgeSq_nonneg (a b : Fin 3 → ℝ) : 0 ≤ wedgeSq a b := by
  unfold wedgeSq; positivity

/-- **The Lagrange identity.**  The Gram determinant `|a|²|b|² − ⟨a,b⟩²` of a
pair of vectors of `ℝ³` is the squared area `|a∧b|²`. -/
theorem lagrange_gram_three (a b : Fin 3 → ℝ) :
    (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 = wedgeSq a b := by
  simp only [Fin.sum_univ_three, wedgeSq]
  ring

/-- Cauchy–Schwarz in the Gram form. -/
lemma gram_nonneg (a b : Fin 3 → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  have h := lagrange_gram_three a b
  have := wedgeSq_nonneg a b
  linarith

/-! ## An abstract transverse Cauchy–Schwarz inequality -/

/-- The squared norm of the component of `D j ·` orthogonal to `w`. -/
lemma perp_norm_sq (w D : Fin 3 → ℝ) {R : ℝ} (hR : 0 < R) (hnorm : ∑ a, w a ^ 2 = R) :
    ∑ a, (D a - ((∑ i, w i * D i) / R) * w a) ^ 2
      = (∑ a, D a ^ 2) - (∑ a, w a * D a) ^ 2 / R := by
  have hexp : ∀ a : Fin 3, (D a - ((∑ i, w i * D i) / R) * w a) ^ 2
      = D a ^ 2 - 2 * ((∑ i, w i * D i) / R) * (w a * D a)
        + ((∑ i, w i * D i) / R) ^ 2 * w a ^ 2 := by
    intro a; ring
  rw [Finset.sum_congr rfl fun a _ => hexp a]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hnorm]
  field_simp
  ring

/-- The regularized version of `ClayNS.perp_norm_sq`: if the squared norm of `w`
is at most `R` the projected norm is *at most* the Gram quotient.  (Equality
holds when `∑ w² = R`.) -/
lemma perp_norm_sq_le (w D : Fin 3 → ℝ) {R : ℝ} (hR : 0 < R) (hnorm : ∑ a, w a ^ 2 ≤ R) :
    ∑ a, (D a - ((∑ i, w i * D i) / R) * w a) ^ 2
      ≤ (∑ a, D a ^ 2) - (∑ a, w a * D a) ^ 2 / R := by
  have hexp : ∀ a : Fin 3, (D a - ((∑ i, w i * D i) / R) * w a) ^ 2
      = D a ^ 2 - 2 * ((∑ i, w i * D i) / R) * (w a * D a)
        + ((∑ i, w i * D i) / R) ^ 2 * w a ^ 2 := by
    intro a; ring
  rw [Finset.sum_congr rfl fun a _ => hexp a]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsq : (0:ℝ) ≤ ((∑ i, w i * D i) / R) ^ 2 := sq_nonneg _
  have hmul : ((∑ i, w i * D i) / R) ^ 2 * (∑ a, w a ^ 2)
      ≤ ((∑ i, w i * D i) / R) ^ 2 * R := mul_le_mul_of_nonneg_left hnorm hsq
  have hkey : ((∑ i, w i * D i) / R) ^ 2 * R = (∑ a, w a * D a) ^ 2 / R := by
    field_simp
  have h2 : 2 * ((∑ i, w i * D i) / R) * (∑ a, w a * D a)
      = 2 * ((∑ a, w a * D a) ^ 2 / R) := by
    field_simp
  rw [h2] at *
  nlinarith [hmul, hkey]

/-- **Transverse Cauchy–Schwarz, regularized form.**  Only `∑ w² ≤ R` is
required. -/
lemma transverse_contraction_le_of_le (w : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) {R : ℝ}
    (hR : 0 < R) (hnorm : ∑ a, w a ^ 2 ≤ R) :
    ∑ a, (∑ j, w j * (D j a - ((∑ i, w i * D j i) / R) * w a)) ^ 2
      ≤ R * ∑ j, ((∑ a, D j a ^ 2) - (∑ a, w a * D j a) ^ 2 / R) := by
  set P : Fin 3 → Fin 3 → ℝ := fun j a => D j a - ((∑ i, w i * D j i) / R) * w a with hP
  have hstep : ∀ a : Fin 3, (∑ j, w j * P j a) ^ 2 ≤ R * ∑ j, (P j a) ^ 2 := by
    intro a
    have hcs := gram_nonneg w (fun j => P j a)
    have hnn : (0:ℝ) ≤ ∑ j, (P j a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ j, w j * P j a) ^ 2 ≤ (∑ j, w j ^ 2) * ∑ j, (P j a) ^ 2 := hcs
      _ ≤ R * ∑ j, (P j a) ^ 2 := mul_le_mul_of_nonneg_right hnorm hnn
  calc ∑ a, (∑ j, w j * P j a) ^ 2 ≤ ∑ a, R * ∑ j, (P j a) ^ 2 :=
        Finset.sum_le_sum fun a _ => hstep a
    _ = R * ∑ j, ∑ a, (P j a) ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ R * ∑ j, ((∑ a, D j a ^ 2) - (∑ a, w a * D j a) ^ 2 / R) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (le_of_lt hR)
        exact perp_norm_sq_le w (D j) hR hnorm

/-- The `w`-contraction of the transverse parts is the transverse part of the
`w`-contraction. -/
lemma perp_contraction_eq (w : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) (R : ℝ) (a : Fin 3) :
    (∑ j, w j * D j a) - (∑ b, w b * ∑ j, w j * D j b) / R * w a
      = ∑ j, w j * (D j a - ((∑ i, w i * D j i) / R) * w a) := by
  have hswap : (∑ b, w b * ∑ j, w j * D j b) = ∑ j, w j * ∑ i, w i * D j i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hswap, Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Transverse Cauchy–Schwarz.**  If `w` has squared norm `R > 0` then the
`w`-contraction of the transverse parts of the vectors `D j ·` obeys
`|∑_j w_j P_⊥D_j|² ≤ R·∑_j |P_⊥D_j|²`. -/
lemma transverse_contraction_le (w : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) {R : ℝ}
    (hR : 0 < R) (hnorm : ∑ a, w a ^ 2 = R) :
    ∑ a, (∑ j, w j * (D j a - ((∑ i, w i * D j i) / R) * w a)) ^ 2
      ≤ R * ∑ j, ((∑ a, D j a ^ 2) - (∑ a, w a * D j a) ^ 2 / R) := by
  set P : Fin 3 → Fin 3 → ℝ := fun j a => D j a - ((∑ i, w i * D j i) / R) * w a with hP
  have hstep : ∀ a : Fin 3, (∑ j, w j * P j a) ^ 2 ≤ R * ∑ j, (P j a) ^ 2 := by
    intro a
    have hcs := gram_nonneg w (fun j => P j a)
    rw [hnorm] at hcs
    exact hcs
  calc ∑ a, (∑ j, w j * P j a) ^ 2 ≤ ∑ a, R * ∑ j, (P j a) ^ 2 :=
        Finset.sum_le_sum fun a _ => hstep a
    _ = R * ∑ j, ∑ a, (P j a) ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ = R * ∑ j, ((∑ a, D j a ^ 2) - (∑ a, w a * D j a) ^ 2 / R) := by
        refine congrArg (fun s => R * s) (Finset.sum_congr rfl fun j _ => ?_)
        exact perp_norm_sq w (D j) hR hnorm

/-! ## The modulus of the increment -/

/-- The modulus `r = |δ_hu| = √(2q)` of the increment. -/
def incrMod (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => Real.sqrt (2 * incrQuad h V z)

lemma two_incrQuad_eq (h : E3) (V : STime → E3) (z : STime) :
    2 * incrQuad h V z = ∑ a, (incrComp h V a z) ^ 2 := by
  simp only [incrQuad, quad, ← mul_assoc]
  norm_num
  exact Finset.sum_congr rfl fun a _ => (sq (incrComp h V a z)).symm

lemma incrQuad_nonneg (h : E3) (V : STime → E3) (z : STime) : 0 ≤ incrQuad h V z := by
  have h1 := two_incrQuad_eq h V z
  have hs : (0:ℝ) ≤ ∑ a, (incrComp h V a z) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma incrMod_nonneg (h : E3) (V : STime → E3) (z : STime) : 0 ≤ incrMod h V z :=
  Real.sqrt_nonneg _

lemma incrMod_pos {h : E3} {V : STime → E3} {z : STime} (hz : 0 < incrQuad h V z) :
    0 < incrMod h V z := Real.sqrt_pos.2 (by linarith)

lemma incrMod_sq {h : E3} {V : STime → E3} {z : STime} (hz : 0 ≤ incrQuad h V z) :
    (incrMod h V z) ^ 2 = 2 * incrQuad h V z :=
  Real.sq_sqrt (by linarith)

/-! ## The chain rule at a point -/

/-- Pointwise chain rule: only a `HasDerivAt` at the value `Q z` is needed, so
functions differentiable only away from a singularity (such as `√·`) are
covered. -/
lemma dvec_comp_scalar_at {Q : STime → ℝ} (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    {f : ℝ → ℝ} {c : ℝ} {z : STime} (hf : HasDerivAt f c (Q z)) (a : STime) :
    dvec a (fun w => f (Q w)) z = c * dvec a Q z := by
  have hQd : DifferentiableAt ℝ Q z := (differentiable_of_contDiffTop hQ) z
  have hcomp : HasFDerivAt (fun w => f (Q w)) (c • fderiv ℝ Q z) z :=
    hf.comp_hasFDerivAt z hQd.hasFDerivAt
  show (fderiv ℝ (fun w => f (Q w)) z) a = _
  rw [hcomp.fderiv]
  simp [dvec]

/-- `d/ds √(2s) = 1/√(2s)` for `s > 0`. -/
lemma hasDerivAt_sqrt_two_mul {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => Real.sqrt (2 * y)) (1 / Real.sqrt (2 * s)) s := by
  have h2 : (0:ℝ) < 2 * s := by linarith
  have hmul : HasDerivAt (fun y : ℝ => 2 * y) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2:ℝ)
  have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt h2)).comp s hmul
  have hne : Real.sqrt (2 * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h2)
  convert hcomp using 1
  field_simp

/-- The derivative of the modulus: `∂ r = (w·∂w)/r`. -/
lemma dvec_incrMod {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : STime}
    (hz : 0 < incrQuad h V z) (a : STime) :
    dvec a (incrMod h V) z
      = (∑ i, incrComp h V i z * dvec a (incrComp h V i) z) / incrMod h V z := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hchain := dvec_comp_scalar_at (Q := incrQuad h V) hQ
    (f := fun y : ℝ => Real.sqrt (2 * y)) (hasDerivAt_sqrt_two_mul hz) a
  have hdq : dvec a (incrQuad h V) z = ∑ i, incrComp h V i z * dvec a (incrComp h V i) z :=
    dvec_quad (incrComp h V) (fun i => contDiff_incrComp h hV i) a z
  have hmod : incrMod h V = fun w => Real.sqrt (2 * incrQuad h V w) := rfl
  rw [hmod, hchain, hdq]
  have hr : Real.sqrt (2 * incrQuad h V z) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  field_simp

/-! ## C₄₅: the exact Gram decomposition of the increment diffusion -/

/-- The **transverse dissipation** `|∇δ_hu|² − |∇|δ_hu||²`. -/
def incrTransDissip (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => incrDissip h V z - ∑ j, (dvec (0, ee j) (incrMod h V) z) ^ 2

lemma incrDissip_eq_sq (h : E3) (V : STime → E3) (z : STime) :
    incrDissip h V z = ∑ j, ∑ a, (dvec (0, ee j) (incrComp h V a) z) ^ 2 := by
  simp only [incrDissip]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => (sq _).symm

/-- The transverse dissipation, written with the radial part subtracted
coordinate by coordinate. -/
lemma incrTransDissip_eq {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : STime}
    (hz : 0 < incrQuad h V z) :
    incrTransDissip h V z
      = ∑ j, ((∑ a, (dvec (0, ee j) (incrComp h V a) z) ^ 2)
          - (∑ a, incrComp h V a z * dvec (0, ee j) (incrComp h V a) z) ^ 2
              / (2 * incrQuad h V z)) := by
  have hrsq : (incrMod h V z) ^ 2 = 2 * incrQuad h V z := incrMod_sq (le_of_lt hz)
  have hstep : ∀ j : Fin 3, (dvec (0, ee j) (incrMod h V) z) ^ 2
      = (∑ a, incrComp h V a z * dvec (0, ee j) (incrComp h V a) z) ^ 2
          / (2 * incrQuad h V z) := by
    intro j
    rw [dvec_incrMod hV hz (0, ee j), div_pow, hrsq]
  simp only [incrTransDissip, incrDissip_eq_sq, hstep, Finset.sum_sub_distrib]

/-- **C₄₅ — the increment-modulus Gram decomposition.**  Wherever the increment
does not vanish,

`|∇δ_hu|² − |∇|δ_hu||² = |δ_hu|^{-2} ∑_j |δ_hu ∧ ∂_jδ_hu|²`.

The right-hand side is a sum of Gram determinants: the diffusion of the vector
increment is the diffusion of its modulus *plus* an exactly identified
transverse (angular) surplus. -/
theorem increment_modulus_gram_decomposition {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : STime} (hz : 0 < incrQuad h V z) :
    incrTransDissip h V z
      = (1 / (2 * incrQuad h V z))
          * ∑ j, wedgeSq (fun a => incrComp h V a z)
              (fun a => dvec (0, ee j) (incrComp h V a) z) := by
  have hnorm : ∑ a, (incrComp h V a z) ^ 2 = 2 * incrQuad h V z := (two_incrQuad_eq h V z).symm
  have hpos : (0:ℝ) < 2 * incrQuad h V z := by linarith
  rw [incrTransDissip_eq hV hz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlag := lagrange_gram_three (fun a => incrComp h V a z)
    (fun a => dvec (0, ee j) (incrComp h V a) z)
  rw [hnorm] at hlag
  field_simp
  linarith [hlag]

/-- The transverse dissipation is nonnegative: the vector increment always
diffuses at least as much as its modulus. -/
theorem incrTransDissip_nonneg {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {z : STime} (hz : 0 < incrQuad h V z) : 0 ≤ incrTransDissip h V z := by
  rw [increment_modulus_gram_decomposition hV hz]
  have h1 : (0:ℝ) ≤ 1 / (2 * incrQuad h V z) := by positivity
  have h2 : (0:ℝ) ≤ ∑ j, wedgeSq (fun a => incrComp h V a z)
      (fun a => dvec (0, ee j) (incrComp h V a) z) :=
    Finset.sum_nonneg fun j _ => wedgeSq_nonneg _ _
  exact mul_nonneg h1 h2

/-! ## The transverse part of the transported derivative -/

/-- The transported derivative `d_a = ∑_j δ_hu_j ∂_j δ_hu_a`. -/
def incrTransport (h : E3) (V : STime → E3) (a : Fin 3) : STime → ℝ :=
  fun z => ∑ j, incrComp h V j z * dvec (0, ee j) (incrComp h V a) z

/-- The transverse (projected) transported derivative `d_⊥ = P_⊥(δ_hu·∇)δ_hu`. -/
def incrTransportPerp (h : E3) (V : STime → E3) (a : Fin 3) : STime → ℝ :=
  fun z => incrTransport h V a z
    - (∑ b, incrComp h V b z * incrTransport h V b z) / (2 * incrQuad h V z)
        * incrComp h V a z

/-- The transverse stretching pairing `u_⊥·d_⊥`. -/
def incrPerpPair (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => incrTransfer h V z
    - incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
        / (2 * incrQuad h V z)

/-- `∑_b δ_hu_b d_b = ∑_j δ_hu_j ∂_jq`: the radial part of the transported
derivative is the transport of the quadratic density. -/
lemma incr_radial_transport {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (z : STime) :
    (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
      = ∑ b, incrComp h V b z * incrTransport h V b z := by
  have hdq : ∀ j : Fin 3, dvec (0, ee j) (incrQuad h V) z
      = ∑ i, incrComp h V i z * dvec (0, ee j) (incrComp h V i) z := fun j =>
    dvec_quad (incrComp h V) (fun i => contDiff_incrComp h hV i) (0, ee j) z
  simp only [hdq, incrTransport, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

/-- The transverse pairing is the `u`-contraction of the transverse transported
derivative. -/
lemma incrPerpPair_eq_pairing {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (z : STime) :
    incrPerpPair h V z = ∑ a, V z a * incrTransportPerp h V a z := by
  have htr : incrTransfer h V z = ∑ a, V z a * incrTransport h V a z := by
    simp only [incrTransfer, incrTransport, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : incrPair h V z * (∑ b, incrComp h V b z * incrTransport h V b z)
        / (2 * incrQuad h V z)
      = ∑ a, V z a * ((∑ b, incrComp h V b z * incrTransport h V b z)
          / (2 * incrQuad h V z) * incrComp h V a z) := by
    rw [incrPair, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [incrPerpPair, htr, incr_radial_transport hV z, h2]
  simp only [incrTransportPerp, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- **The transverse stretching is bounded by the transverse dissipation.**
`|P_⊥(δ_hu·∇)δ_hu|² ≤ |δ_hu|²·(|∇δ_hu|² − |∇|δ_hu||²)`; the surviving
stretching channel and the previously unused diffusion surplus live in exactly
the same transverse geometry. -/
theorem incrTransportPerp_sq_le {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {z : STime} (hz : 0 < incrQuad h V z) :
    ∑ a, (incrTransportPerp h V a z) ^ 2
      ≤ (2 * incrQuad h V z) * incrTransDissip h V z := by
  have hR : (0:ℝ) < 2 * incrQuad h V z := by linarith
  have hnorm : ∑ a, (fun b => incrComp h V b z) a ^ 2 = 2 * incrQuad h V z :=
    (two_incrQuad_eq h V z).symm
  have hperp : ∀ a : Fin 3, incrTransportPerp h V a z
      = ∑ j, incrComp h V j z * (dvec (0, ee j) (incrComp h V a) z
          - ((∑ i, incrComp h V i z * dvec (0, ee j) (incrComp h V i) z)
              / (2 * incrQuad h V z)) * incrComp h V a z) := fun a =>
    perp_contraction_eq (fun b => incrComp h V b z)
      (fun j b => dvec (0, ee j) (incrComp h V b) z) (2 * incrQuad h V z) a
  calc ∑ a, (incrTransportPerp h V a z) ^ 2
      = ∑ a, (∑ j, (fun b => incrComp h V b z) j
          * ((fun j b => dvec (0, ee j) (incrComp h V b) z) j a
            - ((∑ i, (fun b => incrComp h V b z) i
                * (fun j b => dvec (0, ee j) (incrComp h V b) z) j i)
              / (2 * incrQuad h V z)) * (fun b => incrComp h V b z) a)) ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hperp a]
    _ ≤ (2 * incrQuad h V z) * ∑ j, ((∑ a, (fun j b => dvec (0, ee j) (incrComp h V b) z) j a ^ 2)
          - (∑ a, (fun b => incrComp h V b z) a
              * (fun j b => dvec (0, ee j) (incrComp h V b) z) j a) ^ 2
            / (2 * incrQuad h V z)) :=
        transverse_contraction_le _ _ hR hnorm
    _ = (2 * incrQuad h V z) * incrTransDissip h V z := by rw [incrTransDissip_eq hV hz]

/-! ## C₄₇ (analytic half): the transverse pairing is absorbable -/

/-- The transverse stretching pairing obeys
`|u_⊥·d_⊥| ≤ |u|·|δ_hu|·√(|∇δ_hu|² − |∇|δ_hu||²)`. -/
theorem incrPerpPair_abs_le {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {z : STime} (hz : 0 < incrQuad h V z) :
    |incrPerpPair h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2)
          * (incrMod h V z * Real.sqrt (incrTransDissip h V z)) := by
  have hT : 0 ≤ incrTransDissip h V z := incrTransDissip_nonneg hV hz
  have hU : (0:ℝ) ≤ ∑ a, (V z a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP : (0:ℝ) ≤ ∑ a, (incrTransportPerp h V a z) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := gram_nonneg (fun a => V z a) (fun a => incrTransportPerp h V a z)
  have hpair : incrPerpPair h V z = ∑ a, V z a * incrTransportPerp h V a z :=
    incrPerpPair_eq_pairing hV z
  have habs : |incrPerpPair h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2) * Real.sqrt (∑ a, (incrTransportPerp h V a z) ^ 2) := by
    rw [hpair, ← Real.sqrt_mul hU, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  have hmodT : Real.sqrt (∑ a, (incrTransportPerp h V a z) ^ 2)
      ≤ incrMod h V z * Real.sqrt (incrTransDissip h V z) := by
    have hle := incrTransportPerp_sq_le hV hz
    have hsq : (incrMod h V z * Real.sqrt (incrTransDissip h V z)) ^ 2
        = (2 * incrQuad h V z) * incrTransDissip h V z := by
      rw [mul_pow, incrMod_sq (le_of_lt hz), Real.sq_sqrt hT]
    have hnn : 0 ≤ incrMod h V z * Real.sqrt (incrTransDissip h V z) :=
      mul_nonneg (incrMod_nonneg h V z) (Real.sqrt_nonneg _)
    rw [show incrMod h V z * Real.sqrt (incrTransDissip h V z)
        = Real.sqrt ((incrMod h V z * Real.sqrt (incrTransDissip h V z)) ^ 2) from
      (Real.sqrt_sq hnn).symm, hsq]
    exact Real.sqrt_le_sqrt hle
  calc |incrPerpPair h V z|
      ≤ Real.sqrt (∑ a, (V z a) ^ 2) * Real.sqrt (∑ a, (incrTransportPerp h V a z) ^ 2) := habs
    _ ≤ Real.sqrt (∑ a, (V z a) ^ 2) * (incrMod h V z * Real.sqrt (incrTransDissip h V z)) :=
        mul_le_mul_of_nonneg_left hmodT (Real.sqrt_nonneg _)

/-- **The transverse absorption (analytic half of C₄₇).**  With the modulus
entropy the surviving stretching source is `β'(q)·u_⊥·d_⊥ = r^{-1}u_⊥·d_⊥`, and
Young's inequality absorbs it into the transverse viscous term
`ν(|∇δ_hu|² − |∇|δ_hu||²)/r` produced by the modulus chain rule, at the price of

`|u|²·r/(2ν)`,

a source **linear** in the De Giorgi variable `r = |δ_hu|`, with no strain
norm, no gradient of `u` and no level-set exponent. -/
theorem modulus_transverse_absorption {nu : ℝ} (hnu : 0 < nu) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : STime} (hz : 0 < incrQuad h V z) :
    |incrPerpPair h V z| / incrMod h V z
      ≤ nu / 2 * (incrTransDissip h V z / incrMod h V z)
        + incrMod h V z * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  have hr : 0 < incrMod h V z := incrMod_pos hz
  have hT : 0 ≤ incrTransDissip h V z := incrTransDissip_nonneg hV hz
  have hU : (0:ℝ) ≤ ∑ a, (V z a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set A : ℝ := Real.sqrt (incrTransDissip h V z) with hA
  set B : ℝ := Real.sqrt (∑ a, (V z a) ^ 2) with hB
  have hA2 : A ^ 2 = incrTransDissip h V z := Real.sq_sqrt hT
  have hB2 : B ^ 2 = ∑ a, (V z a) ^ 2 := Real.sq_sqrt hU
  have hAB : 0 ≤ A := Real.sqrt_nonneg _
  have hBB : 0 ≤ B := Real.sqrt_nonneg _
  have hkey : |incrPerpPair h V z| / incrMod h V z ≤ B * A := by
    have := incrPerpPair_abs_le hV hz
    rw [div_le_iff₀ hr]
    calc |incrPerpPair h V z| ≤ B * (incrMod h V z * A) := this
      _ = B * A * incrMod h V z := by ring
  have hyoung : B * A ≤ nu / 2 * (A ^ 2 / incrMod h V z)
      + incrMod h V z * B ^ 2 / (2 * nu) := by
    have hsq : 0 ≤ (nu * A / incrMod h V z - B) ^ 2 := sq_nonneg _
    have hexp : (nu * A / incrMod h V z - B) ^ 2
        = nu ^ 2 * A ^ 2 / (incrMod h V z) ^ 2 - 2 * (nu * A * B / incrMod h V z) + B ^ 2 := by
      field_simp
      ring
    rw [hexp] at hsq
    have hmul : 0 ≤ incrMod h V z / (2 * nu) := by positivity
    have := mul_le_mul_of_nonneg_left (by linarith : 2 * (nu * A * B / incrMod h V z)
        ≤ nu ^ 2 * A ^ 2 / (incrMod h V z) ^ 2 + B ^ 2) hmul
    have hne : incrMod h V z ≠ 0 := ne_of_gt hr
    have hnune : nu ≠ 0 := ne_of_gt hnu
    calc B * A = incrMod h V z / (2 * nu) * (2 * (nu * A * B / incrMod h V z)) := by
          field_simp
      _ ≤ incrMod h V z / (2 * nu)
            * (nu ^ 2 * A ^ 2 / (incrMod h V z) ^ 2 + B ^ 2) := this
      _ = nu / 2 * (A ^ 2 / incrMod h V z) + incrMod h V z * B ^ 2 / (2 * nu) := by
          field_simp
  rw [hA2, hB2] at hyoung
  linarith

end ClayNS
