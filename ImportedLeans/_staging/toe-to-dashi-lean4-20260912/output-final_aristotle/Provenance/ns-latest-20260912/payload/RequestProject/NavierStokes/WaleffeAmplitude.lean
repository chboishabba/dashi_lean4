/-
# The literal Waleffe triad amplitude on the exact `ℂ³` carrier

This file is the Lean re-derivation, over the *real* field (not a rational
bookkeeping carrier), of the algebraic core of the Round 93–94 Waleffe lane:

* the Hermitian pairing `⟪·,·⟫` and the (bilinear) cross product on `ℂ³`;
* the **Waleffe amplitude** of an ordered triad `(u_k, u_p, u_q)`,

    `Z = ⟪u_k , u_p × u_q⟫`,     `A = Re Z`;

* the exact **Lagrange/Binet–Cauchy identity** for complex vectors

    `‖u × v‖² = ‖u‖²‖v‖² − |⟪u,v⟫|²`,

  and its consequence, the amplitude–energy product bound

    `A² ≤ ‖u_k‖² ‖u_p‖² ‖u_q‖²`;

* the exact **damped–forced amplitude tangent**: if each mode obeys
  `u̇_j = −ρ_j u_j + f_j` with real `ρ_j`, then

    `Ȧ = −(ρ_k+ρ_p+ρ_q) A + F`,
    `F = Re( ⟪f_k, u_p×u_q⟫ + ⟪u_k, f_p×u_q⟫ + ⟪u_k, u_p×f_q⟫ )`.

  For the physical Galerkin network `ρ_j = ν|j|²` and `f_j` is the projected
  nonlinear network term, so `F` is exactly the *network forcing* of the triad.

Everything here is proved, no hypothesis is postulated, and all norms are the
genuine Euclidean ones on `ℂ³` (kept in squared form, `nsq`, so that no square
root enters the algebra).
-/
import Mathlib

set_option maxRecDepth 8000

noncomputable section

namespace ClayNS.Waleffe

/-- Hermitian pairing on `ℂ³`: conjugate linear in the first slot. -/
def herm (u v : Fin 3 → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * v i

/-- Squared Euclidean norm of a complex 3-vector. -/
def nsq (u : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

/-- Euclidean norm of a complex 3-vector. -/
def nrm (u : Fin 3 → ℂ) : ℝ := Real.sqrt (nsq u)

/-- The bilinear cross product on `ℂ³`. -/
def cross (u v : Fin 3 → ℂ) : Fin 3 → ℂ := crossProduct u v

/-- The complex Waleffe amplitude `Z = ⟪u_k, u_p × u_q⟫` of an ordered triad. -/
def amplitudeC (uK uP uQ : Fin 3 → ℂ) : ℂ := herm uK (cross uP uQ)

/-- The real Waleffe amplitude `A = Re ⟪u_k, u_p × u_q⟫`. -/
def amplitude (uK uP uQ : Fin 3 → ℂ) : ℝ := (amplitudeC uK uP uQ).re

/-- The complex network forcing of a triad: the three product-rule slots of the
amplitude tangent that are *not* viscous damping. -/
def netForcingC (uK uP uQ fK fP fQ : Fin 3 → ℂ) : ℂ :=
  herm fK (cross uP uQ) + herm uK (cross fP uQ) + herm uK (cross uP fQ)

/-- The real network forcing `F` of a triad. -/
def netForcing (uK uP uQ fK fP fQ : Fin 3 → ℂ) : ℝ :=
  (netForcingC uK uP uQ fK fP fQ).re

/-- **Lagrange / Binet–Cauchy identity on `ℂ³`.**  With the bilinear cross
product and the Hermitian pairing, `‖u × v‖² = ‖u‖²‖v‖² − |⟪u,v⟫|²`. -/
theorem lagrange (u v : Fin 3 → ℂ) :
    nsq (cross u v) = nsq u * nsq v - Complex.normSq (herm u v) := by
  simp [nsq, herm, cross, crossProduct, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem nsq_nonneg (u : Fin 3 → ℂ) : 0 ≤ nsq u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem nrm_nonneg (u : Fin 3 → ℂ) : 0 ≤ nrm u := Real.sqrt_nonneg _

@[simp] theorem nrm_sq (u : Fin 3 → ℂ) : nrm u ^ 2 = nsq u := by
  rw [nrm, Real.sq_sqrt (nsq_nonneg u)]

/-- Cauchy–Schwarz on `ℂ³`, as a corollary of the Lagrange identity. -/
theorem normSq_herm_le (u v : Fin 3 → ℂ) : Complex.normSq (herm u v) ≤ nsq u * nsq v := by
  have h := nsq_nonneg (cross u v)
  have := lagrange u v
  linarith

/-- Squared cross product is dominated by the product of the squared norms. -/
theorem nsq_cross_le (u v : Fin 3 → ℂ) : nsq (cross u v) ≤ nsq u * nsq v := by
  have h : (0:ℝ) ≤ Complex.normSq (herm u v) := Complex.normSq_nonneg _
  have := lagrange u v
  linarith

/-- **Exact Waleffe amplitude–energy product bound** (Round 105, item 5):
`A² ≤ ‖u_k‖²‖u_p‖²‖u_q‖²`. -/
theorem amplitude_sq_le (uK uP uQ : Fin 3 → ℂ) :
    (amplitude uK uP uQ) ^ 2 ≤ nsq uK * (nsq uP * nsq uQ) := by
  have h1 : (amplitude uK uP uQ) ^ 2 ≤ Complex.normSq (amplitudeC uK uP uQ) := by
    rw [Complex.normSq_apply]
    have := sq_nonneg (amplitudeC uK uP uQ).im
    simp only [amplitude, pow_two]
    nlinarith
  have h2 := normSq_herm_le uK (cross uP uQ)
  have h3 := nsq_cross_le uP uQ
  have h4 := nsq_nonneg uK
  calc (amplitude uK uP uQ) ^ 2 ≤ Complex.normSq (amplitudeC uK uP uQ) := h1
    _ ≤ nsq uK * nsq (cross uP uQ) := h2
    _ ≤ nsq uK * (nsq uP * nsq uQ) := by nlinarith

/-- The amplitude bound in unsquared form: `|A| ≤ ‖u_k‖‖u_p‖‖u_q‖`. -/
theorem abs_amplitude_le (uK uP uQ : Fin 3 → ℂ) :
    |amplitude uK uP uQ| ≤ nrm uK * nrm uP * nrm uQ := by
  have h := amplitude_sq_le uK uP uQ
  calc |amplitude uK uP uQ| = Real.sqrt ((amplitude uK uP uQ) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (nsq uK * (nsq uP * nsq uQ)) := Real.sqrt_le_sqrt h
    _ = nrm uK * nrm uP * nrm uQ := by
        rw [Real.sqrt_mul (nsq_nonneg uK), Real.sqrt_mul (nsq_nonneg uP), nrm, nrm, nrm]
        ring

/-- The network forcing obeys the same triple-product majorant, term by term. -/
theorem abs_netForcing_le (uK uP uQ fK fP fQ : Fin 3 → ℂ) :
    |netForcing uK uP uQ fK fP fQ|
      ≤ nrm fK * nrm uP * nrm uQ + nrm uK * nrm fP * nrm uQ
        + nrm uK * nrm uP * nrm fQ := by
  have h : netForcing uK uP uQ fK fP fQ
      = amplitude fK uP uQ + amplitude uK fP uQ + amplitude uK uP fQ := by
    simp [netForcing, netForcingC, amplitude, amplitudeC, Complex.add_re]
  rw [h]
  calc |amplitude fK uP uQ + amplitude uK fP uQ + amplitude uK uP fQ|
      ≤ |amplitude fK uP uQ + amplitude uK fP uQ| + |amplitude uK uP fQ| := abs_add_le _ _
    _ ≤ (|amplitude fK uP uQ| + |amplitude uK fP uQ|) + |amplitude uK uP fQ| := by
        have := abs_add_le (amplitude fK uP uQ) (amplitude uK fP uQ); linarith
    _ ≤ nrm fK * nrm uP * nrm uQ + nrm uK * nrm fP * nrm uQ
          + nrm uK * nrm uP * nrm fQ := by
        have h1 := abs_amplitude_le fK uP uQ
        have h2 := abs_amplitude_le uK fP uQ
        have h3 := abs_amplitude_le uK uP fQ
        linarith

/-- **Product-rule tangent of the Waleffe amplitude** on the exact `ℂ³`
carrier, for arbitrary modal tangents. -/
theorem amplitudeC_hasDerivAt (uK uP uQ : ℝ → Fin 3 → ℂ) (dK dP dQ : Fin 3 → ℂ) (t : ℝ)
    (hK : ∀ i, HasDerivAt (fun s => uK s i) (dK i) t)
    (hP : ∀ i, HasDerivAt (fun s => uP s i) (dP i) t)
    (hQ : ∀ i, HasDerivAt (fun s => uQ s i) (dQ i) t) :
    HasDerivAt (fun s => amplitudeC (uK s) (uP s) (uQ s))
      (herm dK (cross (uP t) (uQ t)) + herm (uK t) (cross dP (uQ t))
        + herm (uK t) (cross (uP t) dQ)) t := by
  have key : ∀ (i j k : Fin 3),
      HasDerivAt (fun s => star (uK s i) * (uP s j * uQ s k - uP s k * uQ s j))
        (star (dK i) * (uP t j * uQ t k - uP t k * uQ t j)
          + star (uK t i) * ((dP j * uQ t k + uP t j * dQ k)
            - (dP k * uQ t j + uP t k * dQ j))) t :=
    fun i j k => (hK i).star.mul (((hP j).mul (hQ k)).sub ((hP k).mul (hQ j)))
  have h0 := key 0 1 2
  have h1 := key 1 2 0
  have h2 := key 2 0 1
  simp only [amplitudeC, herm, cross, crossProduct, Fin.sum_univ_three, LinearMap.mk₂_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, starRingEnd_apply]
  have := (h0.add h1).add h2
  convert this using 1
  ring

/-- Substituting `d_j = −ρ_j u_j + f_j` into the three product-rule slots
produces exactly `−(ρ_k+ρ_p+ρ_q)·Z + F`. -/
theorem damped_tangent_eq (rK rP rQ : ℝ) (uK uP uQ fK fP fQ : Fin 3 → ℂ) :
    herm (fun i => -(rK : ℂ) * uK i + fK i) (cross uP uQ)
      + herm uK (cross (fun i => -(rP : ℂ) * uP i + fP i) uQ)
      + herm uK (cross uP (fun i => -(rQ : ℂ) * uQ i + fQ i))
    = -((rK + rP + rQ : ℝ) : ℂ) * amplitudeC uK uP uQ + netForcingC uK uP uQ fK fP fQ := by
  simp only [herm, cross, crossProduct, amplitudeC, netForcingC, Fin.sum_univ_three,
    LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_add, map_mul, map_neg, Complex.conj_ofReal,
    Complex.ofReal_add]
  ring

/-- **The literal damped–forced Waleffe amplitude equation.**  If every mode of
the triad obeys `u̇_j = −ρ_j u_j + f_j` with real damping rates `ρ_j`, then the
real amplitude satisfies the scalar damped–forced ODE

  `Ȧ = −(ρ_k+ρ_p+ρ_q) A + F`

with `F` the network forcing.  For the physical Galerkin system `ρ_j = ν|j|²`
and `f_j` is the projected nonlinear network term. -/
theorem amplitude_hasDerivAt_damped (uK uP uQ : ℝ → Fin 3 → ℂ) (fK fP fQ : Fin 3 → ℂ)
    (rK rP rQ : ℝ) (t : ℝ)
    (hK : ∀ i, HasDerivAt (fun s => uK s i) (-(rK : ℂ) * uK t i + fK i) t)
    (hP : ∀ i, HasDerivAt (fun s => uP s i) (-(rP : ℂ) * uP t i + fP i) t)
    (hQ : ∀ i, HasDerivAt (fun s => uQ s i) (-(rQ : ℂ) * uQ t i + fQ i) t) :
    HasDerivAt (fun s => amplitude (uK s) (uP s) (uQ s))
      (-(rK + rP + rQ) * amplitude (uK t) (uP t) (uQ t)
        + netForcing (uK t) (uP t) (uQ t) fK fP fQ) t := by
  have hC := amplitudeC_hasDerivAt uK uP uQ
      (fun i => -(rK : ℂ) * uK t i + fK i) (fun i => -(rP : ℂ) * uP t i + fP i)
      (fun i => -(rQ : ℂ) * uQ t i + fQ i) t hK hP hQ
  rw [damped_tangent_eq rK rP rQ (uK t) (uP t) (uQ t) fK fP fQ] at hC
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hC
  simpa [amplitude, netForcing, Complex.add_re, Complex.mul_re] using hre

end ClayNS.Waleffe
