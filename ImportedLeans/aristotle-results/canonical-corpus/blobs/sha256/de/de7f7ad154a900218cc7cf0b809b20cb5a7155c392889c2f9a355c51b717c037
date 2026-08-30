/-
# Separable exponential weights on the periodic cell

A reusable calculus framework for weights of the shape

  `Φ(x) = exp( c · Σ_j ψ(x_j − x₀_j) )`,

with `ψ` a fixed smooth scalar profile.  Every weight used in the Gaussian
approximate-adjoint tranche (`GaussianApproximateAdjoint.lean`) is of this
form, and this file computes, once and for all,

* `ClayNS.dvec_sepExp` — the spatial derivative `∂_iΦ = c ψ′(y_i) Φ`;
* `ClayNS.dtime_sepExp` — the time derivative vanishes (`Φ` is static);
* `ClayNS.lap_sepExp` — the Laplacian
  `ΔΦ = ( Σ_i [ c ψ″(y_i) + c² ψ′(y_i)² ] ) Φ`;
* `ClayNS.contDiff_sepExp`, `ClayNS.spacePeriodic_sepExp` — smoothness, and
  `ℤ³`-periodicity as soon as `ψ` has period `1`.

The two instantiations used downstream are `ψ(s) = s²` (the Euclidean
Gaussian) and `ψ(s) = sin(πs)²/π²` (its periodic — torus — analogue).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.AdjointLocalizedIncrement

open Real

noncomputable section

namespace ClayNS

/-! ## The spacetime coordinate functionals -/

/-- The `j`-th spatial coordinate of a spacetime point, as a continuous linear
functional on `STime = ℝ × ℝ³`. -/
def stCoordProj (j : Fin 3) : STime →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.snd ℝ ℝ E3)

@[simp] lemma stCoordProj_apply (j : Fin 3) (z : STime) : stCoordProj j z = z.2 j := rfl

lemma stCoordProj_space (i j : Fin 3) :
    stCoordProj j ((0 : ℝ), ee i) = (if j = i then (1 : ℝ) else 0) := by
  show (ee i) j = _
  simp [ee, EuclideanSpace.single_apply]

lemma stCoordProj_time (j : Fin 3) : stCoordProj j ((1 : ℝ), (0 : E3)) = 0 := by
  show (0 : E3) j = _
  simp

/-! ## The separable weight -/

/-- `Σ_j ψ(x_j − x₀_j)`, a static (time-independent) spacetime scalar. -/
def sepSum (psi : ℝ → ℝ) (x0 : E3) : STime → ℝ := fun z => ∑ j, psi (z.2 j - x0 j)

/-- The separable exponential weight `exp(c · Σ_j ψ(x_j − x₀_j))`. -/
def sepExp (c : ℝ) (psi : ℝ → ℝ) (x0 : E3) : STime → ℝ :=
  fun z => Real.exp (c * sepSum psi x0 z)

lemma sepExp_pos (c : ℝ) (psi : ℝ → ℝ) (x0 : E3) (z : STime) : 0 < sepExp c psi x0 z :=
  Real.exp_pos _

lemma sepExp_nonneg (c : ℝ) (psi : ℝ → ℝ) (x0 : E3) (z : STime) : 0 ≤ sepExp c psi x0 z :=
  (sepExp_pos c psi x0 z).le

/-- With a nonpositive coefficient and a nonnegative profile the weight is at
most `1`. -/
lemma sepExp_le_one {c : ℝ} (hc : c ≤ 0) {psi : ℝ → ℝ} (hpsi : ∀ s, 0 ≤ psi s) (x0 : E3)
    (z : STime) : sepExp c psi x0 z ≤ 1 := by
  have hs : 0 ≤ sepSum psi x0 z := Finset.sum_nonneg fun j _ => hpsi _
  exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc hs)

/-- At the centre of the weight (`x = x₀`) the value is exactly `1`, provided
`ψ(0) = 0`. -/
lemma sepExp_center {psi : ℝ → ℝ} (hpsi0 : psi 0 = 0) (c : ℝ) (x0 : E3) (t : ℝ) :
    sepExp c psi x0 (t, x0) = 1 := by
  have : sepSum psi x0 (t, x0) = 0 := by
    simp [sepSum, hpsi0]
  simp [sepExp, this]

/-! ## Differentiation -/

lemma hasFDerivAt_coordSub (x0 : E3) (j : Fin 3) (z : STime) :
    HasFDerivAt (fun w : STime => w.2 j - x0 j) (stCoordProj j) z := by
  simpa using ((stCoordProj j).hasFDerivAt).sub_const (x0 j)

lemma hasFDerivAt_sepSum {psi psi1 : ℝ → ℝ} (h : ∀ s, HasDerivAt psi (psi1 s) s)
    (x0 : E3) (z : STime) :
    HasFDerivAt (sepSum psi x0) (∑ j, (psi1 (z.2 j - x0 j)) • (stCoordProj j)) z := by
  refine HasFDerivAt.fun_sum fun j _ => ?_
  simpa using (h (z.2 j - x0 j)).comp_hasFDerivAt z (hasFDerivAt_coordSub x0 j z)

lemma hasFDerivAt_sepExp {psi psi1 : ℝ → ℝ} (h : ∀ s, HasDerivAt psi (psi1 s) s)
    (c : ℝ) (x0 : E3) (z : STime) :
    HasFDerivAt (sepExp c psi x0)
      ((c * sepExp c psi x0 z) • (∑ j, (psi1 (z.2 j - x0 j)) • (stCoordProj j))) z := by
  have h1 := (hasFDerivAt_sepSum h x0 z).const_mul c
  have h2 := (Real.hasDerivAt_exp (c * sepSum psi x0 z)).comp_hasFDerivAt z h1
  simpa [sepExp, smul_smul, mul_comm] using h2

/-- **The spatial derivative of a separable weight.** -/
theorem dvec_sepExp {psi psi1 : ℝ → ℝ} (h : ∀ s, HasDerivAt psi (psi1 s) s)
    (c : ℝ) (x0 : E3) (i : Fin 3) (z : STime) :
    dvec (0, ee i) (sepExp c psi x0) z = c * psi1 (z.2 i - x0 i) * sepExp c psi x0 z := by
  rw [dvec, (hasFDerivAt_sepExp h c x0 z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, stCoordProj_space,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **A separable weight is static:** its time derivative vanishes. -/
theorem dtime_sepExp {psi psi1 : ℝ → ℝ} (h : ∀ s, HasDerivAt psi (psi1 s) s)
    (c : ℝ) (x0 : E3) (z : STime) :
    dvec (1, 0) (sepExp c psi x0) z = 0 := by
  rw [dvec, (hasFDerivAt_sepExp h c x0 z).fderiv]
  simp

/-- **The Laplacian of a separable weight.** -/
theorem lap_sepExp {psi psi1 psi2 : ℝ → ℝ} (h : ∀ s, HasDerivAt psi (psi1 s) s)
    (h2 : ∀ s, HasDerivAt psi1 (psi2 s) s) (c : ℝ) (x0 : E3) (z : STime) :
    lap (sepExp c psi x0) z
      = (∑ i, (c * psi2 (z.2 i - x0 i) + c ^ 2 * psi1 (z.2 i - x0 i) ^ 2))
          * sepExp c psi x0 z := by
  have key : ∀ i : Fin 3, (fun w : STime => dspace (sepExp c psi x0) i w)
      = fun w : STime => c * psi1 (w.2 i - x0 i) * sepExp c psi x0 w := by
    intro i; funext w; exact dvec_sepExp h c x0 i w
  have hd : ∀ i : Fin 3,
      dspace (fun w : STime => c * psi1 (w.2 i - x0 i) * sepExp c psi x0 w) i z
        = (c * psi2 (z.2 i - x0 i) + c ^ 2 * psi1 (z.2 i - x0 i) ^ 2) * sepExp c psi x0 z := by
    intro i
    have hA : HasFDerivAt (fun w : STime => c * psi1 (w.2 i - x0 i))
        ((c * psi2 (z.2 i - x0 i)) • stCoordProj i) z := by
      have hcomp := (h2 (z.2 i - x0 i)).comp_hasFDerivAt z (hasFDerivAt_coordSub x0 i z)
      simpa [smul_smul, mul_comm] using hcomp.const_mul c
    rw [dspace, (hA.fun_mul (hasFDerivAt_sepExp h c x0 z)).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, stCoordProj_space, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [lap, Finset.sum_congr rfl fun i _ => by rw [key i, hd i], ← Finset.sum_mul]

/-! ## Smoothness and periodicity -/

lemma contDiff_sepSum {psi : ℝ → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (x0 : E3) :
    ContDiff ℝ (⊤ : ℕ∞) (sepSum psi x0) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  refine ContDiffAt.sum fun j _ => ?_
  exact (hpsi.contDiffAt).comp z
    (((stCoordProj j).contDiff.sub contDiff_const).contDiffAt)

lemma contDiff_sepExp {psi : ℝ → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (c : ℝ) (x0 : E3) :
    ContDiff ℝ (⊤ : ℕ∞) (sepExp c psi x0) :=
  Real.contDiff_exp.comp (contDiff_const.mul (contDiff_sepSum hpsi x0))

lemma continuous_sepExp {psi : ℝ → ℝ} (hpsi : Continuous psi) (c : ℝ) (x0 : E3) :
    Continuous (sepExp c psi x0) := by
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  exact continuous_finset_sum _ fun j _ =>
    hpsi.comp (((stCoordProj j).continuous).sub continuous_const)

/-- A separable weight built from a `1`-periodic profile is `ℤ³`-periodic. -/
lemma spacePeriodic_sepExp {psi : ℝ → ℝ} (hper : ∀ s, psi (s + 1) = psi s)
    (c : ℝ) (x0 : E3) : SpacePeriodic (sepExp c psi x0) := by
  intro z j
  have hsum : sepSum psi x0 (z.1, z.2 + ee j) = sepSum psi x0 z := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = j
    · subst hk
      have : (z.2 + ee k) k = z.2 k + 1 := by simp [ee, EuclideanSpace.single_apply]
      rw [this, show z.2 k + 1 - x0 k = (z.2 k - x0 k) + 1 by ring, hper]
    · have : (z.2 + ee j) k = z.2 k := by
        simp [ee, EuclideanSpace.single_apply, hk]
      rw [this]
  simp [sepExp, hsum]

end ClayNS
