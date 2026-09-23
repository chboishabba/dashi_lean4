/-
# `F1` as a connected two-slice correlation bound

`Lattice/TransferOperatorGap.lean` reduced the finite side of the mass gap to the
estimate `‖⟪P₀ψ, P₁ψ⟫‖ ≤ c‖ψ‖²` on the vacuum complement.  This file puts that
estimate into the two shapes that constructive field theory actually produces.

* `decorrelation_of_truncated_correlation` — the estimate is exactly a bound on
  the **connected (truncated) two-slice correlation function** of the literal
  Wilson–Gibbs measure: the product term drops out precisely because `ψ` is
  orthogonal to the vacuum.
* `decorrelation_of_uniform_joint_density` — the estimate follows from a
  **uniform mixing condition**: if the joint law of the two time slices has
  density `1 + h` with respect to the product of its marginals, with `‖h‖ ≤ ε`,
  then the decorrelation constant is `ε`.  This is the shape delivered by a
  convergent cluster or polymer expansion, and it makes no reference to operators.

Combining the second with `TransferOperatorGap.trajectory_gap_bound_of_defect`,
the finite-side payment of the Clay problem becomes: *along the trajectory, the
joint two-slice density of the literal Wilson measure deviates from the product
of its marginals by at most `1 − Δ a_k`.*

Neither statement proves the mixing condition, and nothing here is specific to a
volume or a coupling.
-/
import Mathlib
import RequestProject.YangMills.Lattice.TransferOperatorGap

namespace RequestProject.YangMills.Lattice

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## The `L²` norm as an integral -/

/-- The squared norm of a slice wavefunction is the integral of its squared
modulus against the literal Wilson slice measure. -/
theorem integral_norm_sq_slice (hchi : Continuous chi) (beta : ℝ)
    (ψ : SliceL2 n G beta chi) :
    ∫ u, ‖(ψ : _ → ℂ) u‖ ^ 2 ∂(sliceMeasure n G beta chi) = ‖ψ‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) ψ ψ
  have hcast : ⟪ψ, ψ⟫_ℂ
      = ((∫ u, ‖(ψ : _ → ℂ) u‖ ^ 2 ∂(sliceMeasure n G beta chi) : ℝ) : ℂ) := by
    rw [h, ← integral_complex_ofReal]
    congr 1
    funext u
    rw [RCLike.inner_apply, Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hre : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  rw [hcast] at hre
  simpa using hre

/-! ## `F1` as a truncated correlation bound -/

/-- **The two-slice estimate is a bound on the connected correlation function.**
For a wavefunction orthogonal to the vacuum the disconnected term vanishes, so a
bound on the truncated two-slice correlation of the literal Wilson–Gibbs measure
is literally the decorrelation hypothesis. -/
theorem decorrelation_of_truncated_correlation (hchi : Continuous chi) (beta : ℝ)
    {c : ℝ} (ψ : SliceL2 n G beta chi) (hψ : ⟪vacuum hchi beta, ψ⟫_ℂ = 0)
    (hcov : ‖(∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)
          ∂(gibbs n G beta chi))
        - (∫ x, (starRingEnd ℂ) ((ψ : _ → ℂ) x) ∂(sliceMeasure n G beta chi))
          * (∫ y, (ψ : _ → ℂ) y ∂(sliceMeasure n G beta chi))‖ ≤ c * ‖ψ‖ ^ 2) :
    ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2 := by
  have hmean : ∫ y, (ψ : _ → ℂ) y ∂(sliceMeasure n G beta chi) = 0 := by
    rw [← inner_vacuum_eq_integral hchi beta ψ, hψ]
  rw [inner_embed_eq_integral hchi beta ψ ψ]
  simpa [hmean] using hcov

/-! ## `F1` from a uniform mixing (joint density) condition -/

/-- **Uniform mixing implies decorrelation.**  Suppose the joint law of the two
time slices under the literal Wilson–Gibbs measure has density `1 + h` with
respect to the product of its marginals, in the sense that integrals of
product-integrable functions may be computed against `(1 + h)·(ν ⊗ ν)`, and that
`‖h‖ ≤ ε` almost everywhere.  Then every vacuum-orthogonal wavefunction satisfies
the two-slice estimate with constant `ε`.

This is the classical route from a convergent cluster expansion to a transfer
matrix gap, stated on the literal objects: no operator, lattice size or coupling
occurs in the hypothesis. -/
theorem decorrelation_of_uniform_joint_density (hchi : Continuous chi) (beta : ℝ)
    {eps : ℝ} (ψ : SliceL2 n G beta chi) (hψ : ⟪vacuum hchi beta, ψ⟫_ℂ = 0)
    (h : (SliceIdx n → G) × (SliceIdx n → G) → ℂ)
    (hmeas : AEStronglyMeasurable h
      ((sliceMeasure n G beta chi).prod (sliceMeasure n G beta chi)))
    (hbound : ∀ᵐ z ∂((sliceMeasure n G beta chi).prod (sliceMeasure n G beta chi)),
      ‖h z‖ ≤ eps)
    (hdensity : ∀ F : (SliceIdx n → G) × (SliceIdx n → G) → ℂ,
      Integrable F ((sliceMeasure n G beta chi).prod (sliceMeasure n G beta chi)) →
        ∫ U, F (slice0 U, slice1 U) ∂(gibbs n G beta chi)
          = ∫ z, F z * (1 + h z)
              ∂((sliceMeasure n G beta chi).prod (sliceMeasure n G beta chi))) :
    ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ eps * ‖ψ‖ ^ 2 := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  set ν := sliceMeasure n G beta chi with hν
  set f : (SliceIdx n → G) → ℂ := fun u => (ψ : _ → ℂ) u with hf
  have hfint : Integrable f ν := (Lp.memLp ψ).integrable (by norm_num)
  have hconjint : Integrable (fun u => (starRingEnd ℂ) (f u)) ν :=
    ⟨Complex.continuous_conj.comp_aestronglyMeasurable hfint.aestronglyMeasurable, by
      simpa [HasFiniteIntegral] using hfint.2⟩
  set F : (SliceIdx n → G) × (SliceIdx n → G) → ℂ :=
    fun z => (starRingEnd ℂ) (f z.1) * f z.2 with hF
  have hFint : Integrable F (ν.prod ν) := hconjint.mul_prod hfint
  have hFh : Integrable (fun z => h z * F z) (ν.prod ν) :=
    hFint.bdd_mul hmeas hbound
  -- the disconnected term
  have hmean : ∫ y, f y ∂ν = 0 := by
    rw [hf, ← inner_vacuum_eq_integral hchi beta ψ, hψ]
  have hdisc : ∫ z, F z ∂(ν.prod ν) = 0 := by
    have hprod : ∫ z, F z ∂(ν.prod ν)
        = (∫ x, (starRingEnd ℂ) (f x) ∂ν) * (∫ y, f y ∂ν) :=
      integral_prod_mul (μ := ν) (ν := ν) (fun x => (starRingEnd ℂ) (f x)) f
    rw [hprod, hmean, mul_zero]
  -- the inner product is the remainder integral
  have hsplit : ∫ z, F z * (1 + h z) ∂(ν.prod ν) = ∫ z, h z * F z ∂(ν.prod ν) := by
    have hcongr : (fun z => F z * (1 + h z)) = fun z => F z + h z * F z := by
      funext z; ring
    rw [hcongr, integral_add hFint hFh, hdisc, zero_add]
  have hval : ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ
      = ∫ z, h z * F z ∂(ν.prod ν) := by
    rw [inner_embed_eq_integral hchi beta ψ ψ, hdensity F hFint, hsplit]
  -- bound the remainder
  have hnormsq : ∫ u, ‖f u‖ ^ 2 ∂ν = ‖ψ‖ ^ 2 := integral_norm_sq_slice hchi beta ψ
  have hsqint : Integrable (fun u => ‖f u‖ ^ 2) ν := by
    have := (Lp.memLp ψ).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hmaj : Integrable
      (fun z => eps * ((‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2)) (ν.prod ν) := by
    have h1 : Integrable (fun z : (SliceIdx n → G) × (SliceIdx n → G) => ‖f z.1‖ ^ 2)
        (ν.prod ν) := by
      simpa using hsqint.mul_prod (integrable_const (1 : ℝ))
    have h2 : Integrable (fun z : (SliceIdx n → G) × (SliceIdx n → G) => ‖f z.2‖ ^ 2)
        (ν.prod ν) := by
      simpa using (integrable_const (1 : ℝ)).mul_prod hsqint
    exact ((h1.add h2).div_const 2).const_mul eps
  have hptwise : ∀ᵐ z ∂(ν.prod ν),
      ‖h z * F z‖ ≤ eps * ((‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2) := by
    filter_upwards [hbound] with z hz
    have hFnorm : ‖F z‖ = ‖f z.1‖ * ‖f z.2‖ := by
      rw [hF]; simp [norm_mul]
    have hepsnn : 0 ≤ eps := le_trans (norm_nonneg _) hz
    have hamgm : ‖f z.1‖ * ‖f z.2‖ ≤ (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖f z.1‖ - ‖f z.2‖)]
    calc ‖h z * F z‖ = ‖h z‖ * ‖F z‖ := norm_mul _ _
      _ ≤ eps * (‖f z.1‖ * ‖f z.2‖) := by
          rw [hFnorm]
          exact mul_le_mul_of_nonneg_right hz (by positivity)
      _ ≤ eps * ((‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hamgm hepsnn
  have hintmaj : ∫ z, eps * ((‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2) ∂(ν.prod ν)
      = eps * ‖ψ‖ ^ 2 := by
    have h1 : ∫ z : (SliceIdx n → G) × (SliceIdx n → G), ‖f z.1‖ ^ 2 ∂(ν.prod ν)
        = ‖ψ‖ ^ 2 := by
      have := integral_prod_mul (μ := ν) (ν := ν) (fun u => ‖f u‖ ^ 2) (fun _ => (1 : ℝ))
      simpa [hnormsq] using this
    have h2 : ∫ z : (SliceIdx n → G) × (SliceIdx n → G), ‖f z.2‖ ^ 2 ∂(ν.prod ν)
        = ‖ψ‖ ^ 2 := by
      have := integral_prod_mul (μ := ν) (ν := ν) (fun _ => (1 : ℝ)) (fun u => ‖f u‖ ^ 2)
      simpa [hnormsq] using this
    have hsum : Integrable
        (fun z : (SliceIdx n → G) × (SliceIdx n → G) => ‖f z.1‖ ^ 2) (ν.prod ν) := by
      simpa using hsqint.mul_prod (integrable_const (1 : ℝ))
    have hsum2 : Integrable
        (fun z : (SliceIdx n → G) × (SliceIdx n → G) => ‖f z.2‖ ^ 2) (ν.prod ν) := by
      simpa using (integrable_const (1 : ℝ)).mul_prod hsqint
    rw [integral_const_mul, integral_div, integral_add hsum hsum2, h1, h2]
    ring
  rw [hval]
  calc ‖∫ z, h z * F z ∂(ν.prod ν)‖
      ≤ ∫ z, eps * ((‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) / 2) ∂(ν.prod ν) :=
        norm_integral_le_of_norm_le hmaj hptwise
    _ = eps * ‖ψ‖ ^ 2 := hintmaj


/-! ## Non-vacuity: the mixing hypothesis holds exactly at zero coupling -/

/-- **At zero coupling the joint two-slice law *is* the product of its
marginals**, so the mixing hypothesis of
`decorrelation_of_uniform_joint_density` holds with `h = 0` and `eps = 0`, for
every lattice volume.  The hypothesis is therefore not vacuous, and the whole
content of `F1` is how the density deviates from the product as the coupling
flows. -/
theorem uniform_joint_density_zero_coupling (h01 : (0 : ZMod (n + 1)) ≠ 1)
    (hchi : Continuous chi) :
    ∀ F : (SliceIdx n → G) × (SliceIdx n → G) → ℂ,
      Integrable F ((sliceMeasure n G 0 chi).prod (sliceMeasure n G 0 chi)) →
        ∫ U, F (slice0 U, slice1 U) ∂(gibbs n G 0 chi)
          = ∫ z, F z * (1 + (0 : ℂ))
              ∂((sliceMeasure n G 0 chi).prod (sliceMeasure n G 0 chi)) := by
  haveI := isProbabilityMeasure_gibbs (n := n) hchi (0 : ℝ)
  intro F hF
  have hind : IndepFun (slice0 (n := n) (G := G)) slice1 (gibbs n G 0 chi) := by
    rw [gibbs_zero]
    exact indepFun_slice h01
  have hmeas0 : AEMeasurable (slice0 (n := n) (G := G)) (gibbs n G 0 chi) :=
    measurable_slice0.aemeasurable
  have hmeas1 : AEMeasurable (slice1 (n := n) (G := G)) (gibbs n G 0 chi) :=
    (measurePreserving_slice1 hchi (0 : ℝ)).measurable.aemeasurable
  have hjoint : Measure.map (fun U => (slice0 U, slice1 U)) (gibbs n G 0 chi)
      = (sliceMeasure n G 0 chi).prod (sliceMeasure n G 0 chi) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hmeas0 hmeas1).1 hind,
      (measurePreserving_slice0 (0 : ℝ) chi).map_eq,
      (measurePreserving_slice1 hchi (0 : ℝ)).map_eq]
  have hmap : ∫ U, F (slice0 U, slice1 U) ∂(gibbs n G 0 chi)
      = ∫ z, F z ∂(Measure.map (fun U => (slice0 U, slice1 U)) (gibbs n G 0 chi)) := by
    rw [integral_map (hmeas0.prodMk hmeas1) (by rw [hjoint]; exact hF.aestronglyMeasurable)]
  rw [hmap, hjoint]
  simp


/-! ## The trajectory form of the mixing criterion -/

/-- **Uniform mixing along the trajectory gives `F1`.**  If at every step the
joint law of the two time slices of the literal four-dimensional `SU(2)` Wilson
measure has density `1 + h_k` with respect to the product of its marginals, with
`‖h_k‖ ≤ eps k`, and the spectral defect condition `Δ·a_k ≤ 1 − eps k` holds,
then the literal physical Hamiltonians have the uniform vacuum form gap `Δ`
required by the continuum weld. -/
theorem ym_uniform_gap_of_uniform_mixing (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {eps : ℕ → ℝ} {Δ : ℝ}
    (hfun : ∀ k, (SliceIdx (vol k) → SU2) × (SliceIdx (vol k) → SU2) → ℂ)
    (hmeas : ∀ k, AEStronglyMeasurable (hfun k)
      ((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
        (sliceMeasure (vol k) SU2 (beta k) chiSU2)))
    (hbound : ∀ k, ∀ᵐ z ∂((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
        (sliceMeasure (vol k) SU2 (beta k) chiSU2)), ‖hfun k z‖ ≤ eps k)
    (hdensity : ∀ k, ∀ F : (SliceIdx (vol k) → SU2) × (SliceIdx (vol k) → SU2) → ℂ,
      Integrable F ((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
          (sliceMeasure (vol k) SU2 (beta k) chiSU2)) →
        ∫ U, F (slice0 U, slice1 U) ∂(gibbs (vol k) SU2 (beta k) chiSU2)
          = ∫ z, F z * (1 + hfun k z)
              ∂((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
                (sliceMeasure (vol k) SU2 (beta k) chiSU2)))
    (hdefect : ∀ k, Δ * a k ≤ 1 - eps k) :
    ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a (fun k => (hapos k).le) k)
      (ymTrajectoryVacuum vol beta k) Δ :=
  ym_uniform_gap_of_trajectory_decorrelation vol beta a (fun k => (hapos k).le)
    (fun k ψ hψ =>
      decorrelation_of_uniform_joint_density (G := SU2) continuous_chiSU2 (beta k)
        (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2) hψ (hfun k) (hmeas k) (hbound k)
        (hdensity k))
    (trajectory_gap_bound_of_defect hapos hdefect)

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms integral_norm_sq_slice
#print axioms decorrelation_of_truncated_correlation
#print axioms decorrelation_of_uniform_joint_density
#print axioms uniform_joint_density_zero_coupling
#print axioms ym_uniform_gap_of_uniform_mixing

end Audit
