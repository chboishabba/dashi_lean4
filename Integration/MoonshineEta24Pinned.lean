import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.Analysis.Calculus.LogDeriv
import Integration.MoonshineEisensteinAnalytic
import Integration.MoonshineEisensteinAgdaTarget

/-!
# eta^24 modularity at the pinned Mathlib v4.28.0 dependency

The later Mathlib discriminant module uses complex square-root calculus to
derive the eta S-transformation and then raises to the 24th power.

That square-root derivative package is not present at the repository's pinned
v4.28.0 dependency.  For the Moonshine lane we only need eta^24, so we can
avoid square roots entirely.

We compare logarithmic derivatives of

  F(z) = eta(-1/z)^24
  G(z) = z^12 * eta(z)^24.

Using the already-pinned theorems

  logDeriv eta = (pi*i/12) E2
  E2 |_2 S = E2 - correction,

their logarithmic derivatives agree on the upper half-plane.  Nonvanishing and
preconnectedness then imply F = c * G.  Evaluating at i, which is fixed by S
and satisfies i^12 = 1, gives c = 1.

Thus eta^24 itself satisfies the weight-12 S law without a Mathlib dependency
bump.
-/

namespace Integration.MoonshineEta24Pinned

open Function Complex SlashInvariantForm Filter
open UpperHalfPlane hiding I
open ModularForm ModularGroup
open EisensteinSeries
open scoped MatrixGroups Real Topology

noncomputable section

def eta24 (z : ℂ) : ℂ :=
  ModularForm.eta z ^ 24

def etaInv (z : ℂ) : ℂ :=
  ModularForm.eta (-1 / z)

def etaInv24 (z : ℂ) : ℂ :=
  etaInv z ^ 24

def weightedEta24 (z : ℂ) : ℂ :=
  z ^ 12 * eta24 z

theorem etaInv_logDeriv (z : ℍ) :
    logDeriv etaInv z =
      ((z : ℂ) ^ (2 : ℤ))⁻¹ *
        logDeriv ModularForm.eta (-(z : ℂ))⁻¹ := by
  unfold etaInv
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp, mul_comm]
  · simp [zpow_ofNat]
  · exact ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (by grind [UpperHalfPlane.im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

theorem etaInv24_logDeriv (z : ℍ) :
    logDeriv etaInv24 z =
      24 * logDeriv etaInv z := by
  unfold etaInv24
  exact logDeriv_fun_pow
    (by
      unfold etaInv
      exact
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
          (by grind [UpperHalfPlane.im_pnat_div_pos 1 z])).comp
          z
          (by fun_prop (disch := exact z.ne_zero)))
    24

theorem eta24_logDeriv (z : ℍ) :
    logDeriv eta24 z =
      24 * logDeriv ModularForm.eta z := by
  unfold eta24
  exact logDeriv_fun_pow
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.2)
    24

theorem weightedEta24_logDeriv (z : ℍ) :
    logDeriv weightedEta24 z =
      12 / (z : ℂ) + 24 * logDeriv ModularForm.eta z := by
  unfold weightedEta24
  rw [logDeriv_mul]
  · rw [logDeriv_pow, eta24_logDeriv]
  · exact pow_ne_zero 12 z.ne_zero
  · exact pow_ne_zero 24 (ModularForm.eta_ne_zero z.2)
  · fun_prop
  · exact
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).pow 24

private theorem e2_S_pointwise (z : ℍ) :
    ((z : ℂ) ^ 2)⁻¹ * E2 (ModularGroup.S • z) =
      E2 z + 6 / (Real.pi * I * (z : ℂ)) := by
  have hE2 := congrFun (E2_slash_action ModularGroup.S) z
  simp only [one_div, SL_slash_def, modular_S_smul,
    ModularGroup.denom_S, Int.reduceNeg, zpow_neg,
    riemannZeta_two, mul_inv_rev, inv_div,
    Pi.sub_apply, Pi.smul_apply, D2,
    smul_eq_mul] at hE2
  field_simp [z.ne_zero, Real.pi_ne_zero, I_ne_zero] at hE2 ⊢
  ring_nf at hE2 ⊢
  exact hE2

theorem etaInv24_logDeriv_eq_weighted (z : ℍ) :
    logDeriv etaInv24 z = logDeriv weightedEta24 z := by
  rw [etaInv24_logDeriv, etaInv_logDeriv,
      ModularForm.logDeriv_eta_eq_E2
        (.mk _ z.im_inv_neg_coe_pos),
      weightedEta24_logDeriv,
      ModularForm.logDeriv_eta_eq_E2 z]
  have hE2 := e2_S_pointwise z
  rw [UpperHalfPlane.modular_S_smul] at hE2
  simp only [neg_div, one_div] at hE2
  field_simp [z.ne_zero, Real.pi_ne_zero, I_ne_zero] at hE2 ⊢
  ring_nf at hE2 ⊢
  exact hE2

private theorem etaInv24_differentiableOn :
    DifferentiableOn ℂ etaInv24 upperHalfPlaneSet := by
  intro z hz
  unfold etaInv24 etaInv
  exact
    (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (by
        have hpos : 0 < (-1 / z).im := by
          simpa [neg_div] using
            UpperHalfPlane.im_pnat_div_pos 1 ⟨z, hz⟩
        exact hpos)).comp z
      (by fun_prop (disch := exact (⟨z, hz⟩ : ℍ).ne_zero))).pow 24).differentiableWithinAt

private theorem weightedEta24_differentiableOn :
    DifferentiableOn ℂ weightedEta24 upperHalfPlaneSet := by
  intro z hz
  unfold weightedEta24 eta24
  exact
    ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w ^ 12) z).mul
      ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 24))
      |>.differentiableWithinAt

private theorem etaInv24_ne_zero_on :
    ∀ z ∈ upperHalfPlaneSet, etaInv24 z ≠ 0 := by
  intro z hz
  unfold etaInv24 etaInv
  apply pow_ne_zero
  exact ModularForm.eta_ne_zero
    (by
      have hpos : 0 < (-1 / z).im := by
        simpa [neg_div] using
          UpperHalfPlane.im_pnat_div_pos 1 ⟨z, hz⟩
      exact hpos)

private theorem weightedEta24_ne_zero_on :
    ∀ z ∈ upperHalfPlaneSet, weightedEta24 z ≠ 0 := by
  intro z hz
  unfold weightedEta24 eta24
  exact mul_ne_zero
    (pow_ne_zero 12 (⟨z, hz⟩ : ℍ).ne_zero)
    (pow_ne_zero 24 (ModularForm.eta_ne_zero hz))

theorem etaInv24_eq_weighted_on :
    upperHalfPlaneSet.EqOn etaInv24 weightedEta24 := by
  have hlog :
      upperHalfPlaneSet.EqOn
        (logDeriv etaInv24)
        (logDeriv weightedEta24) := by
    intro z hz
    exact etaInv24_logDeriv_eq_weighted ⟨z, hz⟩
  rw [logDeriv_eqOn_iff
      etaInv24_differentiableOn
      weightedEta24_differentiableOn
      isOpen_upperHalfPlaneSet
      (Convex.isPreconnected (convex_halfSpace_im_gt 0))
      weightedEta24_ne_zero_on
      etaInv24_ne_zero_on] at hlog
  obtain ⟨c, hc, hEq⟩ := hlog

  have hI := hEq I (by simp)
  have hetaI : ModularForm.eta I ≠ 0 :=
    ModularForm.eta_ne_zero (by simp)
  have hcOne : c = 1 := by
    simp [etaInv24, etaInv, weightedEta24, eta24] at hI
    have hI12 : (I : ℂ) ^ 12 = 1 := by norm_num [pow_succ]
    rw [hI12, one_mul] at hI
    exact mul_left_cancel₀ (pow_ne_zero 24 hetaI) hI.symm

  intro z hz
  have hzEq := hEq z hz
  simpa [hcOne] using hzEq

/-- Upper-half-plane reflection preserving positive imaginary part. -/
abbrev negConj :=
  Integration.MoonshineEisensteinAgdaTarget.negConj

@[simp]
theorem negConj_coe (z : ℍ) :
    ((negConj z : ℍ) : ℂ) = -conj (z : ℂ) :=
  Integration.MoonshineEisensteinAgdaTarget.negConj_coe z

/-- Every eta q-product factor has the expected real-coefficient conjugation
symmetry under z -> -conj z. -/
theorem eta_q_negConj (n : ℕ) (z : ℍ) :
    ModularForm.eta_q n (-(conj (z : ℂ))) =
      conj (ModularForm.eta_q n (z : ℂ)) := by
  rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp, ← Complex.exp_conj]
  congr 1
  simp
  ring

/-- The infinite Euler product in eta commutes with the upper-half-plane
real-structure reflection. -/
theorem eta_tprod_negConj (z : ℍ) :
    (∏' n, (1 - ModularForm.eta_q n (-(conj (z : ℂ))))) =
      conj (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) := by
  have hz :
      HasProd
        (fun n => 1 - ModularForm.eta_q n (z : ℂ))
        (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) :=
    ModularForm.multipliableLocallyUniformlyOn_eta
      |>.hasProdLocallyUniformlyOn
      |>.hasProd z.2
  have hmap :=
    hz.map Complex.conjAe.toMonoidHom Complex.continuous_conj
  have hneg :
      HasProd
        (fun n => 1 - ModularForm.eta_q n (-(conj (z : ℂ))))
        (∏' n, (1 - ModularForm.eta_q n (-(conj (z : ℂ))))) :=
    ModularForm.multipliableLocallyUniformlyOn_eta
      |>.hasProdLocallyUniformlyOn
      |>.hasProd (by simpa using z.2)
  apply hneg.unique
  convert hmap using 1
  funext n
  simp [Function.comp_apply, eta_q_negConj]

/-- The q^(1/24) prefactor has the same conjugation symmetry. -/
theorem qParam24_negConj (z : ℍ) :
    Periodic.qParam 24 (-(conj (z : ℂ))) =
      conj (Periodic.qParam 24 (z : ℂ)) := by
  unfold Periodic.qParam
  rw [← Complex.exp_conj]
  congr 1
  simp
  ring

/-- Dedekind eta itself has the expected real-structure symmetry on the upper
half-plane. -/
theorem eta_negConj (z : ℍ) :
    ModularForm.eta (-(conj (z : ℂ))) =
      conj (ModularForm.eta (z : ℂ)) := by
  unfold ModularForm.eta
  rw [qParam24_negConj, eta_tprod_negConj]
  simp

/-- Consequently eta^24 has real Fourier/product structure. -/
theorem eta24_negConj (z : ℍ) :
    eta24 (negConj z) = conj (eta24 z) := by
  unfold eta24
  rw [eta_negConj]
  simp

/-- Direct pointwise weight-12 S transformation of eta^24. -/
theorem eta24_S_pointwise (z : ℍ) :
    eta24 (ModularGroup.S • z) =
      (z : ℂ) ^ 12 * eta24 z := by
  have h := etaInv24_eq_weighted_on (z : ℂ) z.2
  simpa [etaInv24, etaInv, weightedEta24,
    UpperHalfPlane.modular_S_smul, neg_div] using h

/-- Concrete inverse-conjugation reflection identity for eta^24 at the pinned
Mathlib dependency. -/
theorem eta24_inv_conj (z : ℍ) :
    eta24 (ModularGroup.S • negConj z) =
      conj ((z : ℂ) ^ 12 * eta24 z) := by
  rw [eta24_S_pointwise, eta24_negConj]
  simp [negConj, map_mul, map_pow]
  ring

/-- Unit norm gives the reciprocal-conjugate fixed locus. -/
theorem S_negConj_fixed_of_normSq_one
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1) :
    ModularGroup.S • negConj z = z :=
  Integration.MoonshineEisensteinAgdaTarget.S_negConj_fixed_of_normSq_one
    z hunit

/-- Exact fixed-locus value equation for eta^24. -/
theorem eta24_unitCircle_fixed
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1) :
    eta24 z = conj ((z : ℂ) ^ 12 * eta24 z) := by
  have hfix := S_negConj_fixed_of_normSq_one z hunit
  calc
    eta24 z = eta24 (ModularGroup.S • negConj z) := by
      exact congrArg eta24 hfix.symm
    _ = conj ((z : ℂ) ^ 12 * eta24 z) :=
      eta24_inv_conj z

/-- T invariance follows directly from the q-product definition after raising
eta to the 24th power. -/
theorem eta24_T_pointwise (z : ℍ) :
    eta24 (ModularGroup.T • z) = eta24 z := by
  unfold eta24 ModularForm.eta
  rw [UpperHalfPlane.modular_T_smul]
  simp [Periodic.qParam, ModularForm.eta_q,
    ← Complex.exp_periodic (2 * Real.pi * I * (z : ℂ))]
  ring_nf

structure Eta24PinnedBoundary where
  etaNonvanishingReused : Bool
  etaLogDerivativeReused : Bool
  e2STransformReused : Bool
  eta24SWeight12Owned : Bool
  eta24TInvariantOwned : Bool
  etaRealStructureConjugationOwned : Bool
  eta24InverseConjugationReflectionOwned : Bool
  eta24UnitCircleFixedLocusOwned : Bool
  dependencyBumpUsed : Bool
  eta24EqualsNormalizedE4E6Delta : Bool

def eta24PinnedBoundary : Eta24PinnedBoundary where
  etaNonvanishingReused := true
  etaLogDerivativeReused := true
  e2STransformReused := true
  eta24SWeight12Owned := true
  eta24TInvariantOwned := true
  etaRealStructureConjugationOwned := true
  eta24InverseConjugationReflectionOwned := true
  eta24UnitCircleFixedLocusOwned := true
  dependencyBumpUsed := false
  eta24EqualsNormalizedE4E6Delta := false

end

end Integration.MoonshineEta24Pinned
