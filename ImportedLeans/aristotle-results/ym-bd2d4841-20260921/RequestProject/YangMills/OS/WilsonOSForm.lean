/-
# The Osterwalder–Schrader form of the literal Wilson measure

With reflection positivity available
(`OS/WilsonReflectionPositivity.lean`), the Osterwalder–Schrader inner product

```
  ⟨F, F'⟩_OS  =  ∫ conj (F (Θ U)) · F' (U) dμ_Gibbs(U)
```

on observables of the closed positive half is a Hermitian, positive
semi-definite sesquilinear form — the form whose quotient and completion is the
physical Hilbert space of the reconstruction.  This file proves the three facts
that make it one:

* `wilsonAction_reflConf` — the literal Wilson action is invariant under the
  time reflection of the gauge field;
* `measurePreserving_reflConf_gibbs` — the Wilson–Gibbs measure is invariant
  under the time reflection;
* `osForm`, `osForm_conj_symm` — the OS form and its Hermitian symmetry
  (an immediate consequence of the previous item);
* `osForm_self_re_nonneg`, `osForm_self_im` — positivity and reality of the
  diagonal, i.e. reflection positivity.

Everything is proved; the hypotheses on the character are those of the physical
Wilson action (`χ` continuous, conjugation invariant, inversion symmetric).
-/
import Mathlib
import RequestProject.YangMills.OS.WilsonReflectionPositivity
import RequestProject.YangMills.OS.ActionSplitting

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **The literal Wilson action is reflection invariant.** -/
theorem wilsonAction_reflConf (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    (U : Conf n G) :
    wilsonAction beta chi (reflConf hN U) = wilsonAction beta chi U := by
  have hinvol : reflConf hN (reflConf hN U) = U := (wilsonReflData hN).confRefl_involutive U
  have hplane : actionOn beta chi (plaqPlane n L) (reflConf hN U)
      = actionOn beta chi (plaqPlane n L) U := by
    refine actionOn_plaqPlane_local beta chi fun l hl => ?_
    exact (wilsonReflData hN).confRefl_plane U (by simpa using hl)
  rw [wilsonAction_split (L := L) beta chi (reflConf hN U), wilsonAction_split (L := L) beta chi U,
    actionOn_plaqNeg_eq hN beta hconj hinv (reflConf hN U),
    actionOn_plaqNeg_eq hN beta hconj hinv U, hinvol, hplane]
  ring

/-- **The literal Wilson–Gibbs measure is reflection invariant.** -/
theorem measurePreserving_reflConf_gibbs (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) :
    MeasurePreserving (reflConf hN (G := G)) (gibbs n G beta chi) (gibbs n G beta chi) :=
  measurePreserving_scaled
    (measurePreserving_withDensity ((wilsonReflData hN).measurePreserving_confRefl)
      (measurable_gibbsDensity hchi beta)
      (fun U => by
        have hact : wilsonAction beta chi ((wilsonReflData hN).confRefl U)
            = wilsonAction beta chi U := wilsonAction_reflConf hN beta hconj hinv U
        simp [gibbsDensity, hact])) _

/-- The Osterwalder–Schrader form of the literal Wilson measure. -/
noncomputable def osForm (hN : n + 1 = 2 * L) (beta : ℝ) (chi : G → ℝ)
    (F F' : Conf n G → ℂ) : ℂ :=
  ∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F' U ∂(gibbs n G beta chi)

/-- **The Osterwalder–Schrader form is Hermitian.**  This uses only reflection
invariance of the Wilson–Gibbs measure and involutivity of the reflection. -/
theorem osForm_conj_symm (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (F F' : Conf n G → ℂ) :
    (starRingEnd ℂ) (osForm hN beta chi F' F) = osForm hN beta chi F F' := by
  have hmp := measurePreserving_reflConf_gibbs hN beta hchi hconj hinv
  have hinvol : ∀ U : Conf n G, reflConf hN (reflConf hN U) = U :=
    (wilsonReflData hN).confRefl_involutive
  have hstep : ∫ U, F' (reflConf hN U) * (starRingEnd ℂ) (F U) ∂(gibbs n G beta chi)
      = ∫ V, F' V * (starRingEnd ℂ) (F (reflConf hN V)) ∂(gibbs n G beta chi) := by
    have := hmp.integral_comp ((wilsonReflData hN).confReflEquiv (G := G)).measurableEmbedding
      (fun V => F' V * (starRingEnd ℂ) (F (reflConf hN V)))
    simpa [hinvol] using this
  calc (starRingEnd ℂ) (osForm hN beta chi F' F)
      = ∫ U, F' (reflConf hN U) * (starRingEnd ℂ) (F U) ∂(gibbs n G beta chi) := by
        rw [osForm, ← integral_conj]
        simp
    _ = ∫ V, F' V * (starRingEnd ℂ) (F (reflConf hN V)) ∂(gibbs n G beta chi) := hstep
    _ = osForm hN beta chi F F' := by
        rw [osForm]
        exact integral_congr_ae (Filter.Eventually.of_forall fun V => by ring)

/-- **Reflection positivity in the form the reconstruction consumes**: the
diagonal of the Osterwalder–Schrader form is nonnegative. -/
theorem osForm_self_re_nonneg (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) {F : Conf n G → ℂ} {MF : ℝ}
    (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ MF)
    (hFloc : ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) → F U = F V) :
    0 ≤ (osForm hN beta chi F F).re :=
  wilson_reflection_positive hN hchi hconj hinv beta hFm hFb hFloc

/-- The diagonal of the Osterwalder–Schrader form is real. -/
theorem osForm_self_im (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (F : Conf n G → ℂ) :
    (osForm hN beta chi F F).im = 0 := by
  have h := osForm_conj_symm hN beta hchi hconj hinv F F
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith


/-! ## Sesquilinearity -/

/-- The Osterwalder–Schrader form is additive in its second argument (for
bounded measurable observables, which is all this file ever uses). -/
theorem osForm_add_right (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ} (hchi : Continuous chi)
    {F F₁ F₂ : Conf n G → ℂ} {MF M₁ M₂ : ℝ}
    (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ MF)
    (hF₁m : Measurable F₁) (hF₁b : ∀ U, ‖F₁ U‖ ≤ M₁)
    (hF₂m : Measurable F₂) (hF₂b : ∀ U, ‖F₂ U‖ ≤ M₂) :
    osForm hN beta chi F (fun U => F₁ U + F₂ U)
      = osForm hN beta chi F F₁ + osForm hN beta chi F F₂ := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  have h0 : Measurable fun U : Conf n G => F (reflConf hN U) :=
    hFm.comp (wilsonReflData hN).measurable_confRefl
  have hrefl : Measurable fun U : Conf n G => (starRingEnd ℂ) (F (reflConf hN U)) :=
    Complex.continuous_conj.measurable.comp h0
  have hint₁ : Integrable (fun U => (starRingEnd ℂ) (F (reflConf hN U)) * F₁ U)
      (gibbs n G beta chi) :=
    integrable_of_bounded _ (hrefl.mul hF₁m) (M := MF * M₁) fun U => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hFb _) (hF₁b U) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hFb (fun _ => 1)))
  have hint₂ : Integrable (fun U => (starRingEnd ℂ) (F (reflConf hN U)) * F₂ U)
      (gibbs n G beta chi) :=
    integrable_of_bounded _ (hrefl.mul hF₂m) (M := MF * M₂) fun U => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hFb _) (hF₂b U) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hFb (fun _ => 1)))
  unfold osForm
  rw [← integral_add hint₁ hint₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)

/-- The Osterwalder–Schrader form is homogeneous in its second argument. -/
theorem osForm_smul_right (hN : n + 1 = 2 * L) (beta : ℝ) (chi : G → ℝ)
    (F F' : Conf n G → ℂ) (c : ℂ) :
    osForm hN beta chi F (fun U => c * F' U) = c * osForm hN beta chi F F' := by
  unfold osForm
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms wilsonAction_reflConf
#print axioms measurePreserving_reflConf_gibbs
#print axioms osForm_conj_symm
#print axioms osForm_self_re_nonneg

end Audit
