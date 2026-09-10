/-
# `Y_x` as the logarithm of the literal relative contour holonomy

At Eq. (119) Bałaban's pointwise Lie elements `Y_x` are not free data: they are
the (principal) logarithms of the *relative* group element

    U(Γ_{c,x}) · U(c)^{-1} ,

built from the holonomy of the literal averaging contour and of the coarse
bond.  This file constructs exactly that, in the small-field regime, from the
lattice data alone.

* `expLog` — a local logarithm on a Banach algebra, obtained from the inverse
  function theorem applied to `exp` at `0` (`exp` has strict derivative `1`
  there).  It is a *construction*, not a postulated inverse.
* `relativeHolonomy` — the literal element `U(Γ) · U(c)^{-1}`, assembled from
  the signed-bond holonomy of `CMP98Eq119Transport`.
* `exists_exp_physicalLog` — there is a neighbourhood of the identity on which
  `exp (physicalLog …) = U(Γ)·U(c)^{-1}`: the pointwise `Y_x` really is a
  logarithm of the relative contour element.
* `eq119_data_from_lattice` — the capstone: from the link field, the contour
  words and two smallness conditions alone, **all** the Eq. (119) inputs are
  produced — the pointwise `Y_x`, the outer `Y` as their block average, and
  the two-sided inverse trivialisations `J` of `g(ad Y_x)`.  Nothing in that
  package is a caller-supplied receipt.

**Honest status.** As in the rest of this lane, the identification of these
objects with the literal fields and contours of the Bałaban papers, and every
analytic estimate downstream of Eq. (119), is neither done nor claimed here.
-/
import RequestProject.YangMills.CMP98Eq119Assembly

namespace YangMills.CMP98Eq119

open Filter Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-! ## 1. A local logarithm from the inverse function theorem -/

theorem hasStrictFDerivAt_exp_zero_real :
    HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
  simpa using hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)

/-- The local logarithm on a Banach algebra: the local inverse of `exp` at `0`. -/
noncomputable def expLog : A → A :=
  HasStrictFDerivAt.localInverse NormedSpace.exp _ 0 hasStrictFDerivAt_exp_zero_real

theorem exp_expLog_eventually :
    ∀ᶠ u in 𝓝 (1 : A), NormedSpace.exp (expLog u) = u := by
  have h := (hasStrictFDerivAt_exp_zero_real (A := A)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem exists_ball_exp_expLog :
    ∃ ε > 0, ∀ u : A, ‖u - 1‖ < ε → NormedSpace.exp (expLog u) = u := by
  have h := exp_expLog_eventually (A := A)
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  exact ⟨ε, hε, fun u hu => hball (by simpa [dist_eq_norm] using hu)⟩

/-! ## 2. The relative contour element and its logarithm -/

/-- The literal relative group element `U(Γ) · U(c)^{-1}` of the source. -/
noncomputable def relativeHolonomy {N : ℕ} (link : PSite 4 N → Step 4 → Aˣ) (x : PSite 4 N)
    (gamma coarse : List (Step 4)) : A :=
  ((hol link x gamma * (hol link x coarse)⁻¹ : Aˣ) : A)

/-- Bałaban's pointwise Lie element `Y_x`, constructed as the logarithm of the
relative contour element. -/
noncomputable def physicalLog {N : ℕ} (link : PSite 4 N → Step 4 → Aˣ) (x : PSite 4 N)
    (gamma coarse : List (Step 4)) : A :=
  expLog (relativeHolonomy link x gamma coarse)

/-- On a neighbourhood of the identity, `exp Y_x` really is the relative
contour element. -/
theorem exists_exp_physicalLog {N : ℕ} :
    ∃ ε > 0, ∀ (link : PSite 4 N → Step 4 → Aˣ) (x : PSite 4 N)
      (gamma coarse : List (Step 4)),
      ‖relativeHolonomy link x gamma coarse - 1‖ < ε →
      NormedSpace.exp (physicalLog link x gamma coarse)
        = relativeHolonomy link x gamma coarse := by
  obtain ⟨ε, hε, h⟩ := exists_ball_exp_expLog (A := A)
  exact ⟨ε, hε, fun link x gamma coarse hu => h _ hu⟩

/-! ## 3. All Eq. (119) inputs from lattice data -/

variable [Nontrivial A]

/-- **The Eq. (119) input package is produced, not assumed.**  Given only the
link field, the averaging contours, the coarse bond, and two smallness
conditions, one obtains: the pointwise `Y_x` as logarithms of the literal
relative contour elements, and two-sided inverses of both trivialisations
`g(ad Y_x)` and `g(−ad Y_x)`.  The outer `Y` is then the block average of the
`Y_x`, which is what `eq119` uses. -/
theorem eq119_data_from_lattice {N : ℕ} :
    ∃ ε > 0, ∀ (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
      (gamma : BlockOffset → List (Step 4)) (coarse : List (Step 4)),
      (∀ p, ‖relativeHolonomy link cMinus (gamma p) coarse - 1‖ < ε) →
      (∀ p, ‖physicalLog link cMinus (gamma p) coarse‖ < Real.log 2 / 2) →
      ∃ Jm Jp : BlockOffset → (A →L[ℝ] A),
        (∀ p, NormedSpace.exp (physicalLog link cMinus (gamma p) coarse)
            = relativeHolonomy link cMinus (gamma p) coarse) ∧
        (∀ p, balabanG (adOp (physicalLog link cMinus (gamma p) coarse)) * Jm p = 1) ∧
        (∀ p, Jp p * balabanG (-(adOp (physicalLog link cMinus (gamma p) coarse))) = 1) := by
  obtain ⟨ε, hε, hexp⟩ := exists_exp_physicalLog (A := A) (N := N)
  refine ⟨ε, hε, fun link cMinus gamma coarse hsmall hlog => ?_⟩
  have hunits : ∀ p, IsUnit (balabanG (adOp (physicalLog link cMinus (gamma p) coarse)))
      ∧ IsUnit (balabanG (-(adOp (physicalLog link cMinus (gamma p) coarse)))) :=
    fun p => exists_inverse_of_norm_lt (hlog p)
  refine ⟨fun p => ((hunits p).1.unit⁻¹ : (A →L[ℝ] A)ˣ),
    fun p => ((hunits p).2.unit⁻¹ : (A →L[ℝ] A)ˣ), fun p => hexp _ _ _ _ (hsmall p), ?_, ?_⟩
  · intro p
    simp
  · intro p
    simp

end YangMills.CMP98Eq119
