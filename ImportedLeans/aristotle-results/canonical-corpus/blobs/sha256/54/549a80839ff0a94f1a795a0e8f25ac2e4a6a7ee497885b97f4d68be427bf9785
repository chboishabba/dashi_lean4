/-
# Row A1 — the shell bound with the variation *given by the pivot solve*

Two halves of the Row A1 source lane are already owned:

* the algebra — `Q(U)C(U) = 0` differentiates to `Q C' = −Q'C`, and the pivot
  solve gives `C' = E·(−P⁻¹·(Q'·C))` (`EliminatedCoordinateDerivative`);
* the arithmetic — entrywise source estimates on `E`, `P⁻¹`, `Q'` and `C`
  combine into the linear-vanishing constant

      K_D = |c|²·|n|·e·p·K_Q·c_C                (`EliminatedDerivativeBounds`).

This file welds them onto the Row A1a shell bound.  The Lorentz-diagonal
averaging / constrained-projection variation is no longer a matrix family with
assumed properties: it *is* the pivot-solve expression, and the only inputs are

* the four entrywise source estimates,
* the linear vanishing `|Q'(x)_{ij}| ≤ K_Q‖x‖` of the averaging derivative,
* the Lorentz block-diagonality of the resulting variation, and
* the small-field inequality `|c|²·|n|·e·p·K_Q·c_C ≤ 1/2`.

Main result: `A1_beta_pos_from_pivotSolve`.

**Honest status — Row A1 is not closed.**  The four entrywise estimates and the
linear vanishing of `Q'` are the source theorems being invoked; the shell bound
now consumes them directly, with no intermediate free constant.
-/
import RequestProject.YangMills.EliminatedDerivativeBounds
import RequestProject.YangMills.WardFloorFromRegularity

namespace YangMills

open Matrix Finset MeasureTheory

/-- The pivot-solve variation: the derivative of the constrained substitution,
written out from the constraint row. -/
noncomputable def pivotSolveVariation {c : Type*} [Fintype c]
    (E : Matrix (Fin 4) c ℝ) (Pinv : Matrix c c ℝ)
    (Qp : (Fin 4 → ℝ) → Matrix c (Fin 4) ℝ) (Cm : Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  E * (-(Pinv * (Qp x * Cm)))

/-- Entries of the pivot-solve variation are measurable whenever the entries of
the averaging derivative are. -/
theorem measurable_pivotSolveVariation_entry {c : Type*} [Fintype c]
    (E : Matrix (Fin 4) c ℝ) (Pinv : Matrix c c ℝ)
    {Qp : (Fin 4 → ℝ) → Matrix c (Fin 4) ℝ} (Cm : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : ∀ i j, Measurable fun x => Qp x i j) (a b : Fin 4) :
    Measurable fun x => pivotSolveVariation E Pinv Qp Cm x a b := by
  simp only [pivotSolveVariation, Matrix.mul_apply, Matrix.neg_apply]
  refine Finset.measurable_sum _ fun k _ => measurable_const.mul ?_
  refine Measurable.neg ?_
  refine Finset.measurable_sum _ fun l _ => measurable_const.mul ?_
  exact Finset.measurable_sum _ fun r _ => (hQ l r).mul measurable_const

/-- **Row A1a with the variation supplied by the printed constraint row.**

The Gaussian sector of the shell coefficient is the literal one-loop trace whose
first variation is the pivot solve `E(−P⁻¹Q'C)` of the constraint derivative
`QC' = −Q'C`.  Its linear vanishing at zero momentum, and the smallness the Ward
floor needs, are both computed from four entrywise source estimates together
with the linear vanishing of the averaging derivative `Q'`.

For every shell index and every admissible history, `β_j(g) ≥ 1/16777216 > 0`. -/
theorem A1_beta_pos_from_pivotSolve
    {cc' ι κ : Type*} [Fintype cc'] [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f e p KQ cC KW : ℝ}
    {E : Matrix (Fin 4) cc' ℝ} {Pinv : Matrix cc' cc' ℝ}
    {Qp : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix cc' (Fin 4) ℝ}
    {Cm : Matrix (Fin 4) (Fin 4) ℝ}
    {Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (he : 0 ≤ e) (hp : 0 ≤ p) (hKQ : 0 ≤ KQ) (hKW : 0 ≤ KW)
    (hE : ∀ i j, |E i j| ≤ e) (hP : ∀ i j, |Pinv i j| ≤ p)
    (hC : ∀ i j, |Cm i j| ≤ cC)
    (hQlin : ∀ j h x i l, |Qp j h x i l| ≤ KQ * ‖x‖)
    (hQmeas : ∀ j h i l, Measurable fun x => Qp j h x i l)
    (hDoff : ∀ j h x a b, a ≠ b → pivotSolveVariation E Pinv (Qp j h) Cm x a b = 0)
    (hsmallD : eliminatedDerivativeConstant (Fintype.card cc') 4 e p KQ cC ≤ 1 / 2)
    (hWmeas : ∀ j h a b, Measurable fun x => Wm j h x a b)
    (hWbd : ∀ j h, ∀ x ∈ puncturedCell, ∀ a b, |Wm j h x a b| ≤ KW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (pivotSolveVariation E Pinv (Qp j' h) Cm)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N j g := by
  have hcard : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  have hcCnn : 0 ≤ cC := le_trans (abs_nonneg _) (hC 0 0)
  have hKDnn : 0 ≤ eliminatedDerivativeConstant (Fintype.card cc') 4 e p KQ cC :=
    eliminatedDerivativeConstant_nonneg he hp hKQ hcCnn
  have hDlin : ∀ j' h x a b, |pivotSolveVariation E Pinv (Qp j' h) Cm x a b|
      ≤ eliminatedDerivativeConstant (Fintype.card cc') 4 e p KQ cC * ‖x‖ := by
    intro j' h x a b
    have hbound := eliminatedDerivative_linear_bound (E := E) (Pinv := Pinv) (Cm := Cm)
      (Qp := Qp j' h) he hp hKQ hE hP hC (hQlin j' h) x a b
    rwa [hcard] at hbound
  exact A1_beta_pos_ward_from_regularity
    (KD := eliminatedDerivativeConstant (Fintype.card cc') 4 e p KQ cC)
    (Dm := fun j' h => pivotSolveVariation E Pinv (Qp j' h) Cm)
    hKDnn hsmallD hKW
    (fun j' h a b => measurable_pivotSolveVariation_entry E Pinv Cm (hQmeas j' h) a b)
    hWmeas hDoff hDlin hWbd hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

/-! ## Non-vacuity of the pivot-solve hypothesis package -/

/-- A witness averaging derivative: Lorentz-diagonal and vanishing linearly at
zero momentum, with the small-field constant `K_Q = 1/512`. -/
noncomputable def pivotWitnessQ (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun a => (1 / 512 : ℝ) * x a

theorem pivotWitnessQ_bound (x : Fin 4 → ℝ) (i l : Fin 4) :
    |pivotWitnessQ x i l| ≤ (1 / 512 : ℝ) * ‖x‖ := by
  by_cases h : i = l
  · subst h
    rw [pivotWitnessQ, Matrix.diagonal_apply_eq, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/512)]
    have : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  · rw [pivotWitnessQ, Matrix.diagonal_apply_ne _ h, abs_zero]
    positivity

theorem measurable_pivotWitnessQ_entry (i l : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => pivotWitnessQ x i l := by
  by_cases h : i = l
  · subst h
    simp only [pivotWitnessQ, Matrix.diagonal_apply_eq]
    exact measurable_const.mul (measurable_pi_apply i)
  · simp [pivotWitnessQ, Matrix.diagonal_apply_ne _ h]

theorem pivotWitness_variation_eq (x : Fin 4 → ℝ) :
    pivotSolveVariation (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 pivotWitnessQ 1 x
      = -pivotWitnessQ x := by
  simp [pivotSolveVariation]

/-- The witness variation is genuinely nonzero: at `x = (1,0,0,0)` its `(0,0)`
entry is `−1/512`. -/
theorem pivotWitness_variation_value :
    pivotSolveVariation (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 pivotWitnessQ 1
        (fun mu => if mu = 0 then 1 else 0) 0 0 = -(1 / 512 : ℝ) := by
  rw [pivotWitness_variation_eq]
  simp [pivotWitnessQ, Matrix.diagonal_apply_eq]

/-- **The hypothesis package of `A1_beta_pos_from_pivotSolve` is inhabited, with
a nonzero variation.**  This is an inhabitation statement about the inputs, not
an identification of Bałaban's objects. -/
theorem A1_beta_pos_from_pivotSolve_nonvacuous (f : ℝ) (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun _ _ => literalOneLoopIntegrand
        (sourceVariationMatrix f 1
          (pivotSolveVariation (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 pivotWitnessQ 1))
        (fun _ => 0))
      (fun _ _ (_ : Fin 0) => (0 : ℝ)) (fun _ _ (_ : Fin 0) => (0 : ℝ))
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) 0 j
      (fun _ => (0 : ℝ)) := by
  have hone : ∀ i l : Fin 4, |(1 : Matrix (Fin 4) (Fin 4) ℝ) i l| ≤ 1 := by
    intro i l
    by_cases h : i = l
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  refine A1_beta_pos_from_pivotSolve (Adm := fun h => ∀ j, h j = 0)
    (E := 1) (Pinv := 1) (Cm := 1) (Qp := fun _ _ => pivotWitnessQ)
    (Wm := fun _ _ _ => 0) (e := 1) (p := 1) (KQ := 1 / 512) (cC := 1) (KW := 0)
    (AInt := fun _ => 0) (AChart := fun _ => 0) (ALoc := fun _ => 0)
    (LamDet := 0) (LamGauge := 0) (theta := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    hone hone hone
    (fun _ _ x i l => pivotWitnessQ_bound x i l)
    (fun _ _ i l => measurable_pivotWitnessQ_entry i l)
    ?_ ?_
    (fun _ _ _ _ => measurable_const)
    (fun _ _ _ _ _ _ => by norm_num)
    (fun _ _ i => absurd i.isLt (by omega)) (fun _ _ i => absurd i.isLt (by omega))
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
    ?_ (by norm_num) (by norm_num) (fun _ => rfl) (fun _ => le_rfl) ?_ j
  · intro _ _ x a b hab
    rw [pivotWitness_variation_eq, Matrix.neg_apply, pivotWitnessQ,
      Matrix.diagonal_apply_ne _ hab, neg_zero]
  · rw [eliminatedDerivativeConstant]
    norm_num
  · intro j' h hh
    refine ⟨le_of_eq (hh j').symm, ?_, ?_, ?_⟩ <;> rw [hh j'] <;> norm_num
  · intro _
    have hC : 0 ≤ Cbeta (sourceChannelCoefficient (Fintype.card (Fin 0)) (Fintype.card (Fin 0))
        0 0 (1 / 2) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0) := by
      rw [Cbeta]
      exact Finset.sum_nonneg fun k _ =>
        sourceChannelCoefficient_nonneg (by norm_num) (by norm_num) k
    exact (criticalCoupling_pos (by norm_num) hC).le

end YangMills
