import Synthesis.NavierStokesBorderedActuatorExact

/-! Same-carrier inverse and quadratic root composition. The original
weighted physical form and exact nonlinear expansion remain necessary. -/
namespace Synthesis
noncomputable section
open InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem nsHalfContractionRadius (e b : ℝ)
    (he : 0 ≤ e) (hb : 0 ≤ b) (h : 8*b*e ≤ 1) :
    e+b*(2*e)*(2*e) ≤ 2*e ∧ 2*b*(2*e) ≤ (1/2 : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_right h he
  constructor <;> nlinarith only [hmul,h,he,hb]

theorem nsCoerciveNonlinearRoot
    (form : V →L[ℝ] V →L[ℝ] ℝ) (hc : IsCoercive form)
    (u : V) (F : V → V) (B : V →L[ℝ] V →L[ℝ] V)
    (hexpand : ∀ h : V,
      F (u+h) = F u + hc.continuousLinearEquivOfBilin h +
        hc.continuousLinearEquivOfBilin (B h h))
    (hsmall : 8*‖B‖*‖hc.continuousLinearEquivOfBilin.symm (F u)‖ ≤ 1)
    (hnz : 2*‖hc.continuousLinearEquivOfBilin.symm (F u)‖ < ‖u‖) :
    ∃ v : V, v ≠ 0 ∧ F v = 0 ∧
      ‖v-u‖ ≤ 2*‖hc.continuousLinearEquivOfBilin.symm (F u)‖ := by
  let L := hc.continuousLinearEquivOfBilin
  let A := L.symm.toContinuousLinearMap
  let e := ‖A (F u)‖
  have hs : 8*‖B‖*e ≤ 1 := hsmall
  obtain ⟨hs1,hs2⟩ := nsHalfContractionRadius e ‖B‖
    (norm_nonneg _) (norm_nonneg _) hs
  have hA : Function.Injective A := L.symm.injective
  have hE : ∀ h : V, A (F (u+h)) = A (F u) + h + B h h := by
    intro h
    rw [hexpand]
    simp only [map_add]
    change A (F u) + L.symm (L h) + L.symm (L (B h h)) = _
    rw [L.symm_apply_apply, L.symm_apply_apply]
  exact nsQuadraticCorrectionRoot u F A B (2*e) (1/2 : ℝ≥0)
    (by positivity) (by norm_num) hnz hA hE hs1 (by exact_mod_cast hs2)

end
end Synthesis
