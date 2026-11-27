import Synthesis.NavierStokesCoerciveAdjointExact

/-! The actual rank-one bordered weak system, not a homogeneous adjoint
surrogate. Classical Schur complement; the nonzero coupling must be proved
for the original NS actuator and gauge. -/
namespace Synthesis
noncomputable section
open InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem nsBorderedWeakSolution
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hc : IsCoercive B)
    (f g : V) (gauge : V →L[ℝ] ℝ) (q : ℝ)
    (hnondeg : gauge (hc.continuousLinearEquivOfBilin.symm g) ≠ 0) :
    ∃ u : V, ∃ l : ℝ, gauge u = q ∧
      ∀ v : V, B u v + l * ⟪g,v⟫_ℝ = ⟪f,v⟫_ℝ := by
  let L := hc.continuousLinearEquivOfBilin
  let p := L.symm f
  let z := L.symm g
  let l := (gauge p-q)/gauge z
  have hz : gauge z ≠ 0 := hnondeg
  have hl : l * gauge z = gauge p-q := (div_mul_cancel₀ _ hz)
  have hp (v : V) : B p v = ⟪f,v⟫_ℝ := by
    rw [← hc.continuousLinearEquivOfBilin_apply]
    change ⟪L (L.symm f),v⟫_ℝ = _
    rw [L.apply_symm_apply]
  have hzg (v : V) : B z v = ⟪g,v⟫_ℝ := by
    rw [← hc.continuousLinearEquivOfBilin_apply]
    change ⟪L (L.symm g),v⟫_ℝ = _
    rw [L.apply_symm_apply]
  refine ⟨p-l • z,l,?_,?_⟩
  · simp only [map_sub, map_smul, smul_eq_mul]
    linarith
  · intro v
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hp, hzg]
    ring

/-- With an actual adjoint test, the Schur multiplier vanishes precisely
when the physical residual pairing vanishes. -/
theorem nsBorderedActuatorCancellation
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u a f g : V) (l : ℝ)
    (h : ∀ v : V, B u v + l * ⟪g,v⟫_ℝ = ⟪f,v⟫_ℝ)
    (ha : ⟪g,a⟫_ℝ ≠ 0) :
    l = 0 ↔ B u a = ⟪f,a⟫_ℝ := by
  constructor
  · intro hl
    simpa [hl] using h a
  · intro hr
    apply nsActuatorZeroOfPhysicalPairing
      (B u a - ⟪f,a⟫_ℝ) ⟪g,a⟫_ℝ l ha
    · linarith
    · linarith only [h a]

end
end Synthesis
