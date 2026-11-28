import Synthesis.NavierStokesQuadraticInverseExact
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! Classical Lax–Milgram on the actual supplied Hilbert carrier.
The transposed form is not assumed symmetric. No assertion that the original
NS similarity operator is coercive on an unspecified space. -/
namespace Synthesis
noncomputable section
open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem nsSignedCoercivity
    (B E : V →L[ℝ] V →L[ℝ] ℝ) (c d : ℝ)
    (hgap : d < c)
    (hB : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v)
    (hE : ∀ v, -(d * ‖v‖ * ‖v‖) ≤ E v v) :
    IsCoercive (B + E) := by
  refine ⟨c-d, sub_pos.mpr hgap, ?_⟩
  intro v
  change (c-d)*‖v‖*‖v‖ ≤ B v v + E v v
  linarith only [hB v, hE v]

theorem nsWeakPrimalExists
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hc : IsCoercive B) (f : V) :
    ∃! u : V, ∀ v : V, B u v = ⟪f, v⟫_ℝ := by
  let L := hc.continuousLinearEquivOfBilin
  refine ⟨L.symm f, ?_, ?_⟩
  · intro v
    rw [← hc.continuousLinearEquivOfBilin_apply]
    change ⟪L (L.symm f), v⟫_ℝ = _
    rw [L.apply_symm_apply]
  · intro u hu
    apply L.injective
    have he : f = L u :=
      hc.unique_continuousLinearEquivOfBilin (fun v => (hu v).symm)
    rw [L.apply_symm_apply]
    exact he.symm

/-- Construct the transpose on the SAME Hilbert space. Coercivity is
unchanged on the diagonal; there is no symmetry assumption. -/
theorem nsWeakAdjointExists
    (B Bt : V →L[ℝ] V →L[ℝ] ℝ)
    (htranspose : ∀ u v, Bt u v = B v u)
    (hc : IsCoercive B) (f : V) :
    ∃! a : V, ∀ v : V, B v a = ⟪f, v⟫_ℝ := by
  have hct : IsCoercive Bt := by
    obtain ⟨c, hp, hb⟩ := hc
    exact ⟨c, hp, fun v => by rw [htranspose]; exact hb v⟩
  obtain ⟨a, ha, hu⟩ := nsWeakPrimalExists Bt hct f
  refine ⟨a, ?_, ?_⟩
  · intro v
    rw [← htranspose]
    exact ha v
  · intro b hb
    apply hu b
    intro v
    rw [htranspose]
    exact hb v

/-- Homogeneous coercive adjoint has no nonzero kernel. Thus a nonzero
normalized adjoint must come from the actual bordered / inhomogeneous
problem or from a failure of coercivity, not from an invented null vector. -/
theorem nsHomogeneousAdjointZero
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hc : IsCoercive B) (a : V)
    (ha : ∀ v, B v a = 0) : a = 0 := by
  obtain ⟨c, hp, hb⟩ := hc
  have h := hb a
  rw [ha a] at h
  by_contra hn
  have hnpos : 0 < ‖a‖ := norm_pos_iff.mpr hn
  exact (not_le_of_gt (mul_pos (mul_pos hp hnpos) hnpos)) h

/-- Exact actuator projection by a single test field, with no normalization
assumed beyond a nonzero pairing. Reverse direction uses the same pairing. -/
theorem nsActuatorMultiplierBidi
    (residual actuator multiplier : ℝ) (ha : actuator ≠ 0) :
    residual + multiplier * actuator = 0 ↔
      multiplier = -residual / actuator := by
  constructor
  · intro h
    apply (eq_div_iff ha).2
    linarith
  · intro h
    have he := (eq_div_iff ha).1 h
    linarith

theorem nsActuatorZeroOfPhysicalPairing
    (residual actuator multiplier : ℝ)
    (ha : actuator ≠ 0) (hr : residual = 0)
    (h : residual + multiplier * actuator = 0) :
    multiplier = 0 := by
  rw [(nsActuatorMultiplierBidi residual actuator multiplier ha).1 h, hr]
  simp

end
end Synthesis
