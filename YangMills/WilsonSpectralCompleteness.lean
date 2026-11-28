import Mathlib

/-!
# Dense Wilson vectors imply spectral detection

Once the reconstructed OS Hilbert sector is generated densely by Wilson/cylinder
vectors, no nonzero spectral vector can be invisible to all of them.  Thus the
abstract detector part of spectral completeness is automatic from density; the
physical F2 obligation is to prove that the selected Wilson/cylinder vectors are
dense in the required reconstructed sector.
-/

namespace RequestProject.YangMills

/-- Any dense set in a real Hilbert space detects every nonzero vector by inner product. -/
theorem dense_wilson_vectors_detect_nonzero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (wilsonVectors : Set H)
    (hDense : Dense wilsonVectors)
    (v : H) (hv : v ≠ 0) :
    ∃ w ∈ wilsonVectors, ⟪w, v⟫_ℝ ≠ 0 := by
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨w, hw, hdist⟩ :=
    hDense.exists_dist_lt v (half_pos hvnorm)
  refine ⟨w, hw, ?_⟩
  intro horth
  have hdiff : ⟪v - w, v⟫_ℝ = ⟪v, v⟫_ℝ := by
    rw [inner_sub_left, horth, sub_zero]
  have hcs := abs_real_inner_le_norm (v - w) v
  rw [hdiff, real_inner_self_eq_norm_sq,
    abs_of_nonneg (sq_nonneg ‖v‖)] at hcs
  have hnormdiff : ‖v - w‖ < ‖v‖ / 2 := by
    simpa [dist_eq_norm] using hdist
  have hvnonneg : 0 ≤ ‖v‖ := norm_nonneg v
  nlinarith

/--
Energy-sector form: any nonzero vector selected from a putative subgap spectral
sector is detected by some dense Wilson vector.
-/
theorem dense_wilson_vectors_detect_spectral_sector
    {H Energy : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (wilsonVectors : Set H)
    (hDense : Dense wilsonVectors)
    (spectralVector : Energy → H)
    (energy : Energy)
    (hNonzero : spectralVector energy ≠ 0) :
    ∃ w ∈ wilsonVectors,
      ⟪w, spectralVector energy⟫_ℝ ≠ 0 :=
  dense_wilson_vectors_detect_nonzero
    wilsonVectors hDense (spectralVector energy) hNonzero

/-- Exact remaining F2 physical producer: density of the selected Wilson/cylinder vectors. -/
def WilsonVectorDensityProducerExists
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (wilsonVectors : Set H) : Prop :=
  Dense wilsonVectors

end RequestProject.YangMills
