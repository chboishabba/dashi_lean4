import Synthesis.YMCMP99Path13DexpInverseSeriesExact

namespace CMP99Pivot.Path13
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R] [NormedAlgebra ℝ R]
  [CompleteSpace R] [HasSummableGeomSeries R]

/-- Consume the series enclosure on a selected inverse differential.
The actual geometric identification D=dexpSeries A remains explicit.
Uniqueness prevents choosing a different inverse for the norm estimate. -/
theorem selected_dexp_inverse_enclosure (A D J : R) (e : ℝ)
    (he : 0≤e) (hA : ‖A‖≤148*e) (hr : 148*e≤1/2)
    (hD : D=dexpSeries A) (hJ : J*D=1) :
    D*J=1 ∧ ‖D-1‖≤148*e ∧ ‖J‖≤2 ∧ ‖J-1‖≤296*e := by
  obtain ⟨K,hDK,hKD,hsmall,hK,hnear⟩ :=
    dexpSeries_logInverse_enclosure A e he hA hr
  subst D
  have heq : J=K := calc
    J = J*1 := (mul_one J).symm
    _ = J*(dexpSeries A*K) := by rw [hDK]
    _ = (J*dexpSeries A)*K := (mul_assoc _ _ _).symm
    _ = K := by rw [hJ,one_mul]
  rw [heq]
  exact ⟨hDK,hsmall,hK,hnear⟩

end
end CMP99Pivot.Path13
