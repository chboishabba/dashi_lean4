import Synthesis.NavierStokesActualPressureAndHalfWeightExact

namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

/-- Sum the actual pressure split on any finite triad family, preserving
the output frequency and original pressure coefficient. -/
theorem pressure_finite_sum_split {I : Type*} (S : Finset I)
    (k : Vec3) (u v : I → CVec3) (i : Fin 3) :
    (∑ j ∈ S, -projectedConvection k (u j) (v j) i) =
      (∑ j ∈ S, -rawConvection k (u j) (v j) i) -
        Complex.I*(k i:ℂ)*(∑ j ∈ S, pressureCell k (u j) (v j)) := by
  simp_rw [projected_pressure_split, Finset.sum_sub_distrib, Finset.mul_sum]

end
end DASHI.NavierStokes.EuclideanMidpoint
