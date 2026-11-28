import Synthesis.NavierStokesPressureCellFiniteSumExact

namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

/-- Actual pressure decomposition on a summable triad family.
Summability of raw convection and pressure are separate analytic
obligations, not inferred from the projected series. -/
theorem pressure_series_split {I : Type*} (k : Vec3)
    (u v : I → CVec3) (i : Fin 3)
    (hr : Summable (fun j => -rawConvection k (u j) (v j) i))
    (hp : Summable (fun j => pressureCell k (u j) (v j))) :
    (∑' j, -projectedConvection k (u j) (v j) i) =
      (∑' j, -rawConvection k (u j) (v j) i) -
      Complex.I*(k i:ℂ)*(∑' j, pressureCell k (u j) (v j)) := by
  simp_rw [projected_pressure_split]
  rw [tsum_sub hr (hp.mul_left _), tsum_mul_left]

end
end DASHI.NavierStokes.EuclideanMidpoint
