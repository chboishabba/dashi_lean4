import Synthesis.NavierStokesActualPressureAndHalfWeightExact

/-!
Same-source pressure-cell bilinear difference on the original physical
three-component complex Fourier carrier. This is the exact algebraic
term required for a pressure convergence estimate; no limit is claimed.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

/-- The original longitudinal pressure cell is bilinear in its two
velocity inputs, even in the zero-output sector. -/
theorem pressureCell_sub_left (k : Vec3) (u u' v : CVec3) :
    pressureCell k (u-u') v =
      pressureCell k u v-pressureCell k u' v := by
  unfold pressureCell outputDot
  simp only [Pi.sub_apply, Fin.sum_univ_three]
  ring

theorem pressureCell_sub_right (k : Vec3) (u v v' : CVec3) :
    pressureCell k u (v-v') =
      pressureCell k u v-pressureCell k u v' := by
  unfold pressureCell outputDot
  simp only [Pi.sub_apply, Fin.sum_univ_three]
  ring

/-- Telescope the original pressure cell between two pairs of
velocities. This retains the same original output k and both inputs. -/
theorem pressureCell_bilinear_difference (k : Vec3)
    (u v u' v' : CVec3) :
    pressureCell k u v-pressureCell k u' v' =
      pressureCell k (u-u') v+pressureCell k u' (v-v') := by
  rw [pressureCell_sub_left, pressureCell_sub_right]
  abel

end
end DASHI.NavierStokes.EuclideanMidpoint
