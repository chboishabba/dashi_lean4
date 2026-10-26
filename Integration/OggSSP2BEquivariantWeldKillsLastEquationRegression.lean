import Integration.OggSSP2BEquivariantWeldKillsLastEquation

/-! Regression surface: the terminal action equality must be a consequence of
intertwining, not an independent source receipt. -/

namespace Integration.OggSSP2BEquivariantWeldKillsLastEquationRegression

open Integration.OggSSP2BEquivariantWeldKillsLastEquation

variable {K X Y : Type*}
  [DivisionRing K]
  [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

example (e : X ≃ₗ[K] Y) (gx : X →ₗ[K] X) (gy : Y →ₗ[K] Y)
    (h : ∀ x, e (gx x) = gy (e x)) :
    gx = e.symm.toLinearMap.comp (gy.comp e.toLinearMap) :=
  operator_eq_conjugate_of_intertwining e gx gy h

end Integration.OggSSP2BEquivariantWeldKillsLastEquationRegression
