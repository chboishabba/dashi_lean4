import Mathlib

/-!
# Three-dimensional spatial slice of a flat Lorentzian model

This is a genuine elementary theorem on a *chosen* flat product
R × EuclideanSpace R (Fin 3). The sign convention below is
spacelike-positive (|x|² - t²), opposite to the integer hyperbolic
carrier's (t² - |x|²); this distinction is explicit.

Prior work: DASHI Geometry.Signature.HyperbolicFormZ and
Physics.Closure.MinkowskiLimitReceipt (integer flat carrier).
The physical identification with a derived observer metric, the
completion Z^3 → R^3, and the application to Kakeya tube measure are
NOT asserted or constructed here.
-/

namespace DashiKakeya

abbrev Spatial3 := EuclideanSpace ℝ (Fin 3)
abbrev Flat31 := ℝ × Spatial3

/-- Spacelike-positive Lorentzian quadratic expression. -/
def flatQuadratic (p : Flat31) : ℝ := ‖p.2‖ ^ 2 - p.1 ^ 2

/-- Inject a Euclidean spatial point into the selected time-zero slice. -/
def zeroTime (x : Spatial3) : Flat31 := (0, x)

/-- The spatial restriction is exactly the Euclidean squared norm. -/
theorem flatQuadratic_zeroTime (x : Spatial3) :
    flatQuadratic (zeroTime x) = ‖x‖ ^ 2 := by
  simp [flatQuadratic, zeroTime]

/-- The spatial slice has an exactly preserved coordinate, not merely a label. -/
theorem zeroTime_spatial (x : Spatial3) : (zeroTime x).2 = x := rfl

theorem zeroTime_time (x : Spatial3) : (zeroTime x).1 = 0 := rfl

/-- Euclidean distance squared can be read as the spatial interval square. -/
theorem flatSpatialInterval (x y : Spatial3) :
    ‖x - y‖ ^ 2 = flatQuadratic (zeroTime (x - y)) := by
  rw [flatQuadratic_zeroTime]

/-- The same flat restriction applies on any *constant* time slice. -/
def fixedTime (t : ℝ) (x : Spatial3) : Flat31 := (t, x)

theorem flatQuadratic_fixedTime (t : ℝ) (x : Spatial3) :
    flatQuadratic (fixedTime t x) = ‖x‖ ^ 2 - t ^ 2 := rfl

-- No physical claim: being a spatial metric on a selected flat product
-- is not a theorem that a microscopic/observer cone yields that metric.
-- No full Kakeya theorem is reasserted: use pinned external Lean proof.

end DashiKakeya
