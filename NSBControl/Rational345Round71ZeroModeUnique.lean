import NSBControl.Rational345Round71ZeroMode

namespace NSBControl
namespace Rational345Round71ZeroMode

open Rational345RealRadius4

/-- The centered radius-four cube has exactly one zero wave number. -/
theorem eq_zeroMode_of_isZero (k : Mode) (hk : isZeroMode k) :
    k = zeroMode := by
  rcases k with ⟨x, y, z⟩
  have hx := hk (0 : Fin 3)
  have hy := hk (1 : Fin 3)
  have hz := hk (2 : Fin 3)
  simp [kInt, axisInt] at hx hy hz
  apply Mode.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- Physical zero-mean states vanish at every mode recognized as zero. -/
theorem value_zero_of_isZero
    (u : State) (hu : u zeroMode = 0)
    (k : Mode) (hk : isZeroMode k) :
    u k = 0 := by
  rw [eq_zeroMode_of_isZero k hk, hu]

end Rational345Round71ZeroMode
end NSBControl
