import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import NSBControl.Rational345RealRadius4

/-!
# R830 real radius-four 3-4-5 initial state

The R850 snapshot is installed on the same real radius-four carrier used by the
evolving Galerkin field and selected-rate observable.  This removes any
ambiguity about the initial condition when passing from the rational static
certificate to the real local ODE.

Only six velocity modes are nonzero: three positive reality representatives
and their complex conjugates.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345RealInitialState

open Rational345RealRadius4

def k300 : Mode := ⟨7, 4, 4⟩
def km300 : Mode := ⟨1, 4, 4⟩
def k040 : Mode := ⟨4, 8, 4⟩
def k0m40 : Mode := ⟨4, 0, 4⟩
def k340 : Mode := ⟨7, 8, 4⟩
def km3m40 : Mode := ⟨1, 0, 4⟩

def v300 : Vec3 :=
  ![(0 : ℂ), 2 + 2 * Complex.I, -2 - Complex.I]

def v040 : Vec3 :=
  ![2 + 2 * Complex.I, (0 : ℂ), 2 + 2 * Complex.I]

def v340 : Vec3 :=
  ![6 * Complex.I, -(9 : ℂ) / 2 * Complex.I, -2 + 2 * Complex.I]

def vecConj (v : Vec3) : Vec3 := fun j => star (v j)

def u₀ : State :=
  fun k =>
    if k = k300 then v300
    else if k = km300 then vecConj v300
    else if k = k040 then v040
    else if k = k0m40 then vecConj v040
    else if k = k340 then v340
    else if k = km3m40 then vecConj v340
    else 0

theorem u₀_k300 : u₀ k300 = v300 := by
  simp [u₀]

theorem u₀_km300 : u₀ km300 = vecConj v300 := by
  simp [u₀, k300, km300]

theorem u₀_k040 : u₀ k040 = v040 := by
  simp [u₀, k300, km300, k040]

theorem u₀_k0m40 : u₀ k0m40 = vecConj v040 := by
  simp [u₀, k300, km300, k040, k0m40]

theorem u₀_k340 : u₀ k340 = v340 := by
  simp [u₀, k300, km300, k040, k0m40, k340]

theorem u₀_km3m40 : u₀ km3m40 = vecConj v340 := by
  simp [u₀, k300, km300, k040, k0m40, k340, km3m40]

------------------------------------------------------------------------
-- Exact physical radii on the seed support.
------------------------------------------------------------------------

theorem norm_k300 : modeNorm k300 = 3 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, k300]

theorem norm_km300 : modeNorm km300 = 3 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, km300]

theorem norm_k040 : modeNorm k040 = 4 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, k040]

theorem norm_k0m40 : modeNorm k0m40 = 4 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, k0m40]

theorem norm_k340 : modeNorm k340 = 5 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, k340]

theorem norm_km3m40 : modeNorm km3m40 = 5 := by
  norm_num [modeNorm, normSq, kReal, kInt, axisInt, km3m40]

theorem invNorm_k300 : inverseModeNorm k300 = (1 : ℝ) / 3 := by
  simp [inverseModeNorm, norm_k300]

theorem invNorm_k040 : inverseModeNorm k040 = (1 : ℝ) / 4 := by
  simp [inverseModeNorm, norm_k040]

theorem invNorm_k340 : inverseModeNorm k340 = (1 : ℝ) / 5 := by
  simp [inverseModeNorm, norm_k340]

------------------------------------------------------------------------
-- The three independent stored seed values are transverse.  Reality is
-- supplied structurally by the conjugate negative entries in u₀.
------------------------------------------------------------------------

theorem transverse_v300 :
    bilinearDot (kComplex k300) v300 = 0 := by
  norm_num [bilinearDot, kComplex, kReal, kInt, axisInt, k300, v300]

theorem transverse_v040 :
    bilinearDot (kComplex k040) v040 = 0 := by
  norm_num [bilinearDot, kComplex, kReal, kInt, axisInt, k040, v040]

theorem transverse_v340 :
    bilinearDot (kComplex k340) v340 = 0 := by
  norm_num [bilinearDot, kComplex, kReal, kInt, axisInt, k340, v340]
  ring

/-- Public initial-value calibration target.  The remaining theorem is to
identify selectedRate u₀ with the already-kernel-certified R850 value. -/
def expectedInitialRate : ℝ := -(28273644 : ℝ) / 125

theorem expectedInitialRate_neg : expectedInitialRate < 0 := by
  norm_num [expectedInitialRate]

end Rational345RealInitialState
end NSBControl
