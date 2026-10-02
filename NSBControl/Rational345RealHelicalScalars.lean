import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# R830 real helical scalar backend

The instantaneous 3-4-5 witness is rational because every active mode has
Pythagorean length 3, 4, or 5.  The evolving radius-four Galerkin state is not
supported only on those modes, so R830 must use the genuine real physical
helical scalar

  |k| = sqrt (kx^2 + ky^2 + kz^2)

and its reciprocal on every nonzero retained integer mode.

This file installs that backend and proves that it specializes exactly to the
rational 3-4-5 calibration used by R829/R850.
-/

namespace NSBControl
namespace Rational345RealHelicalScalars

structure Mode3 where
  x : ℤ
  y : ℤ
  z : ℤ
deriving DecidableEq, Repr

def normSq (k : Mode3) : ℝ :=
  (k.x : ℝ)^2 + (k.y : ℝ)^2 + (k.z : ℝ)^2

def modeNorm (k : Mode3) : ℝ :=
  Real.sqrt (normSq k)

def inverseModeNorm (k : Mode3) : ℝ :=
  1 / modeNorm k

def half : ℝ := 1 / 2

def k₁ : Mode3 := ⟨-3, -4, 0⟩
def k₂ : Mode3 := ⟨-3,  0, 0⟩
def k₃ : Mode3 := ⟨-3,  4, 0⟩
def k₄ : Mode3 := ⟨ 0, -4, 0⟩
def k₅ : Mode3 := ⟨ 0,  4, 0⟩
def k₆ : Mode3 := ⟨ 3, -4, 0⟩
def k₇ : Mode3 := ⟨ 3,  0, 0⟩
def k₈ : Mode3 := ⟨ 3,  4, 0⟩

theorem normSq_nonneg (k : Mode3) : 0 ≤ normSq k := by
  dsimp [normSq]
  positivity

theorem modeNorm_nonneg (k : Mode3) : 0 ≤ modeNorm k := by
  exact Real.sqrt_nonneg _

theorem modeNorm_sq (k : Mode3) :
    modeNorm k ^ 2 = normSq k := by
  rw [modeNorm, sq_sqrt (normSq_nonneg k)]

theorem half_exact : half = (1 : ℝ) / 2 := rfl

theorem norm_k₁ : modeNorm k₁ = 5 := by
  norm_num [modeNorm, normSq, k₁]

theorem norm_k₂ : modeNorm k₂ = 3 := by
  norm_num [modeNorm, normSq, k₂]

theorem norm_k₃ : modeNorm k₃ = 5 := by
  norm_num [modeNorm, normSq, k₃]

theorem norm_k₄ : modeNorm k₄ = 4 := by
  norm_num [modeNorm, normSq, k₄]

theorem norm_k₅ : modeNorm k₅ = 4 := by
  norm_num [modeNorm, normSq, k₅]

theorem norm_k₆ : modeNorm k₆ = 5 := by
  norm_num [modeNorm, normSq, k₆]

theorem norm_k₇ : modeNorm k₇ = 3 := by
  norm_num [modeNorm, normSq, k₇]

theorem norm_k₈ : modeNorm k₈ = 5 := by
  norm_num [modeNorm, normSq, k₈]

theorem invNorm_k₁ : inverseModeNorm k₁ = (1 : ℝ) / 5 := by
  simp [inverseModeNorm, norm_k₁]

theorem invNorm_k₂ : inverseModeNorm k₂ = (1 : ℝ) / 3 := by
  simp [inverseModeNorm, norm_k₂]

theorem invNorm_k₃ : inverseModeNorm k₃ = (1 : ℝ) / 5 := by
  simp [inverseModeNorm, norm_k₃]

theorem invNorm_k₄ : inverseModeNorm k₄ = (1 : ℝ) / 4 := by
  simp [inverseModeNorm, norm_k₄]

theorem invNorm_k₅ : inverseModeNorm k₅ = (1 : ℝ) / 4 := by
  simp [inverseModeNorm, norm_k₅]

theorem invNorm_k₆ : inverseModeNorm k₆ = (1 : ℝ) / 5 := by
  simp [inverseModeNorm, norm_k₆]

theorem invNorm_k₇ : inverseModeNorm k₇ = (1 : ℝ) / 3 := by
  simp [inverseModeNorm, norm_k₇]

theorem invNorm_k₈ : inverseModeNorm k₈ = (1 : ℝ) / 5 := by
  simp [inverseModeNorm, norm_k₈]

/-- Exact calibration table needed to identify the real R830 observable with
the rational R850 snapshot at t=0. -/
theorem active345_real_calibration :
    modeNorm k₁ = 5 ∧ inverseModeNorm k₁ = (1 : ℝ) / 5 ∧
    modeNorm k₂ = 3 ∧ inverseModeNorm k₂ = (1 : ℝ) / 3 ∧
    modeNorm k₃ = 5 ∧ inverseModeNorm k₃ = (1 : ℝ) / 5 ∧
    modeNorm k₄ = 4 ∧ inverseModeNorm k₄ = (1 : ℝ) / 4 ∧
    modeNorm k₅ = 4 ∧ inverseModeNorm k₅ = (1 : ℝ) / 4 ∧
    modeNorm k₆ = 5 ∧ inverseModeNorm k₆ = (1 : ℝ) / 5 ∧
    modeNorm k₇ = 3 ∧ inverseModeNorm k₇ = (1 : ℝ) / 3 ∧
    modeNorm k₈ = 5 ∧ inverseModeNorm k₈ = (1 : ℝ) / 5 := by
  exact ⟨norm_k₁, invNorm_k₁,
    norm_k₂, invNorm_k₂,
    norm_k₃, invNorm_k₃,
    norm_k₄, invNorm_k₄,
    norm_k₅, invNorm_k₅,
    norm_k₆, invNorm_k₆,
    norm_k₇, invNorm_k₇,
    norm_k₈, invNorm_k₈⟩

end Rational345RealHelicalScalars
end NSBControl
