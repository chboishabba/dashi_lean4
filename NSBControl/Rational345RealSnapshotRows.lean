import Mathlib.Tactic
import NSBControl.Rational345RealSnapshotSparse

/-!
# W2 exact real snapshot rows

Exact real/complex vectors used by the Agda R844-R850 snapshot proof, now
re-evaluated through the genuine real radius-four convolution.  The first
stage is the eight projected-nonlinearity rows; later stages consume these
same rows in the real helical R224/R230 expressions.
-/

namespace NSBControl
namespace Rational345RealSnapshotRows

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse

classical

private def c (re im : ℝ) : ℂ := re + im * Complex.I
private def v (xr xi yr yi zr zi : ℝ) : Vec3 :=
  ![c xr xi, c yr yi, c zr zi]

-- Active outputs in the R850 order.
def k₁ : Mode := km3m40
def k₂ : Mode := km300
def k₃ : Mode := km340
def k₄ : Mode := k0m40
def k₅ : Mode := k040
def k₆ : Mode := k3m40
def k₇ : Mode := k300
def k₈ : Mode := k340

-- Exact forcing vectors from the R844/R836 certificate.
def f₁ : Vec3 := v (224/25) 0 (-168/25) 0 14 (-6)
def f₂ : Vec3 := v 0 0 (-27) (-27) 60 36
def f₃ : Vec3 := v 0 (-224/25) 0 (-168/25) 6 (-50)
def f₄ : Vec3 := v 48 48 0 0 68 18
def f₅ : Vec3 := v 48 (-48) 0 0 68 (-18)
def f₆ : Vec3 := v 0 (224/25) 0 (168/25) 6 50
def f₇ : Vec3 := v 0 0 (-27) 27 60 (-36)
def f₈ : Vec3 := v (224/25) 0 (-168/25) 0 14 6

private macro "snapshot_simp" : tactic =>
  `(tactic|
    (simp [sparseForcing, seedModes, projectedOrderedBilinear,
      bilinearDot, kComplex, leray, Resonates, kReal, kInt, axisInt,
      u₀, v300, v040, v340, vecConj,
      k300, km300, k040, k0m40, k340, km3m40,
      km340, k3m40, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
      c, v] <;> norm_num <;> ring))

/-- The genuine real R30 convolution reproduces all eight R844 forcing rows. -/
theorem sparseForcing_k₁ : sparseForcing k₁ = f₁ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₂ : sparseForcing k₂ = f₂ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₃ : sparseForcing k₃ = f₃ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₄ : sparseForcing k₄ = f₄ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₅ : sparseForcing k₅ = f₅ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₆ : sparseForcing k₆ = f₆ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₇ : sparseForcing k₇ = f₇ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem sparseForcing_k₈ : sparseForcing k₈ = f₈ := by
  funext j
  fin_cases j <;> snapshot_simp

theorem projectedNonlinearity_k₁ : projectedNonlinearity u₀ k₁ = f₁ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₁]

theorem projectedNonlinearity_k₂ : projectedNonlinearity u₀ k₂ = f₂ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₂]

theorem projectedNonlinearity_k₃ : projectedNonlinearity u₀ k₃ = f₃ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₃]

theorem projectedNonlinearity_k₄ : projectedNonlinearity u₀ k₄ = f₄ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₄]

theorem projectedNonlinearity_k₅ : projectedNonlinearity u₀ k₅ = f₅ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₅]

theorem projectedNonlinearity_k₆ : projectedNonlinearity u₀ k₆ = f₆ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₆]

theorem projectedNonlinearity_k₇ : projectedNonlinearity u₀ k₇ = f₇ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₇]

theorem projectedNonlinearity_k₈ : projectedNonlinearity u₀ k₈ = f₈ := by
  rw [projectedNonlinearity_u₀_eq_sparse, sparseForcing_k₈]

/-- Executable modal forcing function matching the R836 sparse certificate. -/
def forcing₃₄₅ : State := fun k =>
  if k = k₁ then f₁
  else if k = k₂ then f₂
  else if k = k₃ then f₃
  else if k = k₄ then f₄
  else if k = k₅ then f₅
  else if k = k₆ then f₆
  else if k = k₇ then f₇
  else if k = k₈ then f₈
  else 0

theorem projectedNonlinearity_u₀_eq_forcing₃₄₅ :
    projectedNonlinearity u₀ = forcing₃₄₅ := by
  funext k
  by_cases hk : k ∈ activeOutputs
  · simp [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈] at hk
    rcases hk with h | h | h | h | h | h | h | h
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₁
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₂
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₃
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₄
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₅
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₆
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₇
    · subst k; simpa [forcing₃₄₅] using projectedNonlinearity_k₈
  · have hz := projectedNonlinearity_u₀_zero_of_not_mem_active hk
    have hne :
        k ≠ k₁ ∧ k ≠ k₂ ∧ k ≠ k₃ ∧ k ≠ k₄ ∧
        k ≠ k₅ ∧ k ≠ k₆ ∧ k ≠ k₇ ∧ k ≠ k₈ := by
      simpa [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈] using hk
    rcases hne with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    simpa [forcing₃₄₅, h1,h2,h3,h4,h5,h6,h7,h8] using hz

end Rational345RealSnapshotRows
end NSBControl
