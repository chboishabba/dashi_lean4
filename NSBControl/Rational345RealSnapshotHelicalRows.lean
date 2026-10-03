import Mathlib.Tactic
import NSBControl.Rational345RealSnapshotHelicalSparse

/-!
# W2 exact real R224/R230 rows

Evaluates the genuine real helical mixed and forcing-commutator folds at the
eight active 3-4-5 outputs.  The targets are exactly the m_i/g_i vectors used
by Agda R829B/R845/R849.
-/

namespace NSBControl
namespace Rational345RealSnapshotHelicalRows

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse
open Rational345RealSnapshotRows
open Rational345RealSnapshotHelicalSparse

classical

private def c (re im : ℝ) : ℂ := re + im * Complex.I
private def v (xr xi yr yi zr zi : ℝ) : Vec3 :=
  ![c xr xi, c yr yi, c zr zi]

-- Exact R829B mixed rows.
def m₁ : Vec3 := v (-7) (-1) (-7) (-1) (-1) 1
def m₂ : Vec3 := v (-21/10) (-9/2) (7/10) (3/2) (-69/10) (-9/2)
def m₃ : Vec3 := v 1 1 (-1) (-1) (-1) 7
def m₄ : Vec3 := v (-9/5) (-17/5) (18/5) (34/5) (-46/5) (-3)
def m₅ : Vec3 := v (-9/5) (17/5) (18/5) (-34/5) (-46/5) 3
def m₆ : Vec3 := v 1 (-1) (-1) 1 (-1) (-7)
def m₇ : Vec3 := v (-21/10) (9/2) (7/10) (-3/2) (-69/10) (9/2)
def m₈ : Vec3 := v (-7) 1 (-7) 1 (-1) (-1)

-- Exact R829B commutator rows.
def g₁ : Vec3 := v 8 (-23) 8 (-23) (-98) (-56)
def g₂ : Vec3 := v (-246/5) 42 (858/25) (-678/25) (-909/5) (225/2)
def g₃ : Vec3 := v 2 (-35) (-2) 35 308 50
def g₄ : Vec3 := v (2913/50) (-833/50) (-117/5) (-171/5) (5428/25) (-5412/25)
def g₅ : Vec3 := v (2913/50) (833/50) (-117/5) (171/5) (5428/25) (5412/25)
def g₆ : Vec3 := v 2 35 (-2) (-35) 308 (-50)
def g₇ : Vec3 := v (-246/5) (-42) (858/25) (678/25) (-909/5) (-225/2)
def g₈ : Vec3 := v 8 23 8 23 (-98) 56

private macro "helical_snapshot_simp" : tactic =>
  `(tactic|
    (simp [sparseMixed, sparseCommutator, seedModes, activeOutputs,
      mixedCell, forcingCommutatorCell, helicalPlus, helicalMinus,
      inverseModeNorm, modeNorm, normSq, leray, curlSymbol, cross,
      bilinearDot, kComplex, Resonates, kReal, kInt, axisInt,
      forcing₃₄₅, f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈,
      u₀, v300, v040, v340, vecConj,
      k300, km300, k040, k0m40, k340, km3m40, km340, k3m40,
      k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
      c, v, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈,
      g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈] <;>
      norm_num <;> ring))

-- Genuine real R224 mixed rows.
theorem sparseMixed_k₁ : sparseMixed k₁ = m₁ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₂ : sparseMixed k₂ = m₂ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₃ : sparseMixed k₃ = m₃ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₄ : sparseMixed k₄ = m₄ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₅ : sparseMixed k₅ = m₅ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₆ : sparseMixed k₆ = m₆ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₇ : sparseMixed k₇ = m₇ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseMixed_k₈ : sparseMixed k₈ = m₈ := by
  funext j; fin_cases j <;> helical_snapshot_simp

-- Genuine real R230 forcing-commutator rows.
theorem sparseCommutator_k₁ : sparseCommutator k₁ = g₁ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₂ : sparseCommutator k₂ = g₂ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₃ : sparseCommutator k₃ = g₃ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₄ : sparseCommutator k₄ = g₄ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₅ : sparseCommutator k₅ = g₅ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₆ : sparseCommutator k₆ = g₆ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₇ : sparseCommutator k₇ = g₇ := by
  funext j; fin_cases j <;> helical_snapshot_simp

theorem sparseCommutator_k₈ : sparseCommutator k₈ = g₈ := by
  funext j; fin_cases j <;> helical_snapshot_simp

-- Public same-object rows through the literal full operators.
theorem fixedOutputMixed_k₁ : fixedOutputMixed u₀ k₁ = m₁ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₁]
theorem fixedOutputMixed_k₂ : fixedOutputMixed u₀ k₂ = m₂ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₂]
theorem fixedOutputMixed_k₃ : fixedOutputMixed u₀ k₃ = m₃ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₃]
theorem fixedOutputMixed_k₄ : fixedOutputMixed u₀ k₄ = m₄ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₄]
theorem fixedOutputMixed_k₅ : fixedOutputMixed u₀ k₅ = m₅ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₅]
theorem fixedOutputMixed_k₆ : fixedOutputMixed u₀ k₆ = m₆ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₆]
theorem fixedOutputMixed_k₇ : fixedOutputMixed u₀ k₇ = m₇ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₇]
theorem fixedOutputMixed_k₈ : fixedOutputMixed u₀ k₈ = m₈ := by
  rw [fixedOutputMixed_u₀_eq_sparse, sparseMixed_k₈]

theorem fixedOutputCommutator_k₁ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₁ = g₁ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₁]
theorem fixedOutputCommutator_k₂ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₂ = g₂ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₂]
theorem fixedOutputCommutator_k₃ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₃ = g₃ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₃]
theorem fixedOutputCommutator_k₄ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₄ = g₄ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₄]
theorem fixedOutputCommutator_k₅ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₅ = g₅ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₅]
theorem fixedOutputCommutator_k₆ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₆ = g₆ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₆]
theorem fixedOutputCommutator_k₇ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₇ = g₇ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₇]
theorem fixedOutputCommutator_k₈ :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k₈ = g₈ := by
  rw [fixedOutputCommutator_u₀_eq_sparse, sparseCommutator_k₈]

end Rational345RealSnapshotHelicalRows
end NSBControl
