import Integration.EisensteinLatticeCounting
import Mathlib.Data.Nat.Choose.Sum

namespace Dashi.EisensteinLatticeCountingMaxCut

open Finset
open Dashi.EisensteinLatticeCounting

def pascalRowSum (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), n.choose k

theorem pascalRowSum_eq_two_pow (n : Nat) : pascalRowSum n = 2 ^ n := by
  simpa [pascalRowSum] using Nat.sum_range_choose n

theorem two_mul_triangularNumber (n : Nat) :
    2 * triangularNumber n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [triangularNumber, ih]
      ring

theorem hexBallCount_closed (n : Nat) :
    hexBallCount n = 3 * n * n + 3 * n + 1 := by
  calc
    hexBallCount n = 1 + 6 * triangularNumber n := rfl
    _ = 1 + 3 * (2 * triangularNumber n) := by ring
    _ = 1 + 3 * (n * (n + 1)) := by rw [two_mul_triangularNumber]
    _ = 3 * n * n + 3 * n + 1 := by ring

theorem eisensteinNorm_four_decomposition_a (a b : Int) :
    4 * eisensteinNorm a b = 3 * (a * a) + (a - 2 * b) * (a - 2 * b) := by
  simp [eisensteinNorm]
  ring

theorem eisensteinNorm_four_decomposition_b (a b : Int) :
    4 * eisensteinNorm a b = 3 * (b * b) + (2 * a - b) * (2 * a - b) := by
  simp [eisensteinNorm]
  ring

theorem eisensteinNorm_coercive_a (a b : Int) :
    3 * (a * a) ≤ 4 * eisensteinNorm a b := by
  rw [eisensteinNorm_four_decomposition_a]
  exact le_add_of_nonneg_right (sq_nonneg (a - 2 * b))

theorem eisensteinNorm_coercive_b (a b : Int) :
    3 * (b * b) ≤ 4 * eisensteinNorm a b := by
  rw [eisensteinNorm_four_decomposition_b]
  exact le_add_of_nonneg_right (sq_nonneg (2 * a - b))

def rotate (p : Int × Int) : Int × Int := (p.1 - p.2, p.1)

theorem rotate_norm (a b : Int) :
    eisensteinNorm (a - b) a = eisensteinNorm a b := by
  simp [eisensteinNorm]
  ring

theorem rotate_six (p : Int × Int) :
    rotate (rotate (rotate (rotate (rotate (rotate p))))) = p := by
  rcases p with ⟨a, b⟩
  ext <;> simp [rotate] <;> ring

/-- The universal representation theorem is correctly scoped to positive norms.
At `n = 0`, the geometric fibre contains `(0,0)` while the positive-divisor
formula contributes zero. -/
structure UniversalRepresentationSource where
  representation_formula_positive :
    ∀ n : Nat,
      geometricNormShellCount (n + 1) = eisensteinDivisorShellCount (n + 1)

/-- Once the positive-n representation theorem is supplied, the same-object bridge is immediate. -/
def bridgeOfUniversalSource (S : UniversalRepresentationSource) :
    EisensteinNormRepresentationBridge where
  representationCount := geometricNormShellCount
  representationCount_eq_divisorLaw_positive := S.representation_formula_positive

end Dashi.EisensteinLatticeCountingMaxCut
