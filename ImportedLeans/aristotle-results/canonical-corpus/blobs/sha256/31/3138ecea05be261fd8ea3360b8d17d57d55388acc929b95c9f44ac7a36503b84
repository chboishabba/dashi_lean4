/-
# Non-vacuity and axiom checks for the marked polymer decay lane

The Row-B marked-activity theorems are conditional on an activity majorant with
a polynomial mark factor and on a polymer entropy bound.  This file exhibits a
concrete polymer family satisfying both with *nonzero* activities and a
*genuinely growing* shell, and records that the whole lane depends on no axioms
beyond the three standard ones.
-/
import RequestProject.YangMills.MarkedPolymerDecay

namespace YangMills
namespace MarkedPolymerWitness

open Finset

/-- A polymer family whose shell of size `n` contains `2ⁿ` polymers: the entropy
is genuinely exponential, with rate `ν = log 2`. -/
def shellW (n : ℕ) : Finset (ℕ × ℕ) := (range (2 ^ n)).image (fun i => (n, i))

theorem shellW_card (n : ℕ) : (shellW n).card = 2 ^ n := by
  rw [shellW, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_range]

/-- A nonzero activity with one mark, decaying at rate `μ = 2`. -/
noncomputable def actW : ℕ × ℕ → ℝ := fun x => (x.1 : ℝ) * Real.exp (-(2 * (x.1 : ℝ)))

theorem actW_bound (n : ℕ) : ∀ x ∈ shellW n,
    |actW x| ≤ 1 * (n : ℝ) ^ 1 * Real.exp (-(2 * (n : ℝ))) := by
  intro x hx
  have hx1 : x.1 = n := by
    rw [shellW, Finset.mem_image] at hx
    obtain ⟨i, -, hi⟩ := hx
    rw [← hi]
  rw [actW, hx1, abs_of_nonneg (by positivity)]
  simp

theorem shellW_entropy (n : ℕ) :
    ((shellW n).card : ℝ) ≤ 1 * Real.exp (Real.log 2 * n) := by
  rw [shellW_card, one_mul, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  norm_num

theorem log_two_lt_two : Real.log 2 < 2 := by
  have h : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  linarith

/-- The marked shell energy of this family is geometrically small, and the
family is not degenerate: the activities are nonzero and the shell grows
exponentially. -/
theorem marked_witness (n : ℕ) :
    ∑ x ∈ shellW n, |actW x|
      ≤ ((1 * markCost 1 2 (Real.log 2)) * 1)
          * shellRatio (Real.log 2) (markedRate 2 (Real.log 2)) ^ n :=
  marked_shell_energy_geometric (m := 1) (A := 1) (B := 1)
    actW_bound shellW_entropy (by norm_num) log_two_lt_two n

theorem actW_nonzero : actW (1, 0) ≠ 0 := by
  rw [actW]
  simp [Real.exp_ne_zero]

theorem shellW_grows : (shellW 5).card = 32 := by
  rw [shellW_card]
  norm_num

end MarkedPolymerWitness

section AxiomChecks

#print axioms pow_mul_exp_neg_le
#print axioms pow_mul_exp_decay_le
#print axioms marked_activity_bound
#print axioms marked_shell_energy_geometric
#print axioms marked_shell_energy_summable
#print axioms marked_shell_energy_tsum_le
#print axioms MarkedPolymerWitness.marked_witness

end AxiomChecks

end YangMills
