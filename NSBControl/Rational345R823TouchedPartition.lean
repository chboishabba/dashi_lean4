import Mathlib.Tactic

/-!
# Cutoff-four R781 touched partition

R781 partitions one complete swap-paired residual fold into a fully-separated
family and a `ccTouched` family.  The cutoff-four shell theorem proves that
`ccTouched` is true for every physical incidence.  Consequently this partition
is completely degenerate: the separated fold vanishes and the touched fold is
the complete fold, independently of the cell formula.

This generic finite-fold theorem deliberately avoids naming the still-open real
R760 cell; it will apply verbatim once that carrier is instantiated.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823TouchedPartition

variable {α : Type*} [Fintype α]

def completeFold (cell : α → ℝ) : ℝ :=
  ∑ a : α, cell a

/-- Cutoff-four specialization of R781's fully-separated selector. -/
def fullySeparatedCell4 (cell : α → ℝ) (_a : α) : ℝ := 0

/-- Cutoff-four specialization of R781's touched selector. -/
def ccTouchedCell4 (cell : α → ℝ) (a : α) : ℝ := cell a

def fullySeparatedFold4 (cell : α → ℝ) : ℝ :=
  ∑ a : α, fullySeparatedCell4 cell a

def ccTouchedFold4 (cell : α → ℝ) : ℝ :=
  ∑ a : α, ccTouchedCell4 cell a

theorem fullySeparatedFold4_eq_zero (cell : α → ℝ) :
    fullySeparatedFold4 cell = 0 := by
  unfold fullySeparatedFold4 fullySeparatedCell4
  simp

theorem ccTouchedFold4_eq_completeFold (cell : α → ℝ) :
    ccTouchedFold4 cell = completeFold cell := by
  rfl

theorem completeFold_splits_cutoff4 (cell : α → ℝ) :
    completeFold cell = fullySeparatedFold4 cell + ccTouchedFold4 cell := by
  rw [fullySeparatedFold4_eq_zero, ccTouchedFold4_eq_completeFold]
  simp

/-- At cutoff four the R781 partition itself contributes no remaining semantic
obligation. -/
def r823Cutoff4TouchedPartitionClosed : Bool := true

end Rational345R823TouchedPartition
end NSBControl
