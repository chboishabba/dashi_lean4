import Mathlib.Tactic
import NSBControl.Rational345BQGeometry

/-!
# Cutoff-four degeneration of the R781/R798 separated family

The literal R25/R781 shell classifier uses overlap radius Csep = 3.  On the
radius-four Fourier cube every mode has max-coordinate magnitude at most four,
so its dyadic shell index is one of 0,1,2.  Hence no pair of cutoff-four modes
can differ by three shells.  The base scale class of every physical triad is
therefore `comparable`.

R781 marks an orbit `ccTouched` when any one of its three scale classes is
comparable.  Since the base class already is comparable, `ccTouched` is always
true at cutoff four, and R798's complementary fully-separated weight is
identically zero.

This is a cutoff-specific finite combinatorial theorem, not an analytic
estimate.
-/

namespace NSBControl
namespace Rational345R823Cutoff4Separation

open Rational345RealRadius4
open Rational345BQGeometry

classical

/-- Exact radius-four form of ceil(log2(max |k_j|)).  The ambient carrier has
max magnitude at most four, so only the values 0,1,2 occur. -/
def literalShellIndex4 (k : Mode) : ℕ :=
  if maxAbs k ≤ 1 then 0 else if maxAbs k ≤ 2 then 1 else 2

/-- The finite carrier really is bounded by four; `literalShellIndex4` is not a
truncation of larger frequencies. -/
theorem maxAbs_le_four : ∀ k : Mode, maxAbs k ≤ 4 := by
  native_decide

theorem shellIndex4_le_two (k : Mode) : literalShellIndex4 k ≤ 2 := by
  unfold literalShellIndex4
  split_ifs <;> omega

inductive ScaleRegime where
  | lowHigh
  | highLow
  | highHigh
  | comparable
deriving DecidableEq, Repr

/-- Literal R25 scale decision specialized to overlap radius three. -/
def classifyScale4 (p q k : Mode) : ScaleRegime :=
  if literalShellIndex4 p + 3 < literalShellIndex4 q then
    ScaleRegime.lowHigh
  else if literalShellIndex4 q + 3 < literalShellIndex4 p then
    ScaleRegime.highLow
  else if literalShellIndex4 k + 3 < literalShellIndex4 p ∧
          literalShellIndex4 k + 3 < literalShellIndex4 q then
    ScaleRegime.highHigh
  else
    ScaleRegime.comparable

/-- No three-shell separation is possible anywhere in the radius-four cube. -/
theorem classifyScale4_always_comparable (p q k : Mode) :
    classifyScale4 p q k = ScaleRegime.comparable := by
  have hp := shellIndex4_le_two p
  have hq := shellIndex4_le_two q
  have hk := shellIndex4_le_two k
  unfold classifyScale4
  split_ifs with h₁ h₂ h₃
  · omega
  · omega
  · omega
  · rfl

/-- R781's `profileTouchesComparable` is already true from the base coordinate;
there is no need to inspect the two energy-leg coordinates at cutoff four. -/
def ccTouched4 (p q k : Mode) : Bool :=
  decide (classifyScale4 p q k = ScaleRegime.comparable)

theorem ccTouched4_always_true (p q k : Mode) :
    ccTouched4 p q k = true := by
  simp [ccTouched4, classifyScale4_always_comparable]

/-- R798's fully-separated indicator specialized to the real cutoff-four
carrier. -/
def separatedWeight4 (p q k : Mode) : ℝ :=
  if ccTouched4 p q k then 0 else 1

theorem separatedWeight4_zero (p q k : Mode) :
    separatedWeight4 p q k = 0 := by
  simp [separatedWeight4, ccTouched4_always_true]

/-- Consequently every finite fold carrying the separated indicator vanishes. -/
theorem separatedWeighted_sum_zero
    {α : Type*} [Fintype α]
    (p q k : α → Mode)
    (cell : α → ℝ) :
    (∑ a : α, separatedWeight4 (p a) (q a) (k a) * cell a) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  rw [separatedWeight4_zero]
  simp

/-- Cutoff-four R781/R798 combinatorial degeneration is closed. -/
def r823Cutoff4SeparatedFamilyEmpty : Bool := true

end Rational345R823Cutoff4Separation
end NSBControl
