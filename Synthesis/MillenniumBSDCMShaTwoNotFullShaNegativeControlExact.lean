import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# BSD logical negative control: Sha[2]=0 does NOT imply Sha=0

This is a finite, constructive counterexample in the category of
abelian groups: the additive group Z/3 is nonzero but has no
nonzero elements killed by 2. Therefore any theorem promoting
vanishing of Sha(E)[2] to full Sha(E) must use additional
arithmetic hypotheses; it cannot follow from the formal
two-Selmer short exact sequence alone.

This counterexample does not claim that Z/3 occurs as the actual
Sha(E/Q) of the selected curve. It blocks the invalid deduction.
-/

namespace Synthesis.Millennium.BSD

/-- The abelian group Z/3 has trivial two-torsion. -/
theorem cmNonzeroAbelianGroupWithVanishingTwoTorsion
    (x : ZMod 3) (hx : (2 : ℕ) • x = 0) : x = 0 := by
  fin_cases x <;> norm_num at hx ⊢

/-- But that same group has a nonzero element: no implication
from A[2]=0 to A=0 is available for arbitrary abelian groups. -/
theorem cmVanishingTwoTorsion_doesNotForceTrivialGroup :
    (∀ x : ZMod 3, (2 : ℕ) • x = 0 → x = 0) ∧
    (∃ x : ZMod 3, x ≠ 0) := by
  constructor
  · intro x hx
    exact cmNonzeroAbelianGroupWithVanishingTwoTorsion x hx
  · exact ⟨1, by norm_num⟩

end Synthesis.Millennium.BSD
