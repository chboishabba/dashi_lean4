import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Same-object completed Riemann xi function and functional symmetry

Mathlib's `completedRiemannZeta` is the meromorphic Lambda(s),
whereas `completedRiemannZeta₀` is the *entire* pole-subtracted
completion. The standard xi is recovered without evaluating a pole:

    xi(s) = (s(s-1) * completedRiemannZeta₀(s) + 1) / 2.

This identity follows from
    completedRiemannZeta₀ = completedRiemannZeta + 1/s + 1/(1-s),
away from 0 and 1.

External theorem source: Mathlib's `completedRiemannZeta₀_one_sub`,
from its Hurwitz/Mellin/theta functional-equation formalization.
DASHI contribution: a source-preserving, globally defined xi
presentation and exact reflection reuse.

This closes the functional-reflection algebra for this actual LEAN
selected Mathlib xi, NOT the independent Agda analytic-substrate
instance and NOT the Riemann Hypothesis.
-/

namespace Integration.RiemannXiMathlibReflectionExact

noncomputable section

def selectedXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem selectedXi_one_sub (s : ℂ) :
    selectedXi (1 - s) = selectedXi s := by
  unfold selectedXi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem selectedXi_zero : selectedXi 0 = 1 / 2 := by
  simp [selectedXi]

theorem selectedXi_one : selectedXi 1 = 1 / 2 := by
  simp [selectedXi]

#print axioms selectedXi_one_sub
#print axioms selectedXi_zero


/-- Exact identification with the classical completed zeta product
away from the removable poles 0 and 1. This uses Mathlib's
`completedRiemannZeta_eq`, not a new completed-zeta axiom.
It does NOT establish Weil positivity or any zero-location theorem. -/
theorem selectedXi_eq_classical_completed (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    selectedXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  have hs1sub : (1 : ℂ) - s ≠ 0 :=
    sub_ne_zero.mpr hs1.symm
  unfold selectedXi
  field_simp [hs0, hs1, hs1sub]
  ring

#print axioms selectedXi_eq_classical_completed

end
end Integration.RiemannXiMathlibReflectionExact
