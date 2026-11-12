import Integration.BishopRiemannZetaNativeMachinContinuity
import Mathlib.Tactic

/-!
# Positive odd zeta window: original Bishop/Dirichlet values = Mathlib zeta

External mathematical source: W. Zudilin, arXiv:1801.09895.
The July 2026 formalization of the disjunction through zeta(33) is NOT
reproduced or imported here. No irrationality is assumed or asserted.

DASHI contribution: specialize the already established same-object
positive-half-plane theorem from BishopRiemannZetaNativeMachinContinuity
to every odd index 5 + 2*k. Then transfer a rationality predicate and
its finite existential negation with no new zeta axioms.

This is Lean source written against the PR #104 branch, NOT a claim of
successful kernel compilation or Agda's original real-carrier identity.
-/

namespace Integration.BishopOddZetaHalfPlaneSpecialization

open Integration.BishopRiemannZetaNativeMachinContinuity

noncomputable section

def oddArgument (k : ℕ) : ℕ := 5 + 2 * k

private theorem oddArgument_gt_one (k : ℕ) : 1 < oddArgument k := by
  unfold oddArgument
  omega

theorem originalOddDirichlet_eq_riemannZeta (k : ℕ) :
    originalDirichletValue ((oddArgument k : ℕ) : ℂ) =
      riemannZeta ((oddArgument k : ℕ) : ℂ) := by
  apply originalDirichletValue_eq_riemannZeta
  have h : (1 : ℝ) < ((oddArgument k : ℕ) : ℝ) := by
    exact_mod_cast oddArgument_gt_one k
  simpa using h

/-- All 15 entries of the finite Zudilin fallback window are actual
genuine zeta values, not fifteen unrelated abstract real functions. -/
theorem originalOddWindow_eq_riemannZeta (k : Fin 15) :
    originalDirichletValue ((oddArgument k.val : ℕ) : ℂ) =
      riemannZeta ((oddArgument k.val : ℕ) : ℂ) :=
  originalOddDirichlet_eq_riemannZeta k.val

/-- Explicit rational image in the selected complex carrier.
This is deliberately not confused with Mathlib's `Irrational` predicate
on real numbers until the real/complex value coercion is welded. -/
def HasRationalComplexValue (z : ℂ) : Prop :=
  ∃ q : ℚ, z = (q : ℂ)

theorem oddWindow_rational_iff (k : Fin 15) :
    HasRationalComplexValue
      (originalDirichletValue ((oddArgument k.val : ℕ) : ℂ)) ↔
    HasRationalComplexValue
      (riemannZeta ((oddArgument k.val : ℕ) : ℂ)) := by
  rw [originalOddWindow_eq_riemannZeta]

theorem oddWindow_irrational_iff (k : Fin 15) :
    ¬ HasRationalComplexValue
      (originalDirichletValue ((oddArgument k.val : ℕ) : ℂ)) ↔
    ¬ HasRationalComplexValue
      (riemannZeta ((oddArgument k.val : ℕ) : ℂ)) := by
  rw [originalOddWindow_eq_riemannZeta]

/-- An existential theorem is transported between exactly the
two same-object sources, without choosing or manufacturing an index. -/
theorem zetaOddWindow_exists_iff_sourceWindow :
    (∃ k : Fin 15,
      ¬ HasRationalComplexValue
        (riemannZeta ((oddArgument k.val : ℕ) : ℂ))) ↔
    (∃ k : Fin 15,
      ¬ HasRationalComplexValue
        (originalDirichletValue ((oddArgument k.val : ℕ) : ℂ))) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (oddWindow_irrational_iff k).mpr hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (oddWindow_irrational_iff k).mp hk⟩

#print axioms originalOddDirichlet_eq_riemannZeta
#print axioms zetaOddWindow_exists_iff_sourceWindow

end

end Integration.BishopOddZetaHalfPlaneSpecialization
