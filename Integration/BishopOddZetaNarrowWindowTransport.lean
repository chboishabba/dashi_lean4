import Integration.BishopOddZetaHalfPlaneSpecialization
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# The narrower external odd-zeta window: source-faithful predicate transport

EXTERNAL MATHEMATICS / FORMALIZATION
  ZetaIrr.Z7.oneOfZeta7To21, telaviv/zeta-irrationality, author
  Shawn Krisman, based on W. Zudilin and the preceding literature.
  Its claimed kernel audit is NOT reproduced or imported in this file.

DASHI contribution
  (1) Relate Mathlib's *real* Irrational to the existing original
      Dirichlet source's explicit rational complex-value predicate;
  (2) embed the 8-point {7,9,...,21} window into the 15-point
      {5,7,...,33} window without changing the argument.
  (3) transport a supplied witness without assuming that it exists.

No genuine odd-zeta irrationality is manufactured here.
No cross-kernel Agda/Bishop equality is asserted.
-/

namespace Integration.BishopOddZetaNarrowWindowTransport

open Integration.BishopOddZetaHalfPlaneSpecialization
open Integration.BishopRiemannZetaNativeMachinContinuity

noncomputable section

/-- The target's rationality predicate is exactly rationality of
the real part, provided the complex point is the canonical real cast. -/
theorem irrational_real_iff_no_rational_complex (x : ℝ) :
    Irrational x ↔ ¬ HasRationalComplexValue (x : ℂ) := by
  change (¬ ∃ q : ℚ, (q : ℝ) = x) ↔
    ¬ ∃ q : ℚ, (x : ℂ) = (q : ℂ)
  constructor
  · intro hx hcomplex
    obtain ⟨q, hq⟩ := hcomplex
    apply hx
    refine ⟨q, ?_⟩
    exact_mod_cast hq.symm
  · intro hx hreal
    obtain ⟨q, hq⟩ := hreal
    apply hx
    refine ⟨q, ?_⟩
    exact_mod_cast hq.symm

/-- Explicit source-side real-valuedness is a separate input;
in this development it will be discharged by genuine zeta's positive
integer realness theorem, not by the name 'zeta'. -/
theorem irrational_re_iff_complex_rational_neg
    (z : ℂ) (hz : z.im = 0) :
    Irrational z.re ↔ ¬ HasRationalComplexValue z := by
  have hcast : ((z.re : ℝ) : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa [hz]
  rw [← hcast]
  exact irrational_real_iff_no_rational_complex z.re

/-- Faithfully embed the eight-term Z7 window in the fifteen-term
Zudilin fallback window. -/
def intoFifteen (k : Fin 8) : Fin 15 :=
  ⟨k.val + 1, by omega⟩

theorem intoFifteen_same_argument (k : Fin 8) :
    oddArgument (intoFifteen k).val = 7 + 2 * k.val := by
  simp only [intoFifteen, oddArgument]
  omega

/-- Unconditionally available *bridge theorem*, conditional on the
actual external real-irrationality witness and on selected real-valuedness.
The latter is deliberately not silently inferred from equality of names. -/
theorem narrowerWitness_to_originalSource
    (hreal : ∀ k : Fin 8,
      (riemannZeta ((7 + 2 * k.val : ℕ) : ℂ)).im = 0)
    (h : ∃ k : Fin 8,
      Irrational (riemannZeta ((7 + 2 * k.val : ℕ) : ℂ)).re) :
    ∃ j : Fin 15,
      ¬ HasRationalComplexValue
        (originalDirichletValue ((oddArgument j.val : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨intoFifteen k, ?_⟩
  have harg :
      ((oddArgument (intoFifteen k).val : ℕ) : ℂ) =
        ((7 + 2 * k.val : ℕ) : ℂ) := by
    exact_mod_cast intoFifteen_same_argument k
  rw [originalOddWindow_eq_riemannZeta, harg]
  exact (irrational_re_iff_complex_rational_neg _ (hreal k)).mp hk

#print axioms irrational_real_iff_no_rational_complex
#print axioms intoFifteen_same_argument
#print axioms narrowerWitness_to_originalSource

end
end Integration.BishopOddZetaNarrowWindowTransport
