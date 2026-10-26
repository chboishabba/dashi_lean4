import Mathlib

/-!
# Bastounis–Circelli–Hansen (2026): concrete autoformalisation mismatches

Original source: Alexander Bastounis, Fabian Circelli and Anders C. Hansen,
"Navier–Stokes lost in translation: Why Lean verification of AI
autoformalisation does not guarantee correct natural language proofs",
arXiv:2610.08144v1 (2026-10-06), §2, §3, §4.1–4.2.
Permanent source: https://arxiv.org/html/2610.08144v1

This file is a DASHI reconstruction of **limited** mathematical fragments
of Examples 2.1, 2.2, 3.1, 3.3 and 4.3; it does not formalise the entire
source paper, the original OpenAI PDE theorem, the source's SCI results,
or a complete natural-language semantics. The paper authors retain original
credit for the examples and their analysis, and original Lean/OpenAI
authors retain credit for the audited code.

In particular, a Lean kernel proof checks the *encoded theorem*; it does
not by itself certify the source-text-to-formal-statement translation.
-/

namespace RequestProject.Autoformalisation.LostInTranslationExamples

/-! ## §2, Example 2.1: a true polynomial theorem with a false NL factorisation -/

def paperPolynomial (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - x + 1

theorem polynomial_actual_factorisation (x : ℝ) :
    paperPolynomial x = (x - 1) ^ 2 * (x + 1) := by
  dsimp [paperPolynomial]
  ring

theorem polynomial_nonnegative_on_source_domain (x : ℝ) (hx : -1 ≤ x) :
    0 ≤ paperPolynomial x := by
  rw [polynomial_actual_factorisation]
  exact mul_nonneg (sq_nonneg _) (by linarith)

/-- Evaluating at two exposes the *incorrect* factorisation quoted in the
source NL proof, rather than silently replacing its reasoning. -/
theorem incorrect_source_factorisation_fails_at_two :
    paperPolynomial 2 ≠ (2 - 1 : ℝ) * (2 + 1) ^ 2 := by
  norm_num [paperPolynomial]

/-! ## §2, Example 2.2: same conclusion versus same proof route -/

/-- This finite 2×2 real symmetric matrix instance uses the direct
sum-of-squares route. It is NOT the n×n spectral-diagonalisation proof
that Example 2.2 describes and does not purport to preserve that route. -/
theorem symmetric_two_by_two_trace_square_nonnegative
    (a b d : ℝ) :
    0 ≤ a ^ 2 + 2 * b ^ 2 + d ^ 2 := by
  positivity

/-! ## §3, Example 3.1: an extra derivative is a real hypothesis debt

The NL equation (8.19) uses C_y^(m+4) to bound C_y^m,
whereas the cited OpenAI Lean declaration at fixed commit
f9e8bc5b38b6e212696e8a30e3e91517af887bbd requires two coordinate
jets of length m+5. We formalise the *index-level* mismatch, not the
functional analytic strictness of the two C^k normed spaces.
-/

/-- A larger derivative budget can supply a smaller one. -/
def PaysDerivativeBudget (available required : ℕ) : Prop :=
  required ≤ available

theorem source_budget_pays_source_jet (m : ℕ) :
    PaysDerivativeBudget (m + 4) (m + 4) := by
  dsimp [PaysDerivativeBudget]

theorem source_budget_cannot_pay_audited_lean_jet (m : ℕ) :
    ¬ PaysDerivativeBudget (m + 4) (m + 5) := by
  dsimp [PaysDerivativeBudget]
  omega

theorem higher_derivatives_can_pay_source_order (m : ℕ) :
    PaysDerivativeBudget (m + 5) (m + 4) := by
  dsimp [PaysDerivativeBudget]
  omega

theorem audited_derivative_orders_differ (m : ℕ) :
    m + 4 ≠ m + 5 := by
  omega

/-! ## §3, Example 3.3: the additional A_R dependency

NL Eq. (10.19) depends on B_R, R but not A_R. Its cited Lean estimate
uses A_R/R + 1/R². On the *formal independent-parameter test slice*
B_R=0, R=1, the two nonnegative right-side expressions reduce to
0 and A_R+1 (apart from common coefficients). This is a disagreement
between RHS specifications, NOT a physical counterexample to the
actual PDE inequality; relations among A_R, B_R and the fields need
a separately supplied analytic theorem.
-/

def paperPressureFluxRhsAtBZeroROne : ℝ := 0

def leanPressureFluxRhsAtBZeroROne (A : ℝ) : ℝ := A + 1

theorem audited_lean_pressure_rhs_positive_at_zero :
    0 < leanPressureFluxRhsAtBZeroROne 0 := by
  norm_num [leanPressureFluxRhsAtBZeroROne]

/-- No finite multiplicative constant compares these two *syntactic
budgets* on the independent-parameter slice. This does not assert the
source's A_R can be chosen independently in a physical NS solution. -/
theorem pressure_rhs_no_unconditional_comparison :
    ¬ ∃ C : ℝ, ∀ A : ℝ, 0 ≤ A →
      leanPressureFluxRhsAtBZeroROne A ≤
        C * paperPressureFluxRhsAtBZeroROne := by
  rintro ⟨C, h⟩
  have h0 := h 0 (le_refl (0 : ℝ))
  norm_num [leanPressureFluxRhsAtBZeroROne,
    paperPressureFluxRhsAtBZeroROne] at h0

/-! ## §4, Example 4.3: a default value is not an existence witness

B_e(n) says there are no natural solutions x₁+x₂=n.
But (x₁,x₂)=(n,0) always solves the displayed equation.
The source's faithful "least n satisfying B_e" has NO value.
Nat.sInf applied to the empty set returns zero, furnishing a
well-typed *different* Lean expression that satisfies an unrelated
algebraic identity. No SCI/arithmetical hierarchy theorem is
established by this elementary counterexample.
-/

def sourcePolynomial3 (n x₁ x₂ : ℕ) : ℤ :=
  (x₁ : ℤ) + (x₂ : ℤ) - (n : ℤ)

def noNaturalRoot (n : ℕ) : Prop :=
  ∀ x₁ x₂ : ℕ, sourcePolynomial3 n x₁ x₂ ≠ 0

theorem source_polynomial_has_root (n : ℕ) :
    sourcePolynomial3 n n 0 = 0 := by
  simp [sourcePolynomial3]

theorem noNaturalRoot_is_impossible (n : ℕ) :
    ¬ noNaturalRoot n := by
  intro h
  exact h n 0 (source_polynomial_has_root n)

theorem no_faithful_minimum_exists :
    ¬ ∃ n : ℕ, noNaturalRoot n := by
  rintro ⟨n, h⟩
  exact noNaturalRoot_is_impossible n h

noncomputable def defaultedMinimum : ℕ :=
  sInf {n : ℕ | noNaturalRoot n}

/-- The executable-appearing selector represents a *different*
semantics from the source's partial least-number definition. -/
theorem defaultedMinimum_is_zero :
    defaultedMinimum = 0 := by
  have hEmpty : {n : ℕ | noNaturalRoot n} = ∅ := by
    ext n
    simp [noNaturalRoot_is_impossible n]
  simp [defaultedMinimum, hEmpty]

noncomputable def defaultedRational : ℚ :=
  1 / ((defaultedMinimum : ℚ) + 1)

theorem defaultedRational_is_one :
    defaultedRational = 1 := by
  simp [defaultedRational, defaultedMinimum_is_zero]

theorem defaulted_identity_compiles_but_presupposition_fails :
    (defaultedRational + 1) ^ 2 =
      defaultedRational ^ 2 + 2 * defaultedRational + 1 := by
  ring

/-! A fidelity-preserving replacement must carry existence in its type.
For the particular source polynomial, no such input is available. -/

structure FaithfulMinimumWitness where
  n : ℕ
  admissible : noNaturalRoot n
  minimal : ∀ m : ℕ, noNaturalRoot m → n ≤ m

theorem no_faithful_minimum_witness :
    ¬ Nonempty FaithfulMinimumWitness := by
  rintro ⟨w⟩
  exact noNaturalRoot_is_impossible w.n w.admissible

end RequestProject.Autoformalisation.LostInTranslationExamples
