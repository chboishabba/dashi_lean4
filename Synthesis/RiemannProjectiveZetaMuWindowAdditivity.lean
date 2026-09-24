import Synthesis.RiemannProjectiveZetaMuLocalNegative

/-!
# Exact window additivity for the literal projective N-mu residual

The signed residual is a genuine finitely additive ordinate-window object.
For A <= B <= C,

  E_t(A,C) = E_t(A,B) + E_t(B,C).

The zero part is proved on the literal Zeta23 windows
(A,B], (B,C], whose union is (A,C] and which are disjoint.  The smooth part is
ordinary interval-integral additivity.

This is the right algebra for the next Goal-1 step: decompose the global
restricted N-mu consumer into zero jumps and the zero-free gaps between them,
rather than taking a global absolute value.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

open Zeta23

private theorem zeta_window_union
    {A B C : ℝ} (hAB : A <= B) (hBC : B <= C) :
    zetaZeroConfig.window A B ∪ zetaZeroConfig.window B C
      = zetaZeroConfig.window A C := by
  ext rho
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨h.1, h.2.1, h.2.2.trans hBC⟩
    · exact ⟨h.1, hAB.lt_of_lt h.2.1, h.2.2⟩
  · intro h
    by_cases him : rho.im <= B
    · exact Or.inl ⟨h.1, h.2.1, him⟩
    · exact Or.inr ⟨h.1, lt_of_not_ge him, h.2.2⟩

private theorem zeta_window_disjoint
    (A B C : ℝ) :
    Disjoint (zetaZeroConfig.window A B) (zetaZeroConfig.window B C) := by
  rw [Set.disjoint_left]
  intro rho h1 h2
  linarith [h1.2.2, h2.2.1]

/-- Literal multiplicity-weighted zero pairing is exactly additive across an
intermediate ordinate. -/
theorem zetaWindowWeightedPair_add
    {A B C : ℝ} (hAB : A <= B) (hBC : B <= C)
    (phi : ℝ -> ℝ) :
    zetaWindowWeightedPair A C phi
      =
    zetaWindowWeightedPair A B phi
      + zetaWindowWeightedPair B C phi := by
  unfold zetaWindowWeightedPair
  let f : ℂ -> ℝ := fun rho =>
    (zetaZeroConfig.mult rho : ℝ) * phi rho.im
  have hU := zeta_window_union hAB hBC
  have hD := zeta_window_disjoint A B C
  have hABfin := zetaZeroConfig.finite_window A B
  have hBCfin := zetaZeroConfig.finite_window B C
  rw [← hU]
  exact finsum_mem_union hD hABfin hBCfin

/-- Exact additivity of the literal zero-minus-mu pairing. -/
theorem zetaWindowMinusMuPair_add
    {A B C : ℝ} (hAB : A <= B) (hBC : B <= C)
    {phi : ℝ -> ℝ}
    (hint :
      IntervalIntegrable
        (fun x => phi x * Zeta23.mu x) volume A C) :
    zetaWindowMinusMuPair A C phi
      =
    zetaWindowMinusMuPair A B phi
      + zetaWindowMinusMuPair B C phi := by
  have hleft :
      IntervalIntegrable
        (fun x => phi x * Zeta23.mu x) volume A B := by
    exact hint.mono_set (by
      rw [Set.uIcc_of_le hAB, Set.uIcc_of_le (hAB.trans hBC)]
      intro x hx
      exact ⟨hx.1, hx.2.trans hBC⟩)
  have hright :
      IntervalIntegrable
        (fun x => phi x * Zeta23.mu x) volume B C := by
    exact hint.mono_set (by
      rw [Set.uIcc_of_le hBC, Set.uIcc_of_le (hAB.trans hBC)]
      intro x hx
      exact ⟨hAB.trans hx.1, hx.2⟩)
  unfold zetaWindowMinusMuPair
  rw [zetaWindowWeightedPair_add hAB hBC phi]
  rw [intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

/-- The actual projective N-mu consumer is additive on every ordered triple of
ordinate endpoints. -/
theorem projectiveZetaMuWindowResidual_add
    {t A B C : ℝ}
    (hAB : A <= B) (hBC : B <= C) :
    projectiveZetaMuWindowResidual t A C
      =
    projectiveZetaMuWindowResidual t A B
      + projectiveZetaMuWindowResidual t B C := by
  unfold projectiveZetaMuWindowResidual
  apply zetaWindowMinusMuPair_add hAB hBC
  have hphi : Continuous (normalizedProjectiveOrdinateTest t) := by
    by_cases ht0 : t = 0
    · subst t
      unfold normalizedProjectiveOrdinateTest
      simp
      fun_prop
    · exact continuous_of_forall_continuousAt fun x =>
        (normalizedProjectiveOrdinateTest_hasDerivAt
          (t := t) (gamma := x) ht0).continuousAt
  have hmu : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  exact (hphi.mul hmu).intervalIntegrable A C

end Synthesis
