import Synthesis.RiemannNormalizedCenteredOffHorizontalSplit

/-!
# Finite normalized zero-counting Stieltjes surface

This file packages the one-dimensional part of the normalized Off aggregate as
an exact atomic counting functional on the actual zeta zero carrier.

For a finite set F of literal zeros and sample height t, set

  q_rho = (Im rho - t) / t.

The normalized counting functional is

  <phi, mu_{t,F}>
    = sum_{rho in F} m_rho * phi(q_rho).

Its cumulative function is

  N_{t,F}(x)
    = sum_{rho in F, q_rho <= x} m_rho.

The normalized base Off aggregate is definitionally the pairing of the
normalized centered base transform with this actual counting functional.

This is deliberately finite: it is the exact Stieltjes/Abel surface needed for
the difficult intermediate carrier before passing to tails or limits.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23

def normalizedFiniteCountingPair
    (t : ℝ) (F : Finset Zeros) (phi : ℝ → ℝ) : ℝ :=
  ∑ rho ∈ F,
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) * phi (normalizedGap t rho)

def normalizedFiniteCount
    (t : ℝ) (F : Finset Zeros) (x : ℝ) : ℝ :=
  ∑ rho ∈ F.filter (fun rho => normalizedGap t rho <= x),
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)

theorem normalizedFiniteCount_nonneg
    (t : ℝ) (F : Finset Zeros) (x : ℝ) :
    0 <= normalizedFiniteCount t F x := by
  unfold normalizedFiniteCount
  positivity

theorem normalizedFiniteCount_mono
    (t : ℝ) (F : Finset Zeros) :
    Monotone (normalizedFiniteCount t F) := by
  intro x y hxy
  unfold normalizedFiniteCount
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  have hx := (Finset.mem_filter.mp hrho).2
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hrho).1, le_trans hx hxy⟩

theorem normalizedBaseAtomicAggregate_eq_countingPair
    (t : ℝ) (F : Finset Zeros) :
    normalizedBaseAtomicAggregate t F
      =
    normalizedFiniteCountingPair t F
      (normalizedCenteredBaseTransform t) := by
  rfl

theorem normalizedFiniteCountingPair_add
    (t : ℝ) (F : Finset Zeros) (phi psi : ℝ → ℝ) :
    normalizedFiniteCountingPair t F (fun q => phi q + psi q)
      =
    normalizedFiniteCountingPair t F phi
      + normalizedFiniteCountingPair t F psi := by
  unfold normalizedFiniteCountingPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

theorem normalizedFiniteCountingPair_sub
    (t : ℝ) (F : Finset Zeros) (phi psi : ℝ → ℝ) :
    normalizedFiniteCountingPair t F (fun q => phi q - psi q)
      =
    normalizedFiniteCountingPair t F phi
      - normalizedFiniteCountingPair t F psi := by
  unfold normalizedFiniteCountingPair
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

theorem normalizedFiniteCountingPair_const_mul
    (t : ℝ) (F : Finset Zeros) (c : ℝ) (phi : ℝ → ℝ) :
    normalizedFiniteCountingPair t F (fun q => c * phi q)
      =
    c * normalizedFiniteCountingPair t F phi := by
  unfold normalizedFiniteCountingPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

/--
Exact prize-facing finite aggregate decomposition with the base term written as
an actual normalized counting-functional pairing.
-/
theorem sum_literal_centered_pairs_eq_countingPair_plus_horizontal
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    (∑ rho ∈ F,
      (Zeta23Bridge.LiteralWeilParityBalance.zeroConeValue
          (Zeta23Bridge.LiteralWeilParityBalance.gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 rho
        +
       Zeta23Bridge.LiteralWeilParityBalance.zeroConeValue
          (Zeta23Bridge.LiteralWeilParityBalance.gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 (Zeta23.reflectZero rho)))
      =
    (1 / t) *
      (normalizedFiniteCountingPair t F
          (normalizedCenteredBaseTransform t)
        + normalizedHorizontalAtomicAggregate t F) := by
  rw [sum_literal_centered_pairs_eq_base_plus_horizontal ht F,
      normalizedBaseAtomicAggregate_eq_countingPair]

end Synthesis
