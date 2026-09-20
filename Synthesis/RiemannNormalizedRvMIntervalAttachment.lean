import Synthesis.RiemannZeta23RvMTwoSidedDiscrepancy
import Synthesis.RiemannNormalizedCountingAbelCompiler

/-!
# Normalized q-interval attachment of the literal Zeta23 RvM discrepancy

The normalized RH spectral coordinate is

  gamma = t * (1 + q).

This file does not invent a new counting measure.  It defines the q-window count
by literally evaluating Zeta23.Ncount at those two ordinate endpoints and then
specializes the already-proved arbitrary-interval RvM discrepancy theorem.

Positive q-windows (q > -1) use the positive-height theorem directly.
Negative q-windows (q < -1) use the conjugation/even-mu transport.

Thus the remaining Abel-grid work is finite indexing/telescoping, not a
same-object or number-theoretic source-acquisition problem.
-/

noncomputable section

open Complex MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

def normalizedOrdinate (t q : ℝ) : ℝ :=
  t * (1 + q)

def normalizedZetaWindowCount
    (t q1 q2 : ℝ) : ℝ :=
  (Ncount (normalizedOrdinate t q1)
    (normalizedOrdinate t q2) : ℝ)

def normalizedMuWindow
    (t q1 q2 : ℝ) : ℝ :=
  ∫ gamma in (normalizedOrdinate t q1)..(normalizedOrdinate t q2),
    mu gamma

def normalizedRvMWindowDiscrepancy
    (t q1 q2 : ℝ) : ℝ :=
  normalizedZetaWindowCount t q1 q2
    - normalizedMuWindow t q1 q2

theorem normalizedOrdinate_strictMono
    {t : ℝ} (ht : 0 < t) :
    StrictMono (normalizedOrdinate t) := by
  intro q1 q2 hq
  unfold normalizedOrdinate
  nlinarith

theorem normalizedRvM_positive_q_interval_quantitative :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t q1 q2 : ℝ,
        0 < t ->
        q1 < q2 ->
        0 < normalizedOrdinate t q1 ->
        max T0 3 <= normalizedOrdinate t q1 ->
        GoodHeight (normalizedOrdinate t q1) ->
        GoodHeight (normalizedOrdinate t q2) ->
        |normalizedRvMWindowDiscrepancy t q1 q2|
          <=
        (C * Real.log (normalizedOrdinate t q1)
          + Real.pi
          + C * Real.log (normalizedOrdinate t q2)) / Real.pi := by
  obtain ⟨C, T0, hC, hRvM⟩ :=
    literal_zeta_interval_discrepancy_quantitative
  refine ⟨C, T0, hC, ?_⟩
  intro t q1 q2 ht hq hpos hlarge hg1 hg2
  unfold normalizedRvMWindowDiscrepancy
    normalizedZetaWindowCount normalizedMuWindow
  exact hRvM
    (normalizedOrdinate t q1)
    (normalizedOrdinate t q2)
    hlarge
    (normalizedOrdinate_strictMono ht hq)
    hg1 hg2

/--
Negative q-window version.  If both ordinates are negative, reflect the window
to positive magnitudes before applying the same theorem-bearing discrepancy.
-/
theorem normalizedRvM_negative_q_interval_quantitative :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t q1 q2 : ℝ,
        0 < t ->
        q1 < q2 ->
        normalizedOrdinate t q2 < 0 ->
        max T0 3 <= - normalizedOrdinate t q2 ->
        GoodHeight (- normalizedOrdinate t q2) ->
        GoodHeight (- normalizedOrdinate t q1) ->
        |normalizedRvMWindowDiscrepancy t q1 q2|
          <=
        (C * Real.log (- normalizedOrdinate t q2)
          + Real.pi
          + C * Real.log (- normalizedOrdinate t q1)) / Real.pi := by
  obtain ⟨C, T0, hC, hRvM⟩ :=
    literal_zeta_negative_interval_discrepancy_quantitative
  refine ⟨C, T0, hC, ?_⟩
  intro t q1 q2 ht hq hneg hlarge hg2 hg1
  have hord :
      normalizedOrdinate t q1
        < normalizedOrdinate t q2 :=
    normalizedOrdinate_strictMono ht hq
  have hT :
      - normalizedOrdinate t q2
        < - normalizedOrdinate t q1 := by
    linarith
  unfold normalizedRvMWindowDiscrepancy
    normalizedZetaWindowCount normalizedMuWindow
  have h :=
    hRvM
      (- normalizedOrdinate t q2)
      (- normalizedOrdinate t q1)
      hlarge hT hg2 hg1
  simpa only [neg_neg] using h

end Synthesis
