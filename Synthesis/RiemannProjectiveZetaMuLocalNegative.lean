import Synthesis.RiemannNormalizedProjectiveBaseLocalSign
import Synthesis.RiemannProjectiveZetaMuContinuousAbel
import Synthesis.RiemannZetaCountingStieltjesRightContinuous
import Synthesis.RiemannRvMMuHighPositive

/-!
# Strict local negativity of the literal projective N-mu residual

For every high target ordinate t >= 18:

* local finiteness of the literal Zeta23 zero carrier gives a right interval
  (t,t+delta] containing no zero ordinate;
* the canonical q-only projective kernel is strictly positive for sufficiently
  small q=(x-t)/t>0;
* the exact theorem-bearing RvM density mu(x) is strictly positive for x>=t.

Shrinking to the intersection of the first two intervals therefore gives

  zero-pair - integral phi_t(x) mu(x) dx
    = - integral phi_t(x) mu(x) dx
    < 0.

This is the first genuinely signed Route-A theorem.  It is not a rearrangement
of the completed explicit formula and it uses the actual zero carrier and the
actual Zeta23 mu density.

It is local: the remaining global problem is to control what happens after the
next zero ordinate and across later gaps.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

/--
Every high target ordinate has a literal right window on which the exact
projective N-mu residual is strictly negative.
-/
theorem exists_projectiveZetaMuWindowResidual_neg_right
    {t : ℝ} (ht : 18 <= t) :
    ∃ B : ℝ, t < B ∧
      zetaZeroConfig.window t B = ∅ ∧
      projectiveZetaMuWindowResidual t t B < 0 := by
  have htpos : 0 < t := by linarith
  obtain ⟨epsZero, hZeroPos, hZeroOne, hzero⟩ :=
    exists_right_zero_free_literal_window t
  obtain ⟨epsPhi, hPhiPos, hphi⟩ :=
    exists_normalizedProjectiveBaseTransform_pos_right ht

  let delta : ℝ := min epsZero (t * epsPhi) / 2
  let B : ℝ := t + delta

  have htPhi : 0 < t * epsPhi := mul_pos htpos hPhiPos
  have hminPos : 0 < min epsZero (t * epsPhi) :=
    lt_min hZeroPos htPhi
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    linarith
  have hdeltaZero : delta < epsZero := by
    dsimp [delta]
    have hle := min_le_left epsZero (t * epsPhi)
    linarith
  have hdeltaPhi : delta < t * epsPhi := by
    dsimp [delta]
    have hle := min_le_right epsZero (t * epsPhi)
    linarith
  have htB : t < B := by
    dsimp [B]
    linarith

  have hwin : zetaZeroConfig.window t B = ∅ := by
    apply hzero B htB
    dsimp [B]
    linarith

  have hphiCont : Continuous (normalizedProjectiveOrdinateTest t) := by
    exact continuous_of_forall_continuousAt fun x =>
      (normalizedProjectiveOrdinateTest_hasDerivAt
        (t := t) (gamma := x) htpos.ne').continuousAt
  have hmuCont : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  have hint :
      IntervalIntegrable
        (fun x => normalizedProjectiveOrdinateTest t x * Zeta23.mu x)
        volume t B := by
    exact (hphiCont.mul hmuCont).intervalIntegrable t B

  have hintegralPos :
      0 <
      ∫ x in t..B,
        normalizedProjectiveOrdinateTest t x * Zeta23.mu x := by
    apply intervalIntegral_pos_of_pos_on hint
    · intro x hx
      have htx : t < x := hx.1
      have hxB : x < B := hx.2
      have hqpos : 0 < (x - t) / t := by
        positivity
      have hxdiff : x - t < delta := by
        dsimp [B] at hxB
        linarith
      have hqPhi : (x - t) / t < epsPhi := by
        rw [div_lt_iff₀ htpos]
        exact hxdiff.trans hdeltaPhi
      have htest :
          0 < normalizedProjectiveOrdinateTest t x := by
        unfold normalizedProjectiveOrdinateTest
        exact hphi ((x - t) / t) hqpos hqPhi
      have hmu : 0 < Zeta23.mu x :=
        zetaMu_pos_of_high_right ht htx.le
      exact mul_pos htest hmu
    · exact htB

  refine ⟨B, htB, hwin, ?_⟩
  unfold projectiveZetaMuWindowResidual zetaWindowMinusMuPair
  rw [zetaWindowWeightedPair_eq_zero_of_window_eq_empty hwin]
  linarith

end Synthesis
