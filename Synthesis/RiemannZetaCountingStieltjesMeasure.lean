import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Literal Zeta23 counting measure as a Stieltjes measure

The cumulative zero count is taken on the exact Zeta23 carrier:

  C_A(x) = N(A, max A x).

It is monotone, hence Mathlib canonically gives its right-regularization as a
`StieltjesFunction` and therefore a genuine Borel measure.  At every endpoint
where the literal cumulative count is right-continuous, the Stieltjes function
agrees with the literal Ncount and its Ioc mass is exactly the corresponding
zero-count increment.

The only remaining representation lemma in this layer is therefore concrete:
prove right continuity of C_A from Zeta23's local finiteness of zero windows.
No quadrature or new counting surrogate is introduced.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23

def zetaCumulativeCountFrom (A x : ℝ) : ℝ :=
  (Ncount A (max A x) : ℝ)

theorem zetaCumulativeCountFrom_mono (A : ℝ) :
    Monotone (zetaCumulativeCountFrom A) := by
  intro x y hxy
  unfold zetaCumulativeCountFrom
  have hmax : max A x <= max A y :=
    max_le_max le_rfl hxy
  have hN :
      Ncount A (max A x) <= Ncount A (max A y) :=
    Ncount_mono le_rfl hmax
  exact_mod_cast hN

def zetaCountingStieltjesFrom (A : ℝ) :
    StieltjesFunction ℝ :=
  (zetaCumulativeCountFrom_mono A).stieltjesFunction

def zetaCountingMeasureFrom (A : ℝ) : Measure ℝ :=
  (zetaCountingStieltjesFrom A).measure

theorem zetaCountingStieltjesFrom_apply_eq_rightLim
    (A x : ℝ) :
    zetaCountingStieltjesFrom A x
      = Function.rightLim (zetaCumulativeCountFrom A) x := by
  rfl

/--
At a literal right-continuity point, the canonical Stieltjes regularization is
definitionally the original Zeta23 cumulative count.
-/
theorem zetaCountingStieltjesFrom_apply_of_rightContinuous
    {A x : ℝ}
    (hcont :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ici x) x) :
    zetaCountingStieltjesFrom A x
      = zetaCumulativeCountFrom A x := by
  rw [zetaCountingStieltjesFrom_apply_eq_rightLim]
  have hcont' :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ioi x) x :=
    hcont.mono Set.Ioi_subset_Ici_self
  exact
    ((zetaCumulativeCountFrom_mono A)
      .continuousWithinAt_Ioi_iff_rightLim_eq).1 hcont'

/--
Exact Ioc mass at two literal right-continuity endpoints.
-/
theorem zetaCountingMeasureFrom_Ioc_of_rightContinuous
    {A a b : ℝ}
    (ha :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ici a) a)
    (hb :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ici b) b) :
    zetaCountingMeasureFrom A (Set.Ioc a b)
      =
    ENNReal.ofReal
      (zetaCumulativeCountFrom A b - zetaCumulativeCountFrom A a) := by
  unfold zetaCountingMeasureFrom
  rw [StieltjesFunction.measure_Ioc]
  rw [zetaCountingStieltjesFrom_apply_of_rightContinuous ha,
      zetaCountingStieltjesFrom_apply_of_rightContinuous hb]

/--
Above the base point A, the cumulative difference is exactly the literal
Zeta23 interval count once additivity is supplied by Ncount.
-/
theorem zetaCumulativeCountFrom_sub
    {A a b : ℝ}
    (hAa : A <= a)
    (hab : a <= b) :
    zetaCumulativeCountFrom A b - zetaCumulativeCountFrom A a
      =
    (Ncount a b : ℝ) := by
  unfold zetaCumulativeCountFrom
  rw [max_eq_right hAa, max_eq_right (hAa.trans hab)]
  have hadd := Ncount_add (a := A) (b := a) (c := b) hAa hab
  exact_mod_cast by
    omega

/--
Consequently the Stieltjes zero measure has exactly the literal Ncount mass on
Ioc(a,b), conditional only on the now-isolated right-continuity lemma.
-/
theorem zetaCountingMeasureFrom_Ioc_eq_Ncount
    {A a b : ℝ}
    (hAa : A <= a)
    (hab : a <= b)
    (ha :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ici a) a)
    (hb :
      ContinuousWithinAt
        (zetaCumulativeCountFrom A) (Set.Ici b) b) :
    zetaCountingMeasureFrom A (Set.Ioc a b)
      =
    ENNReal.ofReal (Ncount a b : ℝ) := by
  rw [zetaCountingMeasureFrom_Ioc_of_rightContinuous ha hb,
      zetaCumulativeCountFrom_sub hAa hab]

end Synthesis
