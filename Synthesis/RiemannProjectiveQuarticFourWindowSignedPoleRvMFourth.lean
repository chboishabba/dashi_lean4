import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth
import Synthesis.RiemannZetaMuExactAbel
import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy

/-!
# Quartic signed-pole V4: literal local RvM/Abel specialization

This file implements the vertical half of the post-bidi RH recut.

The current marked fourth-angular obstruction has already been split exactly as

  A4_local = V4 + H4,

where V4 is the ordinary ordinate-only fourth moment discrepancy and H4 is the
genuinely off-line horizontal correction.

There is no need for a new 0/2/4 Montgomery producer to control V4.  The repo
already owns the exact same-object Abel identity

  Z_phi(A,B) - integral_A^B phi mu
    = phi(B) D_A(B) - integral_A^B phi'(x) D_A(x) dx,

with D_A(x)=N(A,x)-integral_A^x mu, together with an unconditional
arbitrary-endpoint O(log A + log B) bound for D_A.

Here we specialize that machinery to

  phi_t(x)=(x-t)^4,    phi_t'(x)=4(x-t)^3

on the symmetric literal window (t-r,t+r].  The resulting generic compiler is

  |V4(t,r)| <= 9 r^4 E

whenever the cumulative discrepancy is bounded by E throughout the window.
The final theorem instantiates E from the existing arbitrary-endpoint RvM
producer.

This is deliberately a literal N-mu theorem.  It does not identify the
auxiliary positive prime jet with the actual short-support witness prime
channel; the firewall in the bidi marked owner remains intact.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

def quarticSignedPoleVerticalFourthWeight
    (t x : ℝ) : ℝ :=
  (x - t)^4

def quarticSignedPoleVerticalFourthWeightDeriv
    (t x : ℝ) : ℝ :=
  4 * (x - t)^3

def quarticSignedPoleRvMVerticalFourthDiscrepancy
    (t r : ℝ) : ℝ :=
  zetaWindowMinusMuPair
    (t-r) (t+r)
    (quarticSignedPoleVerticalFourthWeight t)

theorem quarticSignedPoleVerticalFourthWeight_hasDerivAt
    (t x : ℝ) :
    HasDerivAt
      (quarticSignedPoleVerticalFourthWeight t)
      (quarticSignedPoleVerticalFourthWeightDeriv t x)
      x := by
  unfold quarticSignedPoleVerticalFourthWeight
    quarticSignedPoleVerticalFourthWeightDeriv
  simpa [mul_assoc] using
    (((hasDerivAt_id x).sub_const t).pow 4)

theorem quarticSignedPoleVerticalFourthWeightDeriv_intervalIntegrable
    (t A B : ℝ) :
    IntervalIntegrable
      (quarticSignedPoleVerticalFourthWeightDeriv t)
      volume A B := by
  have hcont :
      Continuous (quarticSignedPoleVerticalFourthWeightDeriv t) := by
    unfold quarticSignedPoleVerticalFourthWeightDeriv
    fun_prop
  exact hcont.intervalIntegrable A B

/--
Exact quartic specialization of the literal N-mu Abel identity.
-/
theorem quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_abel
    {t r : ℝ}
    (hr : 0 <= r) :
    quarticSignedPoleRvMVerticalFourthDiscrepancy t r
      =
    r^4 * zetaMuCumulativeDiscrepancy (t-r) (t+r)
      -
    ∫ x in (t-r)..(t+r),
      quarticSignedPoleVerticalFourthWeightDeriv t x
        * zetaMuCumulativeDiscrepancy (t-r) x := by
  have hAB : t-r <= t+r := by linarith
  have h :=
    zetaWindowMinusMuPair_eq_discrepancyAbel
      (A := t-r) (B := t+r)
      (phi := quarticSignedPoleVerticalFourthWeight t)
      (phi' := quarticSignedPoleVerticalFourthWeightDeriv t)
      hAB
      (by
        intro x hx
        exact quarticSignedPoleVerticalFourthWeight_hasDerivAt t x)
      (quarticSignedPoleVerticalFourthWeightDeriv_intervalIntegrable
        t (t-r) (t+r))
  unfold quarticSignedPoleRvMVerticalFourthDiscrepancy
  simpa [quarticSignedPoleVerticalFourthWeight] using h

/--
Abstract quantitative V4 compiler.

If the cumulative literal N-mu discrepancy from the left endpoint is at most E
at every point of the symmetric window, then the quartic moment discrepancy is
at most 9 r^4 E.
-/
theorem quarticSignedPoleRvMVerticalFourthDiscrepancy_abs_le_of_cumulative_bound
    {t r E : ℝ}
    (hr : 0 <= r)
    (hE : 0 <= E)
    (hD :
      ∀ x ∈ Set.Icc (t-r) (t+r),
        |zetaMuCumulativeDiscrepancy (t-r) x| <= E) :
    |quarticSignedPoleRvMVerticalFourthDiscrepancy t r|
      <= 9 * r^4 * E := by
  have hAB : t-r <= t+r := by linarith
  have hDB :
      |zetaMuCumulativeDiscrepancy (t-r) (t+r)| <= E :=
    hD (t+r) ⟨hAB, le_rfl⟩

  have hpoint :
      ∀ x ∈ Set.uIoc (t-r) (t+r),
        |
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-r) x
        |
          <= 4 * r^3 * E := by
    intro x hx
    rw [Set.uIoc_of_le hAB] at hx
    have hxIcc : x ∈ Set.Icc (t-r) (t+r) :=
      ⟨hx.1.le, hx.2⟩
    have hxabs : |x-t| <= r := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hxcube : |x-t|^3 <= r^3 := by
      gcongr
    have hDx := hD x hxIcc
    unfold quarticSignedPoleVerticalFourthWeightDeriv
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= 4),
        abs_pow]
    have hr3 : 0 <= r^3 := by positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hxcube (by norm_num))
      hDx
      (abs_nonneg _)
      (mul_nonneg (by positivity) hr3)

  have hIntRaw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x =>
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-r) x)
      hpoint
  rw [Real.norm_eq_abs] at hIntRaw

  have hfirst :
      |r^4 * zetaMuCumulativeDiscrepancy (t-r) (t+r)|
        <= r^4 * E := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= r^4)]
    exact mul_le_mul_of_nonneg_left hDB (by positivity)

  rw [quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_abel hr]
  calc
    |r^4 * zetaMuCumulativeDiscrepancy (t-r) (t+r)
      -
      ∫ x in (t-r)..(t+r),
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-r) x|
      <=
    |r^4 * zetaMuCumulativeDiscrepancy (t-r) (t+r)|
      +
    |∫ x in (t-r)..(t+r),
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-r) x| := abs_sub _ _
    _ <=
      r^4 * E
        + (4 * r^3 * E) * |(t+r) - (t-r)| := by
          exact add_le_add hfirst hIntRaw
    _ = 9 * r^4 * E := by
      rw [show (t+r) - (t-r) = 2*r by ring,
          abs_of_nonneg (by linarith : 0 <= 2*r)]
      ring

/--
The arbitrary-endpoint RvM theorem supplies the cumulative hypothesis needed
by the quartic V4 compiler.

The local half-width r is assumed positive and the left endpoint must lie
above the existing arbitrary-endpoint threshold.
-/
theorem exists_quarticSignedPoleRvMVerticalFourthDiscrepancy_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t r : ℝ,
        0 < r ->
        max T0 4 <= t-r ->
        |quarticSignedPoleRvMVerticalFourthDiscrepancy t r|
          <=
        9 * r^4 *
          (C *
            (Real.log ((t-r) + 3)
              + Real.log ((t+r) + 4))) := by
  obtain ⟨C,T0,hC,hRvM⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C,T0,hC,?_⟩
  intro t r hr hleft
  let A : ℝ := t-r
  let B : ℝ := t+r
  let E : ℝ :=
    C * (Real.log (A+3) + Real.log (B+4))

  have hAB : A < B := by
    dsimp [A,B]
    linarith
  have hA4 : 4 <= A :=
    (le_max_right T0 4).trans hleft
  have hE : 0 <= E := by
    dsimp [E]
    have hlogA : 0 <= Real.log (A+3) :=
      Real.log_nonneg (by linarith)
    have hlogB : 0 <= Real.log (B+4) :=
      Real.log_nonneg (by linarith)
    exact mul_nonneg hC (add_nonneg hlogA hlogB)

  have hD :
      ∀ x ∈ Set.Icc A B,
        |zetaMuCumulativeDiscrepancy A x| <= E := by
    intro x hx
    by_cases hxA : x = A
    · subst x
      simp [zetaMuCumulativeDiscrepancy, zetaMuPrimitive]
    · have hAx : A < x := lt_of_le_of_ne hx.1 hxA.symm
      have hraw := hRvM A x hleft hAx
      rw [zetaMuCumulativeDiscrepancy_endpoint]
      have hlog :
          Real.log (x+4) <= Real.log (B+4) :=
        Real.log_le_log (by linarith [hA4,hAx]) (by linarith [hx.2])
      have hscaled :
          C * Real.log (x+4) <= C * Real.log (B+4) :=
        mul_le_mul_of_nonneg_left hlog hC
      exact hraw.trans (by
        dsimp [E]
        linarith)

  have hbound :=
    quarticSignedPoleRvMVerticalFourthDiscrepancy_abs_le_of_cumulative_bound
      (t:=t) (r:=r) (E:=E) hr.le hE
      (by
        intro x hx
        simpa [A,B] using hD x hx)
  simpa [A,B,E] using hbound

end Synthesis
