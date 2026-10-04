import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseWindowWeld
import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Quantitative RvM bound for the transformed finite adverse pair core

The strict transformed adverse core is already bounded by the literal weighted
zero window for the nonnegative physical adverse test `phi`.  The AC Abel weld
writes that window as

  integral phi*mu + phi(B) D_A(B) - integral phi' D_A.

If `|D_A(x)| <= E` throughout `[A,B]=[t-R,t+R]`, and `Lphys` is the exact
Lipschitz mass of phi, then

  NearAdverse <= integral phi*mu + E*phi(B) + 2 R E Lphys.

The final theorem instantiates E from the existing unconditional arbitrary-
endpoint RvM producer.  No estimate of the smooth mu main term is hidden here;
it remains explicit and source-native.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Smooth theorem-bearing RvM density contribution of the physical adverse
test on the finite symmetric window. -/
def QuarticFourSignedPolePair.threeTapAdverseMuMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A R : ℝ) : ℝ :=
  ∫ x in (t-R)..(t+R),
    W.threeTapAdversePhysicalOrdinateTest eps A x * Zeta23.mu x

/-- Generic discrepancy compiler. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_of_cumulativeDiscrepancy
    {t eps A R E : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hR : 0 <= R)
    (hE : 0 <= E)
    (hstrip : W.ThreeTapAlphaStripBound A)
    (hD :
      ∀ x ∈ Set.Icc (t-R) (t+R),
        |zetaMuCumulativeDiscrepancy (t-R) x| <= E) :
    W.threeTapPairAdverseNearAt eps R
      <=
    W.threeTapAdverseMuMass eps A R
      + E * W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
      + (2*R) * E * W.threeTapAdversePhysicalLipschitzMass eps A := by
  have hbase :=
    W.threeTapPairAdverseNearAt_le_mu_add_discrepancyAbel
      ht hA hR hstrip
  have hAB : t-R <= t+R := by linarith
  have hDB :
      |zetaMuCumulativeDiscrepancy (t-R) (t+R)| <= E :=
    hD (t+R) ⟨hAB, le_rfl⟩
  have hphiB :
      0 <= W.threeTapAdversePhysicalOrdinateTest eps A (t+R) :=
    W.threeTapAdversePhysicalOrdinateTest_nonneg (by linarith : 0 < t)
  have hboundary :
      W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
          * zetaMuCumulativeDiscrepancy (t-R) (t+R)
      <=
      E * W.threeTapAdversePhysicalOrdinateTest eps A (t+R) := by
    have hDle : zetaMuCumulativeDiscrepancy (t-R) (t+R) <= E :=
      (le_abs_self _).trans hDB
    calc
      W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
          * zetaMuCumulativeDiscrepancy (t-R) (t+R)
        <= W.threeTapAdversePhysicalOrdinateTest eps A (t+R) * E :=
          mul_le_mul_of_nonneg_left hDle hphiB
      _ = E * W.threeTapAdversePhysicalOrdinateTest eps A (t+R) := by ring
  let phi : ℝ → ℝ := W.threeTapAdversePhysicalOrdinateTest eps A
  let L : ℝ := W.threeTapAdversePhysicalLipschitzMass eps A
  have hL : 0 <= L := by
    dsimp [L]
    exact W.threeTapAdversePhysicalLipschitzMass_nonneg (by linarith : 0 < t)
  have hderiv : ∀ x : ℝ, |deriv phi x| <= L := by
    intro x
    have hlip := W.threeTapAdversePhysicalOrdinateTest_lipschitz
      (by linarith : 0 < t) (eps:=eps) (A:=A)
    have hn := norm_deriv_le_of_lipschitz (x₀:=x) hlip
    simpa [phi, L, Real.norm_eq_abs] using hn
  have hpoint :
      ∀ x ∈ Set.uIoc (t-R) (t+R),
        |deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x|
          <= L * E := by
    intro x hx
    rw [Set.uIoc_of_le hAB] at hx
    have hxIcc : x ∈ Set.Icc (t-R) (t+R) := ⟨hx.1.le, hx.2⟩
    rw [abs_mul]
    exact mul_le_mul (hderiv x) (hD x hxIcc)
      (abs_nonneg _) hL
  have hintRaw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x)
      hpoint
  rw [Real.norm_eq_abs] at hintRaw
  have hlength : |(t+R)-(t-R)| = 2*R := by
    rw [show (t+R)-(t-R)=2*R by ring, abs_of_nonneg (by linarith)]
  rw [hlength] at hintRaw
  have hminus :
      - ∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x
      <= (2*R) * E * L := by
    have habsLe :
        |∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x|
        <= L * E * (2*R) := hintRaw
    have hnegLe :
        - ∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x
        <= |∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x| :=
      neg_le_abs _
    calc
      - ∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x
        <= |∫ x in (t-R)..(t+R),
          deriv phi x * zetaMuCumulativeDiscrepancy (t-R) x| := hnegLe
      _ <= L * E * (2*R) := habsLe
      _ = (2*R) * E * L := by ring
  unfold QuarticFourSignedPolePair.threeTapAdverseMuMass
  dsimp [phi, L] at hminus
  linarith

/-- The existing arbitrary-endpoint RvM theorem supplies the discrepancy
hypothesis uniformly on the finite adverse window. -/
theorem QuarticFourSignedPolePair.exists_threeTapPairAdverseNearAt_rvm_bound :
    ∃ C : ℝ, 0 <= C ∧
      ∀ {t eps A R : ℝ},
        200 <= t ->
        0 <= A ->
        0 < R ->
        5 <= t-R ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapAlphaStripBound A ->
        W.threeTapPairAdverseNearAt eps R
          <=
        W.threeTapAdverseMuMass eps A R
          +
        (C * (Real.log ((t-R)+3) + Real.log ((t+R)+4)))
          * W.threeTapAdversePhysicalOrdinateTest eps A (t+R)
          +
        (2*R)
          * (C * (Real.log ((t-R)+3) + Real.log ((t+R)+4)))
          * W.threeTapAdversePhysicalLipschitzMass eps A := by
  obtain ⟨C,hC,hRvM⟩ := exists_zetaMuWindowDiscrepancy_arbitrary_bound_at_five
  refine ⟨C,hC,?_⟩
  intro t eps A R ht hA hR hleft W hstrip
  let E : ℝ :=
    C * (Real.log ((t-R)+3) + Real.log ((t+R)+4))
  have hE : 0 <= E := by
    have hlogL : 0 <= Real.log ((t-R)+3) :=
      Real.log_nonneg (by linarith)
    have hlogR : 0 <= Real.log ((t+R)+4) :=
      Real.log_nonneg (by linarith)
    exact mul_nonneg hC (add_nonneg hlogL hlogR)
  have hD :
      ∀ x ∈ Set.Icc (t-R) (t+R),
        |zetaMuCumulativeDiscrepancy (t-R) x| <= E := by
    intro x hx
    by_cases hxL : x = t-R
    · subst x
      have hN : Ncount (t-R) (t-R) = 0 := by
        simp [Ncount, zerosIn]
      simpa [zetaMuCumulativeDiscrepancy, zetaMuPrimitive, hN] using hE
    · have hLx : t-R < x := lt_of_le_of_ne hx.1 hxL.symm
      have hraw := hRvM (t-R) x hleft hLx
      rw [zetaMuCumulativeDiscrepancy_endpoint]
      have hlog : Real.log (x+4) <= Real.log ((t+R)+4) :=
        Real.log_le_log (by linarith) (by linarith [hx.2])
      have hscaled := mul_le_mul_of_nonneg_left hlog hC
      exact hraw.trans (by
        dsimp [E]
        linarith)
  have hbound := W.threeTapPairAdverseNearAt_le_of_cumulativeDiscrepancy
    ht hA hR.le hE hstrip hD
  simpa [E] using hbound

end Synthesis
