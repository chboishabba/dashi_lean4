import Synthesis.RiemannProjectiveQuarticOffInfiniteSplit
import Zeta23Bridge.FarShellCutoffTailBound

/-!
# Growing signed band for the quartic q-only base carrier

The normalized quartic witness has a fixed punctured negative base band

  0 < |q| < eps_B  ->  Phi_Q(q) < 0.

At physical radius r=t/16 this becomes

  0 < |Im sigma-t| < eps_B * t/16.

Thus the useful signed region grows linearly with the target ordinate.

For any natural cutoff J lying inside that band:
* every off-ordinate source with |Im sigma-t|<J contributes <=0;
* every source outside the cutoff is bounded absolutely by
  C_Q m_sigma/(Im sigma-t)^2.

Combining with the existing explicit far-shell bound gives a one-sided upper
bound on the entire quartic base tsum with no finite positive middle term.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.NearFarCarrierSplit
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.FarShellCutoffTailBound

structure QuarticBaseBand (W : QuarticHighWitness) where
  eps : ℝ
  epsPos : 0 < eps
  neg :
    ∀ q : ℝ, 0 < |q| -> |q| < eps ->
      genericProjectiveBaseKernel
        (quarticThreeWindowProfile W.R W.lam) 1 q < 0

theorem exists_quarticBaseBand
    (W : QuarticHighWitness) :
    ∃ B : QuarticBaseBand W, True := by
  obtain ⟨eps, heps, hneg⟩ :=
    exists_genericProjectiveBaseKernel_neg_punctured_of_quartic_escape
      (quarticThreeWindowProfile_continuous (lam:=W.lam) W.Rpos)
      (quarticThreeWindowProfile_compact (lam:=W.lam) W.Rpos)
      W.J2zero W.J4neg
  exact ⟨{
    eps := eps
    epsPos := heps
    neg := hneg
  }, trivial⟩

theorem QuarticBaseBand.source_nonpos_of_gap_lt
    {W : QuarticHighWitness}
    (B : QuarticBaseBand W)
    {t : ℝ} (ht : 0 < t)
    (sigma : Zeros)
    (hoff : (sigma : ℂ).im ≠ t)
    (hgap :
      |(sigma : ℂ).im-t| < B.eps * (t/16)) :
    quarticBaseSourceTerm W t sigma ≤ 0 := by
  let r := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdelta : (sigma : ℂ).im-t ≠ 0 :=
    sub_ne_zero.mpr hoff
  have hq0 :
      0 < |((sigma : ℂ).im-t)/r| := by
    rw [abs_pos]
    exact div_ne_zero hdelta hr.ne'
  have hqeps :
      |((sigma : ℂ).im-t)/r| < B.eps := by
    rw [abs_div, abs_of_pos hr, div_lt_iff₀ hr]
    simpa [r] using hgap
  have hneg := B.neg _ hq0 hqeps
  unfold quarticBaseSourceTerm
  dsimp [r]
  have hm : 0 ≤ ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by
    positivity
  have hr2 : 0 < (t/16)^2 := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hm hr2.le) hneg.le

def quarticBaseFarTerm
    (W : QuarticHighWitness) (t : ℝ) (J : ℕ)
    (sigma : Zeros) : ℝ :=
  if (J : ℝ) ≤ |(sigma : ℂ).im-t|
  then quarticBaseSourceTerm W t sigma
  else 0

theorem quarticBaseFarTerm_abs_le
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    {J : ℕ} (hJ : 1 ≤ J)
    (sigma : Zeros) :
    |quarticBaseFarTerm W t J sigma|
      ≤
    genericProjectiveBaseCurvature
        (quarticThreeWindowProfile W.R W.lam)
      * tailTermFrom t J sigma := by
  unfold quarticBaseFarTerm
  by_cases hfar : (J : ℝ) ≤ |(sigma : ℂ).im-t|
  · rw [if_pos hfar]
    have hJr : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    have hfar1 : 1 ≤ |(sigma : ℂ).im-t| := hJr.trans hfar
    have hbase :=
      quarticBaseSourceTerm_abs_le_tailTerm_of_far
        W ht sigma hfar1
    unfold tailTerm at hbase
    rw [if_pos hfar1] at hbase
    unfold tailTermFrom
    rw [if_pos hfar]
    exact hbase
  · rw [if_neg hfar]
    unfold tailTermFrom
    rw [if_neg hfar]
    simp

theorem quarticBaseFarTerm_summable
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    {J : ℕ} (hJ : 1 ≤ J) :
    Summable (quarticBaseFarTerm W t J) := by
  let C :=
    genericProjectiveBaseCurvature
      (quarticThreeWindowProfile W.R W.lam)
  have hmaj :
      Summable (fun sigma : Zeros => C * tailTermFrom t J sigma) :=
    (summable_tailTermFrom hJ t).mul_left C
  have hdom :
      ∀ sigma : Zeros,
        ‖quarticBaseFarTerm W t J sigma‖
          ≤ C * tailTermFrom t J sigma := by
    intro sigma
    rw [Real.norm_eq_abs]
    exact quarticBaseFarTerm_abs_le W ht hJ sigma
  exact Summable.of_norm_bounded hmaj hdom

/--
One-sided full-base compiler: a cutoff inside the negative quartic band removes
the whole finite near carrier from the positive budget.
-/
theorem quarticBaseTsum_le_far
    {W : QuarticHighWitness}
    (B : QuarticBaseBand W)
    {t : ℝ} (ht : 0 < t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJband : (J : ℝ) < B.eps * (t/16)) :
    (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
      ≤
    ∑' sigma : Zeros, quarticBaseFarTerm W t J sigma := by
  classical
  have hbase := quarticBaseSourceTerm_summable_full W ht
  have hfar := quarticBaseFarTerm_summable W ht hJ

  let near : Finset Zeros := nearFinset t J
  have hsplit := hbase.sum_add_tsum_compl (s:=near)

  have hnear_nonpos :
      (∑ sigma ∈ near, quarticBaseSourceTerm W t sigma) ≤ 0 := by
    apply Finset.sum_nonpos
    intro sigma hsigma
    have hgap :
        |(sigma : ℂ).im-t| < (J : ℝ) :=
      (mem_nearFinset_iff t J sigma).mp hsigma
    by_cases him : (sigma : ℂ).im = t
    · rw [quarticBaseSourceTerm_eq_zero_of_sameOrd W ht him]
    · exact B.source_nonpos_of_gap_lt
        ht sigma him (hgap.trans hJband)

  have hcompl :
      (∑' sigma : ((↑near : Set Zeros)ᶜ : Set Zeros),
        quarticBaseSourceTerm W t (sigma : Zeros))
        =
      ∑' sigma : Zeros, quarticBaseFarTerm W t J sigma := by
    have hsubbase := hbase.subtype ((↑near : Set Zeros)ᶜ)
    have hsubfar := hfar
    calc
      (∑' sigma : ((↑near : Set Zeros)ᶜ : Set Zeros),
        quarticBaseSourceTerm W t (sigma : Zeros))
        =
      ∑' sigma : ((↑near : Set Zeros)ᶜ : Set Zeros),
        quarticBaseFarTerm W t J (sigma : Zeros) := by
          apply tsum_congr
          intro sigma
          unfold quarticBaseFarTerm
          have hnot : (sigma : Zeros) ∉ near := by
            simpa using sigma.property
          have hge : (J : ℝ) ≤ |((sigma : Zeros) : ℂ).im-t| := by
            by_contra hlt
            exact hnot ((mem_nearFinset_iff t J _).2 (not_le.1 hlt))
          rw [if_pos hge]
      _ =
      ∑' sigma : Zeros, quarticBaseFarTerm W t J sigma := by
          have hzero :
              ∀ sigma ∈ near,
                quarticBaseFarTerm W t J sigma = 0 := by
            intro sigma hs
            unfold quarticBaseFarTerm
            have hlt := (mem_nearFinset_iff t J sigma).mp hs
            rw [if_neg (not_le.mpr hlt)]
          have hsumfar := hfar
          have hdecomp := hsumfar.sum_add_tsum_compl (s:=near)
          have hfinzero :
              (∑ sigma ∈ near,
                quarticBaseFarTerm W t J sigma) = 0 :=
            Finset.sum_eq_zero (fun sigma hs => hzero sigma hs)
          rw [hfinzero, zero_add] at hdecomp
          exact hdecomp.symm

  rw [← hsplit]
  rw [hcompl]
  linarith

theorem exists_quarticBaseTsum_farShell_upper
    {W : QuarticHighWitness}
    (B : QuarticBaseBand W)
    {t : ℝ} (ht : 0 < t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJband : (J : ℝ) < B.eps * (t/16)) :
    ∃ A : ℝ, 1 ≤ A ∧
      (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
        ≤
      genericProjectiveBaseCurvature
          (quarticThreeWindowProfile W.R W.lam)
        * farShellBound A |t| J := by
  obtain ⟨A, hA, hfar⟩ := exists_uniform_farShellBound
  refine ⟨A, hA, ?_⟩
  have hbase := quarticBaseTsum_le_far B ht hJ hJband
  have C0 :
      0 ≤ genericProjectiveBaseCurvature
          (quarticThreeWindowProfile W.R W.lam) :=
    genericProjectiveBaseCurvature_nonneg _
  have habs :
      (∑' sigma : Zeros, quarticBaseFarTerm W t J sigma)
        ≤
      ∑' sigma : Zeros, |quarticBaseFarTerm W t J sigma| := by
    have hsum := quarticBaseFarTerm_summable W ht hJ
    exact le_trans (le_abs_self _) (by
      have habsSum :
          |∑' sigma : Zeros, quarticBaseFarTerm W t J sigma|
            ≤ ∑' sigma : Zeros, |quarticBaseFarTerm W t J sigma| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm
            (f:=quarticBaseFarTerm W t J)
            (by simpa [Real.norm_eq_abs] using hsum.abs)
      exact habsSum)
  have hdom :
      ∑' sigma : Zeros, |quarticBaseFarTerm W t J sigma|
        ≤
      genericProjectiveBaseCurvature
          (quarticThreeWindowProfile W.R W.lam)
        * ∑' sigma : Zeros, tailTermFrom t J sigma := by
    have hfabs :
        Summable (fun sigma : Zeros =>
          |quarticBaseFarTerm W t J sigma|) :=
      (quarticBaseFarTerm_summable W ht hJ).abs
    have hmaj :
        Summable (fun sigma : Zeros =>
          genericProjectiveBaseCurvature
              (quarticThreeWindowProfile W.R W.lam)
            * tailTermFrom t J sigma) :=
      (summable_tailTermFrom hJ t).mul_left _
    calc
      ∑' sigma : Zeros, |quarticBaseFarTerm W t J sigma|
        ≤ ∑' sigma : Zeros,
            genericProjectiveBaseCurvature
                (quarticThreeWindowProfile W.R W.lam)
              * tailTermFrom t J sigma :=
        hfabs.tsum_le_tsum
          (fun sigma => quarticBaseFarTerm_abs_le W ht hJ sigma)
          hmaj
      _ =
        genericProjectiveBaseCurvature
            (quarticThreeWindowProfile W.R W.lam)
          * ∑' sigma : Zeros, tailTermFrom t J sigma := by
        rw [tsum_mul_left]
  have htail := hfar t J hJ
  calc
    (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
      ≤ ∑' sigma : Zeros, quarticBaseFarTerm W t J sigma := hbase
    _ ≤ ∑' sigma : Zeros, |quarticBaseFarTerm W t J sigma| := habs
    _ ≤ genericProjectiveBaseCurvature
          (quarticThreeWindowProfile W.R W.lam)
        * ∑' sigma : Zeros, tailTermFrom t J sigma := hdom
    _ ≤ genericProjectiveBaseCurvature
          (quarticThreeWindowProfile W.R W.lam)
        * farShellBound A |t| J :=
      mul_le_mul_of_nonneg_left htail C0

end Synthesis
