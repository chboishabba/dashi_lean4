import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleAbel

/-!
# Cone / good / far cut for the literal quartic signed-pole G3 source

The joint quartic polynomial is only a local Taylor carrier.  This module does
not expand the far zero source.  Instead it installs the Clay-facing three-way
cut

  cone : |q| <= eta and delta^2 <= 6 a^2
  good : |q| <= eta and 6 a^2 < delta^2
  far  : eta < |q|,

where q=(gamma-t)/(t/16), a=beta-1/2, delta=gamma-t.

The exact literal source is retained on every lane.  The quartic polynomial is
used only to classify the local cone/good geometry.

The scalar literalConeDebtAt is deliberately finite-windowed: it is the
positive part of the exact literal source on the cone inside the already-paid
cofinal centeredZeroFinset.  No global summability of a Taylor polynomial or
of a separated jet remainder is assumed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def quarticSignedPoleNormalizedOrdinateOffset
    (t : ℝ) (rho : Zeros) : ℝ :=
  ((rho : ℂ).im - t) / (t/16)

def quarticSignedPoleLocalCone
    (t eta : ℝ) (rho : Zeros) : Prop :=
  |quarticSignedPoleNormalizedOrdinateOffset t rho| <= eta
    ∧
  ((rho : ℂ).im - t)^2 <= 6 * heightOf rho^2

def quarticSignedPoleLocalGood
    (t eta : ℝ) (rho : Zeros) : Prop :=
  |quarticSignedPoleNormalizedOrdinateOffset t rho| <= eta
    ∧
  6 * heightOf rho^2 < ((rho : ℂ).im - t)^2

def quarticSignedPoleFar
    (t eta : ℝ) (rho : Zeros) : Prop :=
  eta < |quarticSignedPoleNormalizedOrdinateOffset t rho|

theorem quarticSignedPole_cone_good_far_partition
    (t eta : ℝ) (rho : Zeros) :
    quarticSignedPoleLocalCone t eta rho
      ∨ quarticSignedPoleLocalGood t eta rho
      ∨ quarticSignedPoleFar t eta rho := by
  by_cases hlocal :
      |quarticSignedPoleNormalizedOrdinateOffset t rho| <= eta
  · by_cases hcone :
        ((rho : ℂ).im - t)^2 <= 6 * heightOf rho^2
    · exact Or.inl ⟨hlocal,hcone⟩
    · exact Or.inr (Or.inl ⟨hlocal,lt_of_not_ge hcone⟩)
  · exact Or.inr (Or.inr (lt_of_not_ge hlocal))

theorem quarticSignedPoleLocalCone_not_good
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleLocalCone t eta rho) :
    ¬ quarticSignedPoleLocalGood t eta rho := by
  intro hg
  linarith [h.2,hg.2]

theorem quarticSignedPoleLocalCone_not_far
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleLocalCone t eta rho) :
    ¬ quarticSignedPoleFar t eta rho := by
  intro hf
  linarith [h.1,hf]

theorem quarticSignedPoleLocalGood_not_cone
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleLocalGood t eta rho) :
    ¬ quarticSignedPoleLocalCone t eta rho := by
  intro hc
  linarith [h.2,hc.2]

theorem quarticSignedPoleLocalGood_not_far
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleLocalGood t eta rho) :
    ¬ quarticSignedPoleFar t eta rho := by
  intro hf
  linarith [h.1,hf]

theorem quarticSignedPoleFar_not_cone
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleFar t eta rho) :
    ¬ quarticSignedPoleLocalCone t eta rho := by
  intro hc
  linarith [h,hc.1]

theorem quarticSignedPoleFar_not_good
    {t eta : ℝ} {rho : Zeros}
    (h : quarticSignedPoleFar t eta rho) :
    ¬ quarticSignedPoleLocalGood t eta rho := by
  intro hg
  linarith [h,hg.1]

/--
Exact off-ordinate literal source extended by zero to all zero ordinates.
This lets the cone/good/far partition live on the ordinary Zeros carrier
used by the existing finite symmetric exhaustion.
-/
def QuarticFourSignedPolePair.literalOffOrdSource
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : ℝ := by
  classical
  exact if h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
    W.signedLiteralPairSourceTerm ⟨rho,h⟩
  else
    0

def QuarticFourSignedPolePair.literalConeExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleLocalCone t eta rho then
    W.literalOffOrdSource rho
  else
    0

def QuarticFourSignedPolePair.literalGoodExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleLocalGood t eta rho then
    W.literalOffOrdSource rho
  else
    0

def QuarticFourSignedPolePair.literalFarExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleFar t eta rho then
    W.literalOffOrdSource rho
  else
    0

theorem QuarticFourSignedPolePair.literalOffOrdSource_eq_cone_add_good_add_far
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalOffOrdSource rho
      =
    W.literalConeExactTerm eta rho
      + W.literalGoodExactTerm eta rho
      + W.literalFarExactTerm eta rho := by
  classical
  rcases quarticSignedPole_cone_good_far_partition t eta rho with hc | hg | hf
  · have hng := quarticSignedPoleLocalCone_not_good hc
    have hnf := quarticSignedPoleLocalCone_not_far hc
    simp [QuarticFourSignedPolePair.literalConeExactTerm,
      QuarticFourSignedPolePair.literalGoodExactTerm,
      QuarticFourSignedPolePair.literalFarExactTerm,
      hc,hng,hnf]
  · have hnc := quarticSignedPoleLocalGood_not_cone hg
    have hnf := quarticSignedPoleLocalGood_not_far hg
    simp [QuarticFourSignedPolePair.literalConeExactTerm,
      QuarticFourSignedPolePair.literalGoodExactTerm,
      QuarticFourSignedPolePair.literalFarExactTerm,
      hg,hnc,hnf]
  · have hnc := quarticSignedPoleFar_not_cone hf
    have hng := quarticSignedPoleFar_not_good hf
    simp [QuarticFourSignedPolePair.literalConeExactTerm,
      QuarticFourSignedPolePair.literalGoodExactTerm,
      QuarticFourSignedPolePair.literalFarExactTerm,
      hf,hnc,hng]

def QuarticFourSignedPolePair.literalConeExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalConeExactTerm eta rho

def QuarticFourSignedPolePair.literalGoodExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalGoodExactTerm eta rho

def QuarticFourSignedPolePair.literalFarExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalFarExactTerm eta rho

def QuarticFourSignedPolePair.literalOffOrdExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalOffOrdSource rho

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_eq_cone_add_good_add_far
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      =
    W.literalConeExactAt eta n
      + W.literalGoodExactAt eta n
      + W.literalFarExactAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalOffOrdExactAt
    QuarticFourSignedPolePair.literalConeExactAt
    QuarticFourSignedPolePair.literalGoodExactAt
    QuarticFourSignedPolePair.literalFarExactAt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact W.literalOffOrdSource_eq_cone_add_good_add_far rho

def QuarticFourSignedPolePair.literalConeDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalCone t eta rho then
      max (W.literalOffOrdSource rho) 0
    else
      0

theorem QuarticFourSignedPolePair.literalConeDebtAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalConeDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalConeDebtAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hc : quarticSignedPoleLocalCone t eta rho
    · simp [hc]
    · simp [hc]

theorem QuarticFourSignedPolePair.literalConeExactAt_le_debt
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeExactAt eta n
      <= W.literalConeDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalConeExactAt
    QuarticFourSignedPolePair.literalConeExactTerm
    QuarticFourSignedPolePair.literalConeDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · simp [hc, le_max_left]
  · simp [hc]

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_nonpos_of_localGood
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hg : quarticSignedPoleLocalGood t eta rho) :
    W.literalJointQuarticPolynomial rho <= 0 := by
  exact
    W.literalJointQuarticPolynomial_nonpos_of_six_height_sq_le_delta_sq
      ht rho hg.2.le

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_nonneg_of_localCone
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    0 <= W.literalJointQuarticPolynomial rho := by
  exact
    W.literalJointQuarticPolynomial_nonneg_of_delta_sq_le_six_height_sq
      ht rho hc.2

def QuarticFourSignedPolePair.literalGoodQuarticGainAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalGood t eta rho then
      - W.literalJointQuarticPolynomial rho
    else
      0

theorem QuarticFourSignedPolePair.literalGoodQuarticGainAt_nonneg
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalGoodQuarticGainAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalGoodQuarticGainAt
  apply Finset.sum_nonneg
  intro rho hrho
  by_cases hg : quarticSignedPoleLocalGood t eta rho
  · simp [hg,
      neg_nonneg.mpr
        (W.literalJointQuarticPolynomial_nonpos_of_localGood ht hg)]
  · simp [hg]


/-!
## Finite local remainder debt and the Clay-facing scalar budget
-/

def QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : ℝ := by
  classical
  exact if h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
    W.literalJointQuarticRemainder rho
  else
    0

def quarticSignedPoleLocal
    (t eta : ℝ) (rho : Zeros) : Prop :=
  |quarticSignedPoleNormalizedOrdinateOffset t rho| <= eta

def QuarticFourSignedPolePair.literalLocalRemainderDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      |W.literalJointQuarticRemainderOffOrd rho|
    else
      0

theorem QuarticFourSignedPolePair.literalLocalRemainderDebtAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalLocalRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalRemainderDebtAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hl : quarticSignedPoleLocal t eta rho
    · simp [hl]
    · simp [hl]

theorem QuarticFourSignedPolePair.literalOffOrdSource_eq_polynomial_add_remainderOffOrd
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalOffOrdSource rho
      =
    (if h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
      W.literalJointQuarticPolynomial rho
        + W.literalJointQuarticRemainderOffOrd rho
     else
      0) := by
  classical
  by_cases h : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
  · have hs :=
      W.signedLiteralPairSourceTerm_eq_literalQuarticJet ht
        (⟨rho,h⟩ : ((SameOrd t)ᶜ : Set Zeros))
    simp [QuarticFourSignedPolePair.literalOffOrdSource,
      QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd,
      h] at hs ⊢
    exact hs
  · simp [QuarticFourSignedPolePair.literalOffOrdSource,
      QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd,
      h]

/--
Pointwise local budget on the cone lane:
exact source <= positive-part cone debt + absolute joint remainder.
-/
theorem QuarticFourSignedPolePair.literalConeExactTerm_le_debt_add_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalConeExactTerm eta rho
      <=
    (if quarticSignedPoleLocalCone t eta rho then
      max (W.literalOffOrdSource rho) 0
     else 0)
      +
    (if quarticSignedPoleLocal t eta rho then
      |W.literalJointQuarticRemainderOffOrd rho|
     else 0) := by
  classical
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · have hl : quarticSignedPoleLocal t eta rho := hc.1
    simp [QuarticFourSignedPolePair.literalConeExactTerm, hc, hl]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · simp [QuarticFourSignedPolePair.literalConeExactTerm, hc]

/--
Pointwise local budget on the good lane:
the nonpositive quartic polynomial supplies a gain, while the exact joint
remainder is charged only by absolute value.
-/
theorem QuarticFourSignedPolePair.literalGoodExactTerm_add_gain_le_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalGoodExactTerm eta rho
      +
    (if quarticSignedPoleLocalGood t eta rho then
      - W.literalJointQuarticPolynomial rho
     else 0)
      <=
    (if quarticSignedPoleLocal t eta rho then
      |W.literalJointQuarticRemainderOffOrd rho|
     else 0) := by
  classical
  by_cases hg : quarticSignedPoleLocalGood t eta rho
  · have hl : quarticSignedPoleLocal t eta rho := hg.1
    by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hs :=
        W.signedLiteralPairSourceTerm_eq_literalQuarticJet ht
          (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros))
      simp [QuarticFourSignedPolePair.literalGoodExactTerm,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd,
        hg,hl,hoff] at hs ⊢
      rw [hs]
      linarith [le_abs_self
        (W.literalJointQuarticRemainder rho)]
    · simp [QuarticFourSignedPolePair.literalGoodExactTerm,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd,
        hg,hl,hoff]
      have hpoly :=
        W.literalJointQuarticPolynomial_nonpos_of_localGood ht hg
      linarith
  · simp [QuarticFourSignedPolePair.literalGoodExactTerm, hg]

theorem QuarticFourSignedPolePair.literalCone_add_good_le_debt_sub_gain_add_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeExactAt eta n
      + W.literalGoodExactAt eta n
      <=
    W.literalConeDebtAt eta n
      - W.literalGoodQuarticGainAt eta n
      + W.literalLocalRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalConeExactAt
    QuarticFourSignedPolePair.literalGoodExactAt
    QuarticFourSignedPolePair.literalConeDebtAt
    QuarticFourSignedPolePair.literalGoodQuarticGainAt
    QuarticFourSignedPolePair.literalLocalRemainderDebtAt
  rw [← Finset.sum_add_distrib]
  rw [show
      (∑ x ∈ centeredZeroFinset t n,
        (if quarticSignedPoleLocalCone t eta x then
            max (W.literalOffOrdSource x) 0 else 0))
        -
      (∑ x ∈ centeredZeroFinset t n,
        (if quarticSignedPoleLocalGood t eta x then
            -W.literalJointQuarticPolynomial x else 0))
        +
      (∑ x ∈ centeredZeroFinset t n,
        (if quarticSignedPoleLocal t eta x then
            |W.literalJointQuarticRemainderOffOrd x| else 0))
      =
      ∑ x ∈ centeredZeroFinset t n,
        ((if quarticSignedPoleLocalCone t eta x then
            max (W.literalOffOrdSource x) 0 else 0)
          -
         (if quarticSignedPoleLocalGood t eta x then
            -W.literalJointQuarticPolynomial x else 0)
          +
         (if quarticSignedPoleLocal t eta x then
            |W.literalJointQuarticRemainderOffOrd x| else 0)) by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · have hng := quarticSignedPoleLocalCone_not_good hc
    have hl : quarticSignedPoleLocal t eta rho := hc.1
    simp [QuarticFourSignedPolePair.literalConeExactTerm,
      QuarticFourSignedPolePair.literalGoodExactTerm,
      hc,hng,hl]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · by_cases hg : quarticSignedPoleLocalGood t eta rho
    · have hnc := quarticSignedPoleLocalGood_not_cone hg
      have hl : quarticSignedPoleLocal t eta rho := hg.1
      have h :=
        W.literalGoodExactTerm_add_gain_le_remainder
          ht rho
      simp [QuarticFourSignedPolePair.literalConeExactTerm,
        hc,hg,hl] at h ⊢
      exact h
    · have hnotlocal :
          ¬ quarticSignedPoleLocal t eta rho := by
        intro hl
        by_cases hcone :
            ((rho : ℂ).im-t)^2 <= 6 * heightOf rho^2
        · exact hc ⟨hl,hcone⟩
        · exact hg ⟨hl,lt_of_not_ge hcone⟩
      simp [QuarticFourSignedPolePair.literalConeExactTerm,
        QuarticFourSignedPolePair.literalGoodExactTerm,
        hc,hg,hnotlocal]

/--
Finite Clay-facing G3 budget.

The far lane remains the exact decaying literal kernel.  Only the local lanes
are charged by cone debt / good quartic gain / local absolute remainder debt.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_coneDebt_sub_goodGain_add_remainder_add_far
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <=
    W.literalConeDebtAt eta n
      - W.literalGoodQuarticGainAt eta n
      + W.literalLocalRemainderDebtAt eta n
      + W.literalFarExactAt eta n := by
  rw [W.literalOffOrdExactAt_eq_cone_add_good_add_far
      (eta:=eta)]
  have hlocal :=
    W.literalCone_add_good_le_debt_sub_gain_add_remainder
      ht n
  linarith

end Synthesis
