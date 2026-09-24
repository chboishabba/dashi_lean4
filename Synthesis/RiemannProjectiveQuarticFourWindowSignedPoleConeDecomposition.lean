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

def quarticSignedPoleCanonicalLocalRadius : ℝ :=
  1 / (Real.pi + 1)

theorem quarticSignedPoleCanonicalLocalRadius_pos :
    0 < quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalLocalRadius
  positivity

theorem quarticSignedPoleCanonicalLocalRadius_lt_one :
    quarticSignedPoleCanonicalLocalRadius < 1 := by
  unfold quarticSignedPoleCanonicalLocalRadius
  rw [div_lt_one (by positivity : 0 < Real.pi + 1)]
  linarith [Real.pi_pos]


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


/-!
## Fixed-width containment of the unfavorable cone

Every nontrivial zeta zero lies in the critical strip, so
|beta-1/2| <= 1/2.  Therefore the mixed cone delta^2 <= 6 a^2 is contained in
an ordinate window of fixed width, independent of t.
-/

theorem quarticSignedPoleLocalCone_delta_sq_le_three_halves
    {t eta : ℝ} {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    ((rho : ℂ).im-t)^2 <= (3/2 : ℝ) := by
  have hstrip := zetaZero_height_abs_le_half rho
  have ha2 :
      heightOf rho^2 <= (1/2 : ℝ)^2 := by
    nlinarith [sq_nonneg (heightOf rho),
      sq_nonneg ((1/2 : ℝ) - |heightOf rho|)]
  nlinarith [hc.2]

theorem quarticSignedPoleLocalCone_abs_delta_le_three_halves
    {t eta : ℝ} {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    |(rho : ℂ).im-t| <= (3/2 : ℝ) := by
  have hsq :=
    quarticSignedPoleLocalCone_delta_sq_le_three_halves hc
  have habs2 :
      |(rho : ℂ).im-t|^2 = ((rho : ℂ).im-t)^2 := by
    rw [sq_abs]
  rw [← habs2] at hsq
  have habs0 : 0 <= |(rho : ℂ).im-t| := abs_nonneg _
  nlinarith

theorem quarticSignedPoleLocalCone_mem_fixed_window
    {t eta : ℝ} {rho : Zeros}
    (hc : quarticSignedPoleLocalCone t eta rho) :
    t - (3/2 : ℝ) <= (rho : ℂ).im
      ∧
    (rho : ℂ).im <= t + (3/2 : ℝ) := by
  have h :=
    quarticSignedPoleLocalCone_abs_delta_le_three_halves hc
  rw [abs_le] at h
  constructor <;> linarith


/--
Unconditional O(log t) envelope for the entire fixed-width window containing
the mixed cone.

This is deliberately a count envelope, not yet a payment of the weighted
literal cone debt.
-/
theorem exists_quarticSignedPole_fixedConeWindow_zeroCount_bound :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t : ℝ}, 200 <= t ->
        (zetaZeroConfig.N
          (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
          <=
        3 * A0 * Real.log (t + 5) := by
  obtain ⟨A0,hA01,hA0⟩ :=
    Zeta23.RvM.zeta_local_zero_count
  have hA0nonneg : 0 <= A0 := by linarith
  refine ⟨A0,hA0nonneg,?_⟩
  intro t ht
  let A : ℝ := t - 3/2
  let B : ℝ := t - 1/2
  let C : ℝ := t + 1/2
  let D : ℝ := t + 3/2
  have hApos : 0 < A := by dsimp [A]; linarith
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hCpos : 0 < C := by dsimp [C]; linarith
  have hAB : A <= B := by dsimp [A,B]; linarith
  have hBC : B <= C := by dsimp [B,C]; linarith
  have hCD : C <= D := by dsimp [C,D]; linarith
  have hB : B = A + 1 := by dsimp [A,B]; ring
  have hC : C = B + 1 := by dsimp [B,C]; ring
  have hD : D = C + 1 := by dsimp [C,D]; ring
  have eAB :=
    Zeta23.Ncount_add (a:=A) (b:=B) (c:=D)
      hAB (hBC.trans hCD)
  have eBCD :=
    Zeta23.Ncount_add (a:=B) (b:=C) (c:=D)
      hBC hCD
  have hsplit :
      (zetaZeroConfig.N A D : ℝ)
        =
      (zetaZeroConfig.N A B : ℝ)
        + (zetaZeroConfig.N B C : ℝ)
        + (zetaZeroConfig.N C D : ℝ) := by
    simpa only [Zeta23.zetaZeroConfig_N] using by
      rw [eAB, eBCD]
      push_cast
      ring
  have h1 :
      (zetaZeroConfig.N A B : ℝ)
        <= A0 * Real.log (A + 3) := by
    rw [hB]
    simpa [abs_of_pos hApos] using hA0 A
  have h2 :
      (zetaZeroConfig.N B C : ℝ)
        <= A0 * Real.log (B + 3) := by
    rw [hC]
    simpa [abs_of_pos hBpos] using hA0 B
  have h3 :
      (zetaZeroConfig.N C D : ℝ)
        <= A0 * Real.log (C + 3) := by
    rw [hD]
    simpa [abs_of_pos hCpos] using hA0 C
  have hlog1 :
      Real.log (A+3) <= Real.log (t+5) := by
    apply Real.log_le_log
    · dsimp [A]
      linarith
    · dsimp [A]
      linarith
  have hlog2 :
      Real.log (B+3) <= Real.log (t+5) := by
    apply Real.log_le_log
    · dsimp [B]
      linarith
    · dsimp [B]
      linarith
  have hlog3 :
      Real.log (C+3) <= Real.log (t+5) := by
    apply Real.log_le_log
    · dsimp [C]
      linarith
    · dsimp [C]
      linarith
  rw [hsplit]
  have hb1 := mul_le_mul_of_nonneg_left hlog1 hA0nonneg
  have hb2 := mul_le_mul_of_nonneg_left hlog2 hA0nonneg
  have hb3 := mul_le_mul_of_nonneg_left hlog3 hA0nonneg
  dsimp [A,B,C,D] at *
  nlinarith


/-!
## Fail-fast weighted cone multiplicity compiler
-/

def QuarticFourSignedPolePair.literalConeMultiplicityAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℕ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalCone t eta rho then
      zetaZeroConfig.mult (rho : ℂ)
    else
      0

theorem QuarticFourSignedPolePair.literalConeDebtAt_le_envelope_mul_multiplicity
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (W.literalConeMultiplicityAt eta n : ℝ) := by
  classical
  unfold QuarticFourSignedPolePair.literalConeDebtAt
    QuarticFourSignedPolePair.literalConeMultiplicityAt
  rw [Nat.cast_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hsrc :=
        W.literalConeExactSource_le_envelope
          ht hc hoff
      have hC := W.literalConeEnvelopeConstant_nonneg
      have hr6 : 0 < (t/16)^6 := by positivity
      have hR :
          0 <=
            W.literalConeEnvelopeConstant / (t/16)^6
              * (zetaZeroConfig.mult (rho : ℂ) : ℝ) := by
        positivity
      simp [hc,
        QuarticFourSignedPolePair.literalOffOrdSource,
        hoff]
      apply max_le
      · simpa [mul_comm, mul_left_comm, mul_assoc,
          div_eq_mul_inv] using hsrc
      · exact hR
    · simp [hc,
        QuarticFourSignedPolePair.literalOffOrdSource,
        hoff]
  · simp [hc]

def quarticSignedPoleConeComplexSet
    (t eta : ℝ) : Set ℂ :=
  {z : ℂ |
    ∃ hz : z ∈ zetaZeroConfig.carrier,
      quarticSignedPoleLocalCone t eta (⟨z,hz⟩ : Zeros)}

theorem quarticSignedPoleConeComplexSet_subset_fixedWindow
    {t eta : ℝ} :
    quarticSignedPoleConeComplexSet t eta
      ⊆
    zetaZeroConfig.window
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
  intro z hz
  rcases hz with ⟨hzCarrier,hcone⟩
  have hw :=
    quarticSignedPoleLocalCone_mem_fixed_window hcone
  exact ⟨hzCarrier,hw.1,hw.2⟩

theorem QuarticFourSignedPolePair.literalConeMultiplicityAt_le_fixedWindowN
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeMultiplicityAt eta n
      <=
    zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
  classical
  let F : Finset Zeros :=
    (centeredZeroFinset t n).filter
      (quarticSignedPoleLocalCone t eta)
  let s : Set ℂ :=
    (fun rho : Zeros => (rho : ℂ)) '' (↑F : Set Zeros)
  have hsWindow :
      s ⊆
        zetaZeroConfig.window
          (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) := by
    intro z hz
    rcases hz with ⟨rho,hrho,rfl⟩
    have hcone :
        quarticSignedPoleLocalCone t eta rho := by
      have := (Finset.mem_filter.mp hrho).2
      exact this
    exact quarticSignedPoleConeComplexSet_subset_fixedWindow
      ⟨rho.2,hcone⟩
  have hmono :=
    zetaZeroConfig.finsum_mult_mono
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ))
      hsWindow subset_rfl
  have hsFinite :
      s.Finite := by
    exact Set.Finite.image F.finite_toSet _
  have hsum :
      W.literalConeMultiplicityAt eta n
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z := by
    unfold QuarticFourSignedPolePair.literalConeMultiplicityAt
    change
      (∑ rho ∈ centeredZeroFinset t n,
        if quarticSignedPoleLocalCone t eta rho then
          zetaZeroConfig.mult (rho : ℂ) else 0)
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [← Finset.sum_filter]
    change
      (∑ rho ∈ F, zetaZeroConfig.mult (rho : ℂ))
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [finsum_mem_eq_finite_toFinset_sum _ hsFinite]
    have himage :
        hsFinite.toFinset
          =
        F.image (fun rho : Zeros => (rho : ℂ)) := by
      ext z
      simp [s]
    rw [himage, Finset.sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [hsum]
  exact hmono

theorem QuarticFourSignedPolePair.literalConeDebtAt_le_fixedWindowN
    {t eta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := by
  have hdebt :=
    W.literalConeDebtAt_le_envelope_mul_multiplicity
      ht n
  have hmult :=
    W.literalConeMultiplicityAt_le_fixedWindowN
      (eta:=eta) n
  have hC : 0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  exact hdebt.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmult) hC)


/--
Unconditional finite cone-debt bound at the correct physical t^-6 scale.

The witness-dependent constant is deliberately left explicit.  The theorem is
intended as a fail-fast scaling diagnostic, not a constant-optimization result.
-/
theorem exists_quarticFourSignedPole_literalConeDebtAt_le_log_over_r6 :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t eta : ℝ},
        200 <= t ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ n : ℕ,
          W.literalConeDebtAt eta n
            <=
          3 * A0 * W.literalConeEnvelopeConstant
            * Real.log (t + 5)
            / (t/16)^6 := by
  obtain ⟨A0,hA0,hcount⟩ :=
    exists_quarticSignedPole_fixedConeWindow_zeroCount_bound
  refine ⟨A0,hA0,?_⟩
  intro t eta ht W n
  have hdebt :=
    W.literalConeDebtAt_le_fixedWindowN
      (eta:=eta) ht n
  have hN := hcount ht
  have hC :
      0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hN hC
  calc
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := hdebt
    _ <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (3 * A0 * Real.log (t+5)) := hmul
    _ =
    3 * A0 * W.literalConeEnvelopeConstant
      * Real.log (t+5) / (t/16)^6 := by ring

/--
Canonical coefficient appearing after the common r^-6 factor is cancelled
against any target lower bound of the form c*S(W)*a^4/r^6.
-/
def QuarticFourSignedPolePair.coneLogCoefficient
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A0 : ℝ) : ℝ :=
  3 * A0 * W.literalConeEnvelopeConstant * Real.log (t+5)

theorem QuarticFourSignedPolePair.coneDebt_le_coneLogCoefficient_over_r6
    {t eta A0 : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hA0 :
      (zetaZeroConfig.N
        (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
        <= 3 * A0 * Real.log (t+5))
    (hA0nonneg : 0 <= A0) :
    W.literalConeDebtAt eta n
      <=
    W.coneLogCoefficient A0 / (t/16)^6 := by
  have hdebt :=
    W.literalConeDebtAt_le_fixedWindowN
      (eta:=eta) ht n
  have hC :
      0 <= W.literalConeEnvelopeConstant / (t/16)^6 := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hA0 hC
  unfold QuarticFourSignedPolePair.coneLogCoefficient
  calc
    W.literalConeDebtAt eta n
      <=
    W.literalConeEnvelopeConstant / (t/16)^6
      *
    (zetaZeroConfig.N
      (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := hdebt
    _ <=
    W.literalConeEnvelopeConstant / (t/16)^6
      * (3 * A0 * Real.log (t+5)) := hmul
    _ =
    (3 * A0 * W.literalConeEnvelopeConstant * Real.log (t+5))
      / (t/16)^6 := by ring


/-!
## Fail-fast target-scaling diagnostic

The absolute cone estimate has the correct r^-6 scale.  What it does not
supply is a quartic floor in the target horizontal displacement a.

The elementary lemma below is deliberately not a statement about existence of
zeta zeros at arbitrary horizontal coordinates.  It only records that the
strip hypothesis 0<|a|<=1/2, by itself, cannot imply a uniform positive lower
bound for a^4.
-/

theorem exists_punctured_half_with_quartic_below
    {B : ℝ} (hB : 0 < B) :
    ∃ a : ℝ,
      0 < |a| ∧
      |a| <= (1/2 : ℝ) ∧
      a^4 < B := by
  let a : ℝ := min (1/4 : ℝ) (B/8)
  have haPos : 0 < a := by
    dsimp [a]
    exact lt_min (by norm_num) (by positivity)
  have haQuarter : a <= (1/4 : ℝ) := by
    dsimp [a]
    exact min_le_left _ _
  have haB : a <= B/8 := by
    dsimp [a]
    exact min_le_right _ _
  have haOne : a <= 1 := by linarith
  have haNonneg : 0 <= a := haPos.le
  have ha2 : a^2 <= a := by
    nlinarith [mul_nonneg haNonneg (sub_nonneg.mpr haOne)]
  have ha2One : a^2 <= 1 := ha2.trans haOne
  have ha4 : a^4 <= a^2 := by
    have hnon2 : 0 <= a^2 := sq_nonneg a
    have hprod :=
      mul_nonneg hnon2 (sub_nonneg.mpr ha2One)
    nlinarith [show a^4 = (a^2)^2 by ring]
  refine ⟨a,?_,?_,?_⟩
  · simpa [abs_of_pos haPos]
  · rw [abs_of_pos haPos]
    linarith
  · have : a^4 <= a := ha4.trans ha2
    linarith

def QuarticFourSignedPolePair.absoluteConeTargetCoefficientCondition
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A0 c a : ℝ) : Prop :=
  W.coneLogCoefficient A0
    < c * W.targetStrength * a^4

/--
If a future target theorem supplies
  target >= c*S(W)*a^4/r^6,
then the absolute cone estimate is paid exactly by the scalar coefficient
condition above.  This theorem intentionally leaves that target lower bound
as an explicit hypothesis because the current quantitative target compiler
only proves positivity.
-/
theorem QuarticFourSignedPolePair.literalConeDebtAt_lt_target_of_quartic_floor
    {t eta A0 c a target : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hcount :
      (zetaZeroConfig.N
        (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
        <= 3 * A0 * Real.log (t+5))
    (hA0 : 0 <= A0)
    (hcoef : W.absoluteConeTargetCoefficientCondition A0 c a)
    (htarget :
      c * W.targetStrength * a^4 / (t/16)^6 <= target) :
    W.literalConeDebtAt eta n < target := by
  have hdebt :=
    W.coneDebt_le_coneLogCoefficient_over_r6
      ht n hcount hA0
  have hr6 : 0 < (t/16)^6 := by positivity
  have hcoefScaled :
      W.coneLogCoefficient A0 / (t/16)^6
        <
      c * W.targetStrength * a^4 / (t/16)^6 := by
    exact div_lt_div_of_pos_right hcoef hr6
  exact lt_of_le_of_lt hdebt
    (hcoefScaled.trans_le htarget)


/-!
## Signed compensation normal form

Do not pay the exact far lane by absolute value.  The finite Clay-facing budget
is compressed to

  localDebt      = coneDebt + localRemainderDebt
  compensation   = goodQuarticGain - farExact

so the exact off-ordinate source obeys

  offOrdExact <= localDebt - compensation.

This is the fail-fast interface for the remaining conventional analysis.
-/

def QuarticFourSignedPolePair.literalLocalDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalConeDebtAt eta n
    + W.literalLocalRemainderDebtAt eta n

def QuarticFourSignedPolePair.literalSignedCompensationAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalGoodQuarticGainAt eta n
    - W.literalFarExactAt eta n

def QuarticFourSignedPolePair.literalJointBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalLocalDebtAt eta n
    - W.literalSignedCompensationAt eta n

theorem QuarticFourSignedPolePair.literalJointBudgetAt_eq
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalJointBudgetAt eta n
      =
    W.literalConeDebtAt eta n
      - W.literalGoodQuarticGainAt eta n
      + W.literalLocalRemainderDebtAt eta n
      + W.literalFarExactAt eta n := by
  unfold QuarticFourSignedPolePair.literalJointBudgetAt
    QuarticFourSignedPolePair.literalLocalDebtAt
    QuarticFourSignedPolePair.literalSignedCompensationAt
  ring

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_jointBudget
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <= W.literalJointBudgetAt eta n := by
  rw [W.literalJointBudgetAt_eq]
  exact
    W.literalOffOrdExactAt_le_coneDebt_sub_goodGain_add_remainder_add_far
      ht n

/--
A target-margin compiler that preserves the sign of the good/far
compensation.  No absolute estimate on the far exact carrier appears.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_lt_margin_of_debt_lt_compensation_add
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hpay :
      W.literalLocalDebtAt eta n
        < W.literalSignedCompensationAt eta n + margin) :
    W.literalOffOrdExactAt n < margin := by
  have hbudget :=
    W.literalOffOrdExactAt_le_jointBudget ht n
  unfold QuarticFourSignedPolePair.literalJointBudgetAt at hbudget
  linarith

/--
Equivalent scalar payment form.  This is the preferred finite conventional
research statement after the absolute cone estimate has failed to pay the
target by itself.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_lt_margin_of_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hgap :
      margin + W.literalSignedCompensationAt eta n
        - W.literalLocalDebtAt eta n > 0) :
    W.literalOffOrdExactAt n < margin := by
  apply W.literalOffOrdExactAt_lt_margin_of_debt_lt_compensation_add
    ht n
  linarith

/--
The local debt is nonnegative; all potentially useful negative information is
therefore concentrated in the signed compensation coordinate.
-/
theorem QuarticFourSignedPolePair.literalLocalDebtAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalLocalDebtAt eta n := by
  unfold QuarticFourSignedPolePair.literalLocalDebtAt
  exact add_nonneg
    (W.literalConeDebtAt_nonneg n)
    (W.literalLocalRemainderDebtAt_nonneg n)


/-!
## Cofinal limit of the exact off-ordinate source

The exact off-ordinate source is extended by zero across SameOrd(t).  This
extension is summable because its restriction to the complement is exactly the
already-summable literal pair source.
-/

theorem QuarticFourSignedPolePair.literalOffOrdSource_summable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Summable W.literalOffOrdSource := by
  classical
  let s : Set Zeros := ((SameOrd t)ᶜ : Set Zeros)
  have hsub :
      Summable (fun rho : s => W.literalOffOrdSource (rho : Zeros)) := by
    refine (W.signedLiteralPairSourceTerm_summable ht).congr ?_
    intro rho
    simp [QuarticFourSignedPolePair.literalOffOrdSource, s, rho.2]
  have hind :
      Summable (s.indicator W.literalOffOrdSource) :=
    (summable_subtype_iff_indicator (s:=s)).mp hsub
  refine hind.congr ?_
  intro rho
  by_cases h : rho ∈ s
  · simp [Set.indicator, h,
      QuarticFourSignedPolePair.literalOffOrdSource]
  · simp [Set.indicator, h,
      QuarticFourSignedPolePair.literalOffOrdSource, s] at *

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_tendsto_tsum
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto W.literalOffOrdExactAt atTop
      (𝓝 (∑' rho : Zeros, W.literalOffOrdSource rho)) := by
  have hsum := (W.literalOffOrdSource_summable ht).hasSum
  have hcofinal := centeredZeroFinset_tendsto_atTop t
  exact hsum.comp hcofinal

/--
A cofinal eventual signed-compensation payment compiles directly to a global
upper bound for the exact off-ordinate source limit.
-/
theorem QuarticFourSignedPolePair.globalOffOrd_lt_margin_of_eventual_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSignedCompensationAt eta n
          - W.literalLocalDebtAt eta n > 0) :
    (∑' rho : Zeros, W.literalOffOrdSource rho) <= margin := by
  have hfinite :
      ∀ᶠ n : ℕ in atTop,
        W.literalOffOrdExactAt n <= margin := by
    filter_upwards [hgap] with n hn
    exact (W.literalOffOrdExactAt_lt_margin_of_compensation_gap
      ht n hn).le
  have hlim :=
    W.literalOffOrdExactAt_tendsto_tsum ht
  exact le_of_tendsto hlim hfinite


/-!
## Same-object global tsum weld and completed-residual compiler
-/

theorem QuarticFourSignedPolePair.literalOffOrdSource_tsum_eq_signedLiteralPairSource_tsum
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∑' rho : Zeros, W.literalOffOrdSource rho)
      =
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.signedLiteralPairSourceTerm sigma := by
  classical
  let s : Set Zeros := ((SameOrd t)ᶜ : Set Zeros)
  calc
    (∑' rho : Zeros, W.literalOffOrdSource rho)
      =
    ∑' rho : Zeros,
      s.indicator W.literalOffOrdSource rho := by
        apply tsum_congr
        intro rho
        by_cases h : rho ∈ s
        · simp [Set.indicator, h]
        · simp [Set.indicator, h,
            QuarticFourSignedPolePair.literalOffOrdSource, s] at *
    _ =
    ∑' sigma : s,
      W.literalOffOrdSource (sigma : Zeros) := by
        rw [← tsum_subtype]
    _ =
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.signedLiteralPairSourceTerm sigma := by
        apply tsum_congr
        intro sigma
        simp [QuarticFourSignedPolePair.literalOffOrdSource,
          s, sigma.2]

theorem QuarticFourSignedPolePair.globalSignedLiteralPairSource_le_margin_of_eventual_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSignedCompensationAt eta n
          - W.literalLocalDebtAt eta n > 0) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.signedLiteralPairSourceTerm sigma)
      <= margin := by
  rw [← W.literalOffOrdSource_tsum_eq_signedLiteralPairSource_tsum]
  exact W.globalOffOrd_lt_margin_of_eventual_compensation_gap
    ht hgap

/--
Clay-facing compiler from one eventual signed-compensation statement to G3.

The scalar margin is compared against the exact smooth-mu correction appearing
in completedSignedResidual_eq_jointPairSource; no N-mu/horizontal absolute
split is reintroduced.
-/
theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_eventual_compensation_gap
    {t eta margin : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSignedCompensationAt eta n
          - W.literalLocalDebtAt eta n > 0)
    (hmargin :
      margin
        <
      4 * W.combinedZeroHeightDefect rho
        +
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  have htpos : 0 < t := by linarith
  have hsum :=
    W.globalSignedLiteralPairSource_le_margin_of_eventual_compensation_gap
      htpos hgap
  rw [W.completedSignedResidual_eq_jointPairSource ht]
  linarith


/-!
## Human-facing uniform compensation theorem

The auxiliary scalar margin used by the compiler is not part of the preferred
Clay-facing statement.  The actual analytic min-cut is a uniform positive gap
between the finite signed budget and the exact target threshold.
-/

def QuarticFourSignedPolePair.compensationTargetThreshold
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : ℝ :=
  4 * W.combinedZeroHeightDefect rho
    +
  ∫ tau : ℝ,
    W.signedOrdinateTest tau * Zeta23.mu tau

def QuarticFourSignedPolePair.UniformSignedCompensationGap
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      W.literalLocalDebtAt
          quarticSignedPoleCanonicalLocalRadius n
        -
      W.literalSignedCompensationAt
          quarticSignedPoleCanonicalLocalRadius n
      <=
      W.compensationTargetThreshold rho - eps

/--
The one conventional analytic theorem now sufficient for G3.

The compiler chooses the old auxiliary margin internally:
  M = T_W(rho) - eps/2.
-/
theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_uniform_compensation_gap
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hC : W.UniformSignedCompensationGap rho) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  rcases hC with ⟨eps,heps,N,hN⟩
  let T : ℝ := W.compensationTargetThreshold rho
  let M : ℝ := T - eps/2
  have hgap :
      ∀ᶠ n : ℕ in atTop,
        M
          + W.literalSignedCompensationAt
              quarticSignedPoleCanonicalLocalRadius n
          - W.literalLocalDebtAt
              quarticSignedPoleCanonicalLocalRadius n
        > 0 := by
    rw [eventually_atTop]
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    dsimp [T, M] at h ⊢
    linarith
  have hmargin :
      M
        <
      4 * W.combinedZeroHeightDefect rho
        +
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau := by
    dsimp [M, T, QuarticFourSignedPolePair.compensationTargetThreshold]
    linarith
  exact
    W.completedSignedResidual_lt_target_of_eventual_compensation_gap
      ht hgap hmargin

/--
Expanded form of the preferred analytic hypothesis, useful for papers and
downstream modules that should not mention the auxiliary proposition name.
-/
theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_uniform_compensation_gap_explicit
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hC :
      ∃ eps : ℝ, 0 < eps ∧
        ∃ N : ℕ, ∀ n : ℕ, N <= n ->
          W.literalLocalDebtAt
              quarticSignedPoleCanonicalLocalRadius n
            -
          W.literalSignedCompensationAt
              quarticSignedPoleCanonicalLocalRadius n
          <=
          (4 * W.combinedZeroHeightDefect rho
            +
           ∫ tau : ℝ,
             W.signedOrdinateTest tau * Zeta23.mu tau)
            - eps) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  apply W.completedSignedResidual_lt_target_of_uniform_compensation_gap ht
  exact hC


/-!
## Sharpened cone compensation: keep the exact negative part

The old LocalRemainderDebt charged the entire local cone by absolute remainder.
That is safe but unnecessarily loses the exact negative cone source.  Since the
joint kernel is now known to possess a favorable negative core, split the exact
cone contribution itself into positive and negative parts.
-/

def QuarticFourSignedPolePair.literalConeGainAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalCone t eta rho then
      max (- W.literalOffOrdSource rho) 0
    else
      0

theorem QuarticFourSignedPolePair.literalConeGainAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalConeGainAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalConeGainAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hc : quarticSignedPoleLocalCone t eta rho
    · simp [hc]
    · simp [hc]

theorem real_eq_max_sub_max_neg (x : ℝ) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 <= x
  · simp [max_eq_left hx, max_eq_right (by linarith : -x <= 0)]
  · have hx' : x <= 0 := le_of_not_ge hx
    have hnx : 0 <= -x := by linarith
    simp [max_eq_right hx', max_eq_left hnx]

theorem QuarticFourSignedPolePair.literalConeExactAt_eq_debt_sub_gain
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalConeExactAt eta n
      =
    W.literalConeDebtAt eta n
      - W.literalConeGainAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalConeExactAt
    QuarticFourSignedPolePair.literalConeExactTerm
    QuarticFourSignedPolePair.literalConeDebtAt
    QuarticFourSignedPolePair.literalConeGainAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hc : quarticSignedPoleLocalCone t eta rho
  · simp [hc, real_eq_max_sub_max_neg]
  · simp [hc]

def QuarticFourSignedPolePair.literalGoodRemainderDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocalGood t eta rho then
      |W.literalJointQuarticRemainderOffOrd rho|
    else
      0

theorem QuarticFourSignedPolePair.literalGoodRemainderDebtAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalGoodRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalGoodRemainderDebtAt
  exact Finset.sum_nonneg fun rho _ => by
    by_cases hg : quarticSignedPoleLocalGood t eta rho
    · simp [hg]
    · simp [hg]

theorem QuarticFourSignedPolePair.literalGoodExactAt_add_gain_le_goodRemainderDebt
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalGoodExactAt eta n
      + W.literalGoodQuarticGainAt eta n
      <= W.literalGoodRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalGoodExactAt
    QuarticFourSignedPolePair.literalGoodQuarticGainAt
    QuarticFourSignedPolePair.literalGoodRemainderDebtAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro rho hrho
  have h :=
    W.literalGoodExactTerm_add_gain_le_remainder
      (eta:=eta) ht rho
  by_cases hg : quarticSignedPoleLocalGood t eta rho
  · have hl : quarticSignedPoleLocal t eta rho := hg.1
    simpa [hg, hl] using h
  · simp [QuarticFourSignedPolePair.literalGoodExactTerm, hg]

def QuarticFourSignedPolePair.literalSharpenedLocalDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalConeDebtAt eta n
    + W.literalGoodRemainderDebtAt eta n

def QuarticFourSignedPolePair.literalSharpenedSignedCompensationAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalConeGainAt eta n
    + W.literalGoodQuarticGainAt eta n
    - W.literalFarExactAt eta n

def QuarticFourSignedPolePair.literalSharpenedJointBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalSharpenedLocalDebtAt eta n
    - W.literalSharpenedSignedCompensationAt eta n

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_sharpenedJointBudget
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <= W.literalSharpenedJointBudgetAt eta n := by
  rw [W.literalOffOrdExactAt_eq_cone_add_good_add_far (eta:=eta)]
  rw [W.literalConeExactAt_eq_debt_sub_gain]
  have hg :=
    W.literalGoodExactAt_add_gain_le_goodRemainderDebt
      ht n
  unfold QuarticFourSignedPolePair.literalSharpenedJointBudgetAt
    QuarticFourSignedPolePair.literalSharpenedLocalDebtAt
    QuarticFourSignedPolePair.literalSharpenedSignedCompensationAt
  linarith

theorem QuarticFourSignedPolePair.literalSharpenedLocalDebtAt_nonneg
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    0 <= W.literalSharpenedLocalDebtAt eta n := by
  unfold QuarticFourSignedPolePair.literalSharpenedLocalDebtAt
  exact add_nonneg
    (W.literalConeDebtAt_nonneg n)
    (W.literalGoodRemainderDebtAt_nonneg n)

/--
The sharpened budget is never worse merely because the cone has negative exact
mass: ConeGain is retained as compensation and no absolute cone remainder is
charged separately.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_lt_margin_of_sharpened_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hgap :
      margin + W.literalSharpenedSignedCompensationAt eta n
        - W.literalSharpenedLocalDebtAt eta n > 0) :
    W.literalOffOrdExactAt n < margin := by
  have hbudget :=
    W.literalOffOrdExactAt_le_sharpenedJointBudget ht n
  unfold QuarticFourSignedPolePair.literalSharpenedJointBudgetAt at hbudget
  linarith


/-!
## Global sharpened compensation compiler

This reuses the already-paid exact-source cofinal limit.  No new
representation layer is introduced.
-/

theorem QuarticFourSignedPolePair.globalOffOrd_le_margin_of_eventual_sharpened_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSharpenedSignedCompensationAt eta n
          - W.literalSharpenedLocalDebtAt eta n > 0) :
    (∑' rho : Zeros, W.literalOffOrdSource rho) <= margin := by
  have hfinite :
      ∀ᶠ n : ℕ in atTop,
        W.literalOffOrdExactAt n <= margin := by
    filter_upwards [hgap] with n hn
    exact
      (W.literalOffOrdExactAt_lt_margin_of_sharpened_compensation_gap
        ht n hn).le
  have hlim :=
    W.literalOffOrdExactAt_tendsto_tsum ht
  exact le_of_tendsto hlim hfinite

theorem QuarticFourSignedPolePair.globalSignedLiteralPairSource_le_margin_of_eventual_sharpened_compensation_gap
    {t eta margin : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSharpenedSignedCompensationAt eta n
          - W.literalSharpenedLocalDebtAt eta n > 0) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.signedLiteralPairSourceTerm sigma)
      <= margin := by
  rw [← W.literalOffOrdSource_tsum_eq_signedLiteralPairSource_tsum]
  exact
    W.globalOffOrd_le_margin_of_eventual_sharpened_compensation_gap
      ht hgap

theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_eventual_sharpened_compensation_gap
    {t eta margin : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hgap :
      ∀ᶠ n : ℕ in atTop,
        margin + W.literalSharpenedSignedCompensationAt eta n
          - W.literalSharpenedLocalDebtAt eta n > 0)
    (hmargin :
      margin
        <
      4 * W.combinedZeroHeightDefect rho
        +
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  have htpos : 0 < t := by linarith
  have hsum :=
    W.globalSignedLiteralPairSource_le_margin_of_eventual_sharpened_compensation_gap
      htpos hgap
  rw [W.completedSignedResidual_eq_jointPairSource ht]
  linarith

def QuarticFourSignedPolePair.UniformSharpenedSignedCompensationGap
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      W.literalSharpenedLocalDebtAt
          quarticSignedPoleCanonicalLocalRadius n
        -
      W.literalSharpenedSignedCompensationAt
          quarticSignedPoleCanonicalLocalRadius n
      <=
      W.compensationTargetThreshold rho - eps

theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_uniform_sharpened_compensation_gap
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hC : W.UniformSharpenedSignedCompensationGap rho) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  rcases hC with ⟨eps,heps,N,hN⟩
  let T : ℝ := W.compensationTargetThreshold rho
  let M : ℝ := T - eps/2
  have hgap :
      ∀ᶠ n : ℕ in atTop,
        M
          + W.literalSharpenedSignedCompensationAt
              quarticSignedPoleCanonicalLocalRadius n
          - W.literalSharpenedLocalDebtAt
              quarticSignedPoleCanonicalLocalRadius n
        > 0 := by
    rw [eventually_atTop]
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    dsimp [T, M] at h ⊢
    linarith
  have hmargin :
      M
        <
      4 * W.combinedZeroHeightDefect rho
        +
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau := by
    dsimp [M, T, QuarticFourSignedPolePair.compensationTargetThreshold]
    linarith
  exact
    W.completedSignedResidual_lt_target_of_eventual_sharpened_compensation_gap
      ht hgap hmargin


/-!
## Sharpened budget dominates the conservative budget
-/

theorem QuarticFourSignedPolePair.literalGoodRemainderDebtAt_le_localRemainderDebtAt
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalGoodRemainderDebtAt eta n
      <= W.literalLocalRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalGoodRemainderDebtAt
    QuarticFourSignedPolePair.literalLocalRemainderDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hg : quarticSignedPoleLocalGood t eta rho
  · have hl : quarticSignedPoleLocal t eta rho := hg.1
    simp [hg,hl]
  · by_cases hl : quarticSignedPoleLocal t eta rho
    · simp [hg,hl]
    · simp [hg,hl]

theorem QuarticFourSignedPolePair.literalSharpenedJointBudgetAt_le_jointBudgetAt
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalSharpenedJointBudgetAt eta n
      <= W.literalJointBudgetAt eta n := by
  have hrem :=
    W.literalGoodRemainderDebtAt_le_localRemainderDebtAt
      (eta:=eta) n
  have hgain :=
    W.literalConeGainAt_nonneg (eta:=eta) n
  unfold QuarticFourSignedPolePair.literalSharpenedJointBudgetAt
    QuarticFourSignedPolePair.literalSharpenedLocalDebtAt
    QuarticFourSignedPolePair.literalSharpenedSignedCompensationAt
    QuarticFourSignedPolePair.literalJointBudgetAt
    QuarticFourSignedPolePair.literalLocalDebtAt
    QuarticFourSignedPolePair.literalSignedCompensationAt
  linarith

theorem QuarticFourSignedPolePair.uniformCompensationGap_implies_sharpened
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hC : W.UniformSignedCompensationGap rho) :
    W.UniformSharpenedSignedCompensationGap rho := by
  rcases hC with ⟨eps,heps,N,hN⟩
  refine ⟨eps,heps,N,?_⟩
  intro n hn
  have hold := hN n hn
  have hbud :=
    W.literalSharpenedJointBudgetAt_le_jointBudgetAt
      (eta:=quarticSignedPoleCanonicalLocalRadius) n
  unfold QuarticFourSignedPolePair.literalSharpenedJointBudgetAt at hbud
  unfold QuarticFourSignedPolePair.literalJointBudgetAt at hbud
  exact hbud.trans hold

end Synthesis
