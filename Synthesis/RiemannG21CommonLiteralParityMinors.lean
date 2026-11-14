import Mathlib.Tactic
import Synthesis.RiemannG21CommonParityRadius
import Synthesis.RiemannG21LiteralOddMinorExists
import Synthesis.RiemannG21EvenFiniteMinorExists

/-!
# Same-radius literal G21 even and odd parity minors

The symmetric four-sample G21 carrier uses one pair of positive radii `r,2r`
(and their negatives).  Separate existence theorems for the even and odd
sectors are therefore insufficient unless they can be synchronized.

This owner combines the two positive continuum ratio gaps with the common
small-radius compiler and then applies both quantitative determinant closures
at that same radius.  Under the literal taper plateau/nonnegativity and the
required moment integrability receipts, it produces

  exists r, 0<r<=1 and D_odd(r,2r)<0 and D_even(r,2r)<0.

This is the finite analytic statement needed by the existing symmetric parity
block reduction before the nuisance-space/pole-quotient transversality weld.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

private theorem oddMomentNonneg_common
    {w : ℝ → ℝ} {R y : ℝ}
    (hy : 0 < y) (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= oddN3 R w y ∧ 0 <= oddN5 R w y := by
  constructor
  · unfold oddN3 momentQ
    apply integral_nonneg_of_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hwc : 0 <= g21ClippedWeight R w x := by
        simpa [g21ClippedWeight, hx] using hw x hx
      have hs : 0 <= Real.sinh (y*x) :=
        (Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx.1)
      unfold oddHeightWeight
      positivity
    · simp [oddHeightWeight, g21ClippedWeight, hx]
  · unfold oddN5
    apply integral_nonneg_of_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hwc : 0 <= g21ClippedWeight R w x := by
        simpa [g21ClippedWeight, hx] using hw x hx
      have hs : 0 <= Real.sinh (y*x) :=
        (Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx.1)
      unfold oddHeightWeight
      positivity
    · simp [oddHeightWeight, g21ClippedWeight, hx]

private theorem evenMomentNonneg_common
    {w : ℝ → ℝ} {R y : ℝ}
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= evenM2 R w y ∧ 0 <= evenM4 R w y := by
  constructor
  · unfold evenM2
    apply integral_nonneg_of_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hwc : 0 <= g21ClippedWeight R w x := by
        simpa [g21ClippedWeight, hx] using hw x hx
      unfold evenHeightWeight
      positivity
    · simp [evenHeightWeight, g21ClippedWeight, hx]
  · unfold evenM4
    apply integral_nonneg_of_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hwc : 0 <= g21ClippedWeight R w x := by
        simpa [g21ClippedWeight, hx] using hw x hx
      unfold evenHeightWeight
      positivity
    · simp [evenHeightWeight, g21ClippedWeight, hx]

/-- One literal four-sample radius with both parity minors strictly nonzero. -/
theorem exists_commonRadius_literalParityMinors_neg
    {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (ho1a : Integrable (oddHeightWeight R w a) volume)
    (ho3a : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (ho5a : Integrable (fun x => x^4 * oddHeightWeight R w a x) volume)
    (ho1p : Integrable (oddHeightWeight R w p) volume)
    (ho3p : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume)
    (ho5p : Integrable (fun x => x^4 * oddHeightWeight R w p x) volume)
    (he0a : Integrable (evenHeightWeight R w a) volume)
    (he2a : Integrable (fun x => x^2 * evenHeightWeight R w a x) volume)
    (he4a : Integrable (fun x => x^4 * evenHeightWeight R w a x) volume)
    (he0p : Integrable (evenHeightWeight R w p) volume)
    (he2p : Integrable (fun x => x^2 * evenHeightWeight R w p x) volume)
    (he4p : Integrable (fun x => x^4 * evenHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      literalOddFiniteDeterminant R w a p r < 0 ∧
      literalEvenFiniteDeterminant R w a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  have hR : 0 <= R := (hl.trans (hlm.trans (hmr.trans hrR))).le

  -- Literal odd continuum gap.
  have hoN1a : 0 < oddN1 R w a :=
    oddN1_pos_of_positivePlateau ha hl (hlm.trans hmr) hrR hwNonneg hwPos ho1a
  have hoN1p : 0 < oddN1 R w p :=
    oddN1_pos_of_positivePlateau hp hl (hlm.trans hmr) hrR hwNonneg hwPos ho1p
  have hoCross :
      0 < oddN1 R w a * oddN3 R w p - oddN3 R w a * oddN1 R w p := by
    simpa [oddN1, oddN3, oddHeightWeight, g21OddMomentWeight,
      mul_assoc, mul_left_comm, mul_comm] using
      (oddMomentCrossProduct_pos_of_positivePlateau
        ha hap hl hlm hmr hrR hwNonneg hwPos ho1a ho1p ho3a ho3p)
  have hoGap : 0 < oddRatio R w p - oddRatio R w a := by
    apply sub_pos.mpr
    unfold oddRatio
    apply oddRatioGap_of_crossProduct hoN1a hoN1p
    linarith

  -- Literal even continuum gap.
  have heM0a : 0 < evenM0 R w a :=
    evenM0_pos_of_positivePlateau hl (hlm.trans hmr) hrR hwNonneg hwPos he0a
  have heM0p : 0 < evenM0 R w p :=
    evenM0_pos_of_positivePlateau hl (hlm.trans hmr) hrR hwNonneg hwPos he0p
  have heCross :
      0 < evenM0 R w a * evenM2 R w p - evenM2 R w a * evenM0 R w p := by
    simpa [evenM0, evenM2, evenHeightWeight, moment0, momentQ,
      mul_assoc, mul_left_comm, mul_comm] using
      (evenMomentCrossProduct_pos_of_positivePlateau
        ha hap hl hlm hmr hrR hwNonneg hwPos he0a he0p he2a he2p)
  have heGap : 0 < evenRatio R w p - evenRatio R w a := by
    apply sub_pos.mpr
    unfold evenRatio
    apply oddRatioGap_of_crossProduct heM0a heM0p
    linarith

  obtain ⟨r,hr,hr1,hoGate,heGate⟩ :=
    exists_unit_commonParityRadiusGate hR hoGap heGap

  -- Odd support moments and actual remainder bounds at the common radius.
  have hoNonA := oddMomentNonneg_common ha hwNonneg
  have hoNonP := oddMomentNonneg_common hp hwNonneg
  have hoSuppA := literalOddSupportMomentBounds hR ha hwNonneg ho1a ho3a ho5a
  have hoSuppP := literalOddSupportMomentBounds hR hp hwNonneg ho1p ho3p ho5p
  have hoa1raw := oddSixScaledRemainder_le_N5 (r:=r) ha hwNonneg ho5a
  have hoa2raw := oddSixScaledRemainder_le_N5 (r:=2*r) ha hwNonneg ho5a
  have hop1raw := oddSixScaledRemainder_le_N5 (r:=r) hp hwNonneg ho5p
  have hop2raw := oddSixScaledRemainder_le_N5 (r:=2*r) hp hwNonneg ho5p
  have h2r : 0 < 2*r := by positivity
  have hoa1 : |oddSixScaledRemainder R w a r| <= r^5*(oddN5 R w a/20) := by
    simpa [abs_of_pos hr] using hoa1raw
  have hop1 : |oddSixScaledRemainder R w p r| <= r^5*(oddN5 R w p/20) := by
    simpa [abs_of_pos hr] using hop1raw
  have hoa2 : |oddSixScaledRemainder R w a (2*r)| <= 32*r^5*(oddN5 R w a/20) := by
    rw [abs_of_pos h2r] at hoa2raw
    nlinarith
  have hop2 : |oddSixScaledRemainder R w p (2*r)| <= 32*r^5*(oddN5 R w p/20) := by
    rw [abs_of_pos h2r] at hop2raw
    nlinarith
  have hOddNeg := oddActualDeterminant_neg_of_supportGate hR hr hr1
    hoN1a hoNonA.1 hoNonA.2 hoN1p hoNonP.1 hoNonP.2
    hoSuppA.1 hoSuppA.2 hoSuppP.1 hoSuppP.2 hoGate
    hoa1 hoa2 hop1 hop2

  -- Even support moments and actual remainder bounds at the same radius.
  have heNonA := evenMomentNonneg_common (y:=a) hwNonneg
  have heNonP := evenMomentNonneg_common (y:=p) hwNonneg
  have heSuppA := literalEvenSupportMomentBounds hR hwNonneg he0a he2a he4a
  have heSuppP := literalEvenSupportMomentBounds hR hwNonneg he0p he2p he4p
  have hea1raw := evenCosRemainder_le_M4 (r:=r) hwNonneg he4a
  have hea2raw := evenCosRemainder_le_M4 (r:=2*r) hwNonneg he4a
  have hep1raw := evenCosRemainder_le_M4 (r:=r) hwNonneg he4p
  have hep2raw := evenCosRemainder_le_M4 (r:=2*r) hwNonneg he4p
  have hea1 : |evenCosRemainder R w a r| <= r^4*(evenM4 R w a/24) := by
    simpa [abs_of_pos hr] using hea1raw
  have hep1 : |evenCosRemainder R w p r| <= r^4*(evenM4 R w p/24) := by
    simpa [abs_of_pos hr] using hep1raw
  have hea2 : |evenCosRemainder R w a (2*r)| <= 16*r^4*(evenM4 R w a/24) := by
    rw [abs_of_pos h2r] at hea2raw
    nlinarith
  have hep2 : |evenCosRemainder R w p (2*r)| <= 16*r^4*(evenM4 R w p/24) := by
    rw [abs_of_pos h2r] at hep2raw
    nlinarith
  have hEvenNeg := evenActualDeterminant_neg_of_supportGate hR hr hr1
    heM0a heNonA.1 heNonA.2 heM0p heNonP.1 heNonP.2
    heSuppA.1 heSuppA.2 heSuppP.1 heSuppP.2 heGate
    hea1 hea2 hep1 hep2

  refine ⟨r,hr,hr1,?_,?_⟩
  · unfold literalOddFiniteDeterminant
    exact hOddNeg
  · unfold literalEvenFiniteDeterminant
    exact hEvenNeg

end Synthesis
