import Synthesis.RiemannZeta23RvMArbitraryWindowDiscrepancy
import Zeta23.GammaFacts.Complete

/-!
# Arbitrary-endpoint zeta-minus-mu cumulative discrepancy

The good-height theorem is the exact contour identity.  The normalized Abel
consumer, however, moves its cutoff continuously and cannot require every
requested endpoint to avoid zero ordinates.

For arbitrary 4 <= A < B:
* choose T1 in [A-1,A] and T2 in [B,B+1] that are good heights;
* apply the exact good-height discrepancy on [T1,T2];
* remove [T1,A] and [B,T2] using the unconditional unit-window local zero count;
* remove the corresponding mu integrals using the proved bound |mu(t)| <= C log(t+3).

This yields an O(log(A+3)+log(B+4)) cumulative actual-minus-mu discrepancy on
the literal zeta carrier, with no good-height premise.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

theorem exists_zetaMuWindowDiscrepancy_arbitrary_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ A B : ℝ,
        max T0 4 <= A ->
        A < B ->
        |zetaMuWindowDiscrepancy A B|
          <= C * (Real.log (A + 3) + Real.log (B + 4)) := by
  obtain ⟨CB, TB, hB⟩ := Zeta23.RvM.backlund_horizontal
  obtain ⟨A0, hA01, hA0⟩ := Zeta23.RvM.zeta_local_zero_count
  obtain ⟨CM, hCM0, hCM⟩ := Zeta23.RvM.mu_le_log Zeta23.gammaFacts
  let C : ℝ :=
    2 * (1 / Real.pi) * |CB|
      + 2 * A0 + 2 * CM + 1
  have hC0 : 0 <= C := by
    dsimp [C]
    positivity
  refine ⟨C, TB + 1, hC0, ?_⟩
  intro A B hA hAB
  have hA4 : 4 <= A := (le_max_right (TB + 1) 4).trans hA
  have hATB : TB + 1 <= A := (le_max_left (TB + 1) 4).trans hA
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := lt_trans hApos hAB
  obtain ⟨T1, hT1mem, hg1⟩ := Zeta23.RvM.exists_goodHeight (A - 1)
  obtain ⟨T2, hT2mem, hg2⟩ := Zeta23.RvM.exists_goodHeight B
  have hT1lo : A - 1 <= T1 := hT1mem.1
  have hT1hi : T1 <= A := by linarith [hT1mem.2]
  have hT2lo : B <= T2 := hT2mem.1
  have hT2hi : T2 <= B + 1 := hT2mem.2
  have hT1one : 1 <= T1 := by linarith
  have hT1TB : TB <= T1 := by linarith
  have hT2TB : TB <= T2 := le_trans hT1TB (by linarith)
  have hT12 : T1 < T2 := by linarith

  have hgoodEq :=
    zetaMuWindowDiscrepancy_eq_zetaHalfContour
      hT1one hT12 hg1 hg2
  have hgoodHC :=
    zetaHalfContour_im_abs_le
      hB hT1TB hT2TB hT1one hT12 hg1 hg2
  have hgood :
      |zetaMuWindowDiscrepancy T1 T2|
        <= (1 / Real.pi)
          * (|CB| * Real.log T1 + Real.pi + |CB| * Real.log T2) := by
    rw [hgoodEq, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
    exact mul_le_mul_of_nonneg_left hgoodHC (by positivity)

  have hNsplit :
      (zetaZeroConfig.N T1 T2 : ℝ)
        =
      (zetaZeroConfig.N T1 A : ℝ)
        + (zetaZeroConfig.N A B : ℝ)
        + (zetaZeroConfig.N B T2 : ℝ) := by
    have e1 := Zeta23.Ncount_add
      (a := T1) (b := A) (c := T2) hT1hi (by linarith)
    have e2 := Zeta23.Ncount_add
      (a := A) (b := B) (c := T2) hAB.le hT2lo
    simpa only [Zeta23.zetaZeroConfig_N] using by
      rw [e1, e2]
      push_cast
      ring

  have hmuInt : ∀ a b : ℝ,
      IntervalIntegrable Zeta23.mu volume a b :=
    fun a b => Zeta23.gammaFacts.smooth.continuous.intervalIntegrable a b
  have hMusplit :
      (∫ tau in T1..T2, Zeta23.mu tau)
        =
      (∫ tau in T1..A, Zeta23.mu tau)
        + (∫ tau in A..B, Zeta23.mu tau)
        + (∫ tau in B..T2, Zeta23.mu tau) := by
    have e1 :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hmuInt T1 A) (hmuInt A B)).symm
    have e2 :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hmuInt T1 B) (hmuInt B T2)).symm
    rw [e2, e1]

  have hDsplit :
      zetaMuWindowDiscrepancy A B
        =
      zetaMuWindowDiscrepancy T1 T2
        - ((zetaZeroConfig.N T1 A : ℝ)
            - ∫ tau in T1..A, Zeta23.mu tau)
        - ((zetaZeroConfig.N B T2 : ℝ)
            - ∫ tau in B..T2, Zeta23.mu tau) := by
    unfold zetaMuWindowDiscrepancy
    rw [hNsplit, hMusplit]
    ring

  have hN1mono :
      zetaZeroConfig.N T1 A <= zetaZeroConfig.N T1 (T1 + 1) := by
    simpa only [Zeta23.zetaZeroConfig_N] using
      Zeta23.Ncount_mono le_rfl (by linarith)
  have hN2mono :
      zetaZeroConfig.N B T2 <= zetaZeroConfig.N B (B + 1) := by
    simpa only [Zeta23.zetaZeroConfig_N] using
      Zeta23.Ncount_mono le_rfl hT2hi
  have hN1 :
      (zetaZeroConfig.N T1 A : ℝ)
        <= A0 * Real.log (A + 3) := by
    calc
      (zetaZeroConfig.N T1 A : ℝ)
        <= (zetaZeroConfig.N T1 (T1 + 1) : ℝ) := by exact_mod_cast hN1mono
      _ <= A0 * Real.log (|T1| + 3) := by
        simpa only [Zeta23.zetaZeroConfig_N] using hA0 T1
      _ <= A0 * Real.log (A + 3) := by
        have hT1pos : 0 < T1 := by linarith
        rw [abs_of_pos hT1pos]
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith) (by linarith))
          (by linarith)
  have hN2 :
      (zetaZeroConfig.N B T2 : ℝ)
        <= A0 * Real.log (B + 3) := by
    calc
      (zetaZeroConfig.N B T2 : ℝ)
        <= (zetaZeroConfig.N B (B + 1) : ℝ) := by exact_mod_cast hN2mono
      _ <= A0 * Real.log (|B| + 3) := by
        simpa only [Zeta23.zetaZeroConfig_N] using hA0 B
      _ = A0 * Real.log (B + 3) := by
        rw [abs_of_pos hBpos]

  have hmu1point :
      ∀ tau ∈ Set.uIoc T1 A,
        |Zeta23.mu tau| <= CM * Real.log (A + 3) := by
    intro tau htau
    rw [Set.uIoc_of_le hT1hi] at htau
    have htau1 : 1 <= tau := le_trans hT1one htau.1.le
    exact (hCM tau htau1).trans
      (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith) (by linarith))
        hCM0.le)
  have hmu2point :
      ∀ tau ∈ Set.uIoc B T2,
        |Zeta23.mu tau| <= CM * Real.log (B + 4) := by
    intro tau htau
    rw [Set.uIoc_of_le hT2lo] at htau
    have htau1 : 1 <= tau := by linarith
    exact (hCM tau htau1).trans
      (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith) (by linarith))
        hCM0.le)
  have hmu1raw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Zeta23.mu) hmu1point
  have hmu2raw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Zeta23.mu) hmu2point
  have hmu1 :
      |∫ tau in T1..A, Zeta23.mu tau|
        <= CM * Real.log (A + 3) := by
    rw [Real.norm_eq_abs] at hmu1raw
    calc
      |∫ tau in T1..A, Zeta23.mu tau|
        <= CM * Real.log (A + 3) * |A - T1| := hmu1raw
      _ <= CM * Real.log (A + 3) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · rw [abs_of_nonneg (by linarith)]
          linarith
        · positivity
      _ = _ := by ring
  have hmu2 :
      |∫ tau in B..T2, Zeta23.mu tau|
        <= CM * Real.log (B + 4) := by
    rw [Real.norm_eq_abs] at hmu2raw
    calc
      |∫ tau in B..T2, Zeta23.mu tau|
        <= CM * Real.log (B + 4) * |T2 - B| := hmu2raw
      _ <= CM * Real.log (B + 4) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · rw [abs_of_nonneg (by linarith)]
          linarith
        · positivity
      _ = _ := by ring

  have hT1log : Real.log T1 <= Real.log (A + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hT2log : Real.log T2 <= Real.log (B + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogA0 : 0 <= Real.log (A + 3) :=
    Real.log_nonneg (by linarith)
  have hlogB0 : 0 <= Real.log (B + 4) :=
    Real.log_nonneg (by linarith)
  have hpiInv : (1 / Real.pi : ℝ) <= 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]

  have hgoodSimple :
      |zetaMuWindowDiscrepancy T1 T2|
        <= |CB| * Real.log (A + 3)
          + 1
          + |CB| * Real.log (B + 4) := by
    calc
      |zetaMuWindowDiscrepancy T1 T2|
        <= (1 / Real.pi)
          * (|CB| * Real.log T1 + Real.pi + |CB| * Real.log T2) := hgood
      _ <=
        |CB| * Real.log (A + 3)
          + 1
          + |CB| * Real.log (B + 4) := by
        have h1 :=
          mul_le_mul_of_nonneg_left hT1log (abs_nonneg CB)
        have h2 :=
          mul_le_mul_of_nonneg_left hT2log (abs_nonneg CB)
        have hp : (1 / Real.pi) * Real.pi = 1 := by
          field_simp
        nlinarith [mul_nonneg (abs_nonneg CB) hlogA0,
          mul_nonneg (abs_nonneg CB) hlogB0]

  rw [hDsplit]
  have htri :
      |zetaMuWindowDiscrepancy T1 T2
        - ((zetaZeroConfig.N T1 A : ℝ)
            - ∫ tau in T1..A, Zeta23.mu tau)
        - ((zetaZeroConfig.N B T2 : ℝ)
            - ∫ tau in B..T2, Zeta23.mu tau)|
      <=
      |zetaMuWindowDiscrepancy T1 T2|
      + ((zetaZeroConfig.N T1 A : ℝ)
          + |∫ tau in T1..A, Zeta23.mu tau|)
      + ((zetaZeroConfig.N B T2 : ℝ)
          + |∫ tau in B..T2, Zeta23.mu tau|) := by
    have hn1 : 0 <= (zetaZeroConfig.N T1 A : ℝ) := by positivity
    have hn2 : 0 <= (zetaZeroConfig.N B T2 : ℝ) := by positivity
    calc
      |zetaMuWindowDiscrepancy T1 T2
        - ((zetaZeroConfig.N T1 A : ℝ)
            - ∫ tau in T1..A, Zeta23.mu tau)
        - ((zetaZeroConfig.N B T2 : ℝ)
            - ∫ tau in B..T2, Zeta23.mu tau)|
        <=
      |zetaMuWindowDiscrepancy T1 T2|
        + |(zetaZeroConfig.N T1 A : ℝ)
            - ∫ tau in T1..A, Zeta23.mu tau|
        + |(zetaZeroConfig.N B T2 : ℝ)
            - ∫ tau in B..T2, Zeta23.mu tau| := by
          exact (abs_sub _ _).trans
            (add_le_add (abs_sub _ _) le_rfl)
      _ <=
      |zetaMuWindowDiscrepancy T1 T2|
      + ((zetaZeroConfig.N T1 A : ℝ)
          + |∫ tau in T1..A, Zeta23.mu tau|)
      + ((zetaZeroConfig.N B T2 : ℝ)
          + |∫ tau in B..T2, Zeta23.mu tau|) := by
          gcongr <;> exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

  have hlogB3 :
      Real.log (B + 3) <= Real.log (B + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hA0nonneg : 0 <= A0 := by linarith
  refine le_trans htri ?_
  have hN2' :
      (zetaZeroConfig.N B T2 : ℝ)
        <= A0 * Real.log (B + 4) :=
    le_trans hN2
      (mul_le_mul_of_nonneg_left hlogB3 hA0nonneg)
  dsimp [C]
  nlinarith [hgoodSimple, hN1, hN2', hmu1, hmu2,
    mul_nonneg (abs_nonneg CB) hlogA0,
    mul_nonneg (abs_nonneg CB) hlogB0,
    mul_nonneg hA0nonneg hlogA0,
    mul_nonneg hA0nonneg hlogB0,
    mul_nonneg hCM0.le hlogA0,
    mul_nonneg hCM0.le hlogB0]

end Synthesis
