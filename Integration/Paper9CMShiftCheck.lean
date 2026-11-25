import Integration.Paper9ExecutableCM163

/-! SOURCE-WRITTEN, UNCOMPILED.
Reflect exact literal shifted integer dominance into the ORIGINAL
real half-unit isolation theorem. The only analytic premise left in
this consumer is the actual CM enclosure (besides the diagonal gate).
-/
namespace Integration.Paper9CMShiftCheck
open scoped BigOperators
open Integration.Paper9ActualCMRoot
open Integration.Paper9CM163LiteralPacket
open Integration.Paper9ExecutableCM163
open Integration.Paper9ActualCMPoint

def dominanceZ : Prop :=
  (∑ i ∈ Finset.range 80, |shiftedZ (i+3)|*2^(79-i)) <
    |shiftedZ 2|*2^80

instance : Decidable dominanceZ := by unfold dominanceZ; infer_instance

def shiftOK : Bool := decide (shiftedZ 0=0 ∧ shiftedZ 1=0 ∧ dominanceZ)

theorem dominanceReal (h : dominanceZ) :
    (∑ i ∈ Finset.range 80,
      |(shiftedZ (i+3):ℝ)|*(1/2:ℝ)^(i+1)) < |(shiftedZ 2:ℝ)| := by
  have hz : (∑ i ∈ Finset.range 80,
      |(shiftedZ (i+3):ℝ)|*(2:ℝ)^(79-i)) <
      |(shiftedZ 2:ℝ)|*2^80 := by
    unfold dominanceZ at h
    exact_mod_cast h
  have hm : (∑ i ∈ Finset.range 80,
      |(shiftedZ (i+3):ℝ)|*(1/2:ℝ)^(i+1))*2^80 =
      ∑ i ∈ Finset.range 80, |(shiftedZ (i+3):ℝ)|*(2:ℝ)^(79-i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i<80 := Finset.mem_range.mp hi
    have he : (2:ℝ)^80=2^(i+1)*2^(79-i) := by
      rw [← pow_add,show i+1+(79-i)=80 by omega]
    rw [he,div_pow,one_pow]
    field_simp
  apply (mul_lt_mul_right₀ (by positivity : (0:ℝ)<2^80)).mp
  rw [hm]
  exact hz

theorem rootOfChecks (hu : unitOK=true) (hd : diagOK=true)
    (hs : shiftOK=true)
    (hdyadic : |(Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau).re-(K:ℝ)|≤1/2) :
    Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau=(K:ℂ) := by
  have h : shiftedZ 0=0 ∧ shiftedZ 1=0 ∧ dominanceZ := of_decide_eq_true hs
  exact cmRootFromDiagonal (diagonalOfCheck hu hd) h.1 h.2.1
    (dominanceReal h.2.2) hdyadic

end Integration.Paper9CMShiftCheck
