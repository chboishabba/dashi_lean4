import Integration.Paper9OriginalCMChartWeld
import Mathlib.Analysis.SpecificLimits.Normed

/-! SOURCE-WRITTEN, UNCOMPILED. Recover the original 90/30 Machin
prefixes and integer sqrt endpoints of the CM -163 dyadic checker.
Use the existing faithful Machin evaluation, pinned Real.hasSum_arctan
and Antitone alternating partial-sum bounds. No new pi definition.
-/
namespace Integration.Paper9CMOriginalMachinWindow
open scoped BigOperators Topology
open Filter
open Integration.BishopVendoredMachinPiSemantics
open Integration.BishopVendoredRealEvaluation
open Integration.Paper9ActualCMPoint

noncomputable section

def magnitude (x : ℝ) (n : ℕ) : ℝ :=
  x^(2*n+1)/(2*n+1:ℕ)

theorem magnitudeAntitone (x : ℝ) (hx : 0≤x) (hx' : x≤1) :
    Antitone (magnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : 0≤x^(2*n+1) := pow_nonneg hx _
  have hs : x^2≤1 := by nlinarith
  have hpow : x^(2*(n+1)+1)≤x^(2*n+1) := by
    rw [show 2*(n+1)+1=2*n+1+2 by omega,pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hs hp]
  unfold magnitude
  calc
    _ ≤ x^(2*n+1)/((2*(n+1)+1:ℕ):ℝ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left hp (by positivity)
      push_cast
      linarith

def prefix (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1:ℝ)^k*magnitude x k

-- Exact even/odd bracketing from the already-owned alternating theorem.
theorem atanBracket (x : ℝ) (hx : 0≤x) (h1 : x<1) (k : ℕ) :
    prefix x (2*k)≤Real.arctan x ∧ Real.arctan x≤prefix x (2*k+1) := by
  have hsum := (Real.hasSum_arctan (x:=x) (by simpa [Real.norm_eq_abs,abs_of_nonneg hx] using h1)).tendsto_sum_nat
  have ht : Tendsto (prefix x) atTop (𝓝 (Real.arctan x)) := by
    simpa [prefix,magnitude,mul_div_assoc] using hsum
  have ha := magnitudeAntitone x hx h1.le
  exact ⟨ha.alternating_series_le_tendsto ht k,
    ha.tendsto_le_alternating_series ht k⟩

end

-- Finite exact rational prefix of the ORIGINAL certificate.
def prefixRat (d n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1:ℚ)^k/
    (((2*k+1:ℕ):ℚ)*(d:ℚ)^(2*k+1))
def piLowerRat : ℚ := 16*prefixRat 5 90-4*prefixRat 239 31
def piUpperRat : ℚ := 16*prefixRat 5 91-4*prefixRat 239 30
def scale : ℕ := 2^128
def piLo : ℕ := 1069028584064966747859680373161870783300
def piHi : ℕ := 1069028584064966747859680373161870783301
def sqrtLo : ℕ := 4344434433350621975299947493401713860084
def sqrtHi : ℕ := 4344434433350621975299947493401713860085

noncomputable section

theorem prefixCast (d n : ℕ) (hd : d≠0) :
    (prefixRat d n:ℝ)=prefix (1/(d:ℝ)) n := by
  unfold prefixRat prefix magnitude
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [div_pow,one_pow]
  field_simp [show (d:ℝ)≠0 by exact_mod_cast hd] <;> ring

theorem actualPiBracket :
    (piLowerRat:ℝ)≤Real.pi ∧ Real.pi≤(piUpperRat:ℝ) := by
  have ha := atanBracket (1/5) (by norm_num) (by norm_num) 45
  have hb := atanBracket (1/239) (by norm_num) (by norm_num) 15
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  change 4*Real.arctan (1/5)-Real.arctan (1/239)=Real.pi/4 at hm
  change prefix (1/5) 90≤_ ∧ _≤prefix (1/5) 91 at ha
  change prefix (1/239) 30≤_ ∧ _≤prefix (1/239) 31 at hb
  unfold piLowerRat piUpperRat
  push_cast
  rw [prefixCast 5 90 (by decide),prefixCast 239 31 (by decide),
    prefixCast 5 91 (by decide),prefixCast 239 30 (by decide)]
  exact ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩

-- The original rational-to-dyadic floor/ceil checks must be executed
-- by the actual Lean kernel/decider. No external receipt is a proof.
def piRoundOK : Prop :=
  (piLo:ℚ)/(scale:ℚ)≤piLowerRat ∧ piUpperRat≤(piHi:ℚ)/(scale:ℚ)

instance : Decidable piRoundOK := by unfold piRoundOK; infer_instance

theorem actualDyadicPi (h : piRoundOK) :
    (piLo:ℝ)/(scale:ℝ)≤Real.pi ∧ Real.pi≤(piHi:ℝ)/(scale:ℝ) := by
  have hl : (piLo:ℝ)/(scale:ℝ)≤(piLowerRat:ℝ) := by exact_mod_cast h.1
  have hu : (piUpperRat:ℝ)≤(piHi:ℝ)/(scale:ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans actualPiBracket.1,actualPiBracket.2.trans hu⟩

theorem sourceDyadicPi (A : VendoredArithmeticMirror) (M : VendoredMachinSourceMirror A)
    (h : piRoundOK) :
    (piLo:ℝ)/(scale:ℝ)≤eval (machinPiB A M) ∧
      eval (machinPiB A M)≤(piHi:ℝ)/(scale:ℝ) := by
  rw [eval_machinPi_eq_real_pi]
  exact actualDyadicPi h

def sqrtRoundOK : Prop :=
  sqrtLo^2≤163*scale^2 ∧ 163*scale^2≤sqrtHi^2

instance : Decidable sqrtRoundOK := by unfold sqrtRoundOK; infer_instance

theorem actualDyadicSqrt (h : sqrtRoundOK) :
    (sqrtLo:ℝ)/(scale:ℝ)≤root163 ∧ root163≤(sqrtHi:ℝ)/(scale:ℝ) := by
  have hs : 0<(scale:ℝ) := by norm_num [scale]
  have hl : (sqrtLo:ℝ)^2≤163*(scale:ℝ)^2 := by exact_mod_cast h.1
  have hu : 163*(scale:ℝ)^2≤(sqrtHi:ℝ)^2 := by exact_mod_cast h.2
  have hr : 0≤root163 := by linarith [root163_gt]
  have he : (root163*(scale:ℝ))^2=163*(scale:ℝ)^2 := by rw [mul_pow,root163_sq]
  have hpos : 0≤root163*(scale:ℝ) := mul_nonneg hr hs.le
  constructor
  · apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg ((sqrtLo:ℝ)-root163*(scale:ℝ))]
  · apply (le_div_iff₀ hs).2
    nlinarith [sq_nonneg ((sqrtHi:ℝ)-root163*(scale:ℝ))]

end
end Integration.Paper9CMOriginalMachinWindow
