import Integration.Paper9ActualDeltaWindow
import Integration.BishopVendoredExponentialSemantics

/-! SOURCE-WRITTEN, UNCOMPILED. Original exponential series with a
finite-prefix comparison at the actual signed CM point. No new exp
definition. Explicit finite predicates, not external receipts as proofs. -/
namespace Integration.Paper9CMExpWindow
open Filter
open scoped BigOperators Topology
open Integration.Paper9CMOriginalMachinWindow
open Integration.Paper9CMNormalizedCuspWindow
open Integration.Paper9ActualDeltaWindow
open Integration.Paper9ActualCMPoint
open Integration.Paper9CMShiftCheck
open Integration.Paper9ExecutableCM163
open Integration.Paper9ActualCMRoot

noncomputable section

def expTerm (x : ℝ) (n : ℕ) : ℝ := x^n/(n.factorial:ℝ)
def prefixR (x : ℝ) : ℝ := ∑ n ∈ Finset.range 180, expTerm x n

theorem expTermNonneg (x : ℝ) (hx : 0≤x) (n : ℕ) :
    0≤expTerm x n := by unfold expTerm; positivity

theorem expHasSum (x : ℝ) : HasSum (expTerm x) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem termHalf (x : ℝ) (hx : 0≤x) (h : 2*x≤181) (n : ℕ) :
    expTerm x (180+n+1)≤expTerm x (180+n)/2 := by
  have he : expTerm x (180+n+1) =
      expTerm x (180+n)*x/(181+n:ℕ) := by
    unfold expTerm
    rw [pow_succ,Nat.factorial_succ]
    push_cast
    field_simp <;> ring
  rw [he]
  have hn : (0:ℝ)<(181+n:ℕ) := by positivity
  have hx' : 2*x≤(181+n:ℕ) := by push_cast; linarith
  apply (div_le_iff₀ hn).2
  nlinarith [mul_le_mul_of_nonneg_left hx' (expTermNonneg x hx (180+n))]

theorem geometricTerm (x : ℝ) (hx : 0≤x) (h : 2*x≤181) (n : ℕ) :
    expTerm x (180+n)≤expTerm x 180*(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 180+(n+1)=180+n+1 by omega,pow_succ]
    calc
      _ ≤ expTerm x (180+n)/2 := termHalf x hx h n
      _ ≤ _ := by linarith

theorem expPrefixBracket (x : ℝ) (hx : 0≤x) (hh : 2*x≤181) :
    prefixR x≤Real.exp x ∧
      Real.exp x≤prefixR x+2*expTerm x 180 := by
  have hs := expHasSum x
  have ht : Summable (fun n : ℕ => expTerm x (n+180)) :=
    (summable_nat_add_iff 180).mpr hs.summable
  have he := hs.unique ((hasSum_nat_add_iff' 180).mp ht.hasSum)
  have hg : HasSum (fun n : ℕ => expTerm x 180*(1/2:ℝ)^n)
      (2*expTerm x 180) := by
    convert (hasSum_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)).mul_left
      (expTerm x 180) using 1 <;> ring
  have hl : 0≤∑' n : ℕ, expTerm x (n+180) :=
    tsum_nonneg (fun n => expTermNonneg x hx _)
  have hu := tsum_le_tsum (fun n => by
    simpa [Nat.add_comm] using geometricTerm x hx hh n) ht hg.summable
  rw [hg.tsum_eq] at hu
  unfold prefixR
  constructor <;> linarith

theorem prefixCast (x : ℚ) : (expPrefix x:ℝ)=prefixR (x:ℝ) := by
  unfold expPrefix prefixR expTerm
  push_cast
  rfl

theorem upperCast (x : ℚ) :
    (expUpper x:ℝ)=prefixR (x:ℝ)+2*expTerm (x:ℝ) 180 := by
  unfold expUpper
  push_cast
  rw [prefixCast]
  unfold expTerm
  ring

theorem actualArgumentBracket (hp : piRoundOK) (hs : sqrtRoundOK) :
    (xLo:ℝ)≤Real.pi*root163 ∧ Real.pi*root163≤(xHi:ℝ) := by
  obtain ⟨hpl,hph⟩ := actualDyadicPi hp
  obtain ⟨hsl,hsh⟩ := actualDyadicSqrt hs
  have h0 : 0≤(piLo:ℝ)/(scale:ℝ) := by positivity
  have h1 : 0≤(sqrtLo:ℝ)/(scale:ℝ) := by positivity
  have hp0 : 0≤Real.pi := Real.pi_pos.le
  have hs0 : 0≤root163 := by linarith [root163_gt]
  constructor
  · have h := mul_le_mul hpl hsl h1 hp0
    unfold xLo
    push_cast
    convert h using 1 <;> ring
  · have h := mul_le_mul hph hsh hs0 (show 0≤(piHi:ℝ)/(scale:ℝ) by positivity)
    unfold xHi
    push_cast
    convert h using 1 <;> ring

theorem actualExpQuarter (hp : piRoundOK) (hs : sqrtRoundOK)
    (hw : expWindowOK) :
    |Real.exp (Real.pi*root163)-((640320:ℝ)^3+744)|≤1/4 := by
  obtain ⟨h0,h01,hhalf,hlo,hhi⟩ := hw
  have hl0 : 0≤(xLo:ℝ) := by exact_mod_cast h0
  have hlh : (xLo:ℝ)≤(xHi:ℝ) := by exact_mod_cast h01
  have hh : 2*(xHi:ℝ)≤181 := by exact_mod_cast hhalf.le
  have hL := (expPrefixBracket _ hl0 (by linarith)).1
  have hH := (expPrefixBracket _ (hl0.trans hlh) hh).2
  obtain ⟨ha,hb⟩ := actualArgumentBracket hp hs
  have h1 := hL.trans (Real.exp_le_exp.mpr ha)
  have h2 := (Real.exp_le_exp.mpr hb).trans hH
  have hlo' : (640320:ℝ)^3+744-1/4 < (expPrefix xLo:ℝ) := by exact_mod_cast hlo
  have hhi' : (expUpper xHi:ℝ)<(640320:ℝ)^3+744+1/4 := by exact_mod_cast hhi
  rw [prefixCast] at hlo'
  rw [upperCast] at hhi'
  rw [abs_le]
  constructor <;> linarith

local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

-- A4 endpoint with only finite reflection predicates. No free
-- analytic enclosure hypothesis. A3c checks remain explicit.
theorem rootFromOriginalFiniteChecks
    (hu : unitOK=true) (hd : diagOK=true) (hz : shiftOK=true)
    (hp : piRoundOK) (hs : sqrtRoundOK) (hw : expWindowOK) :
    j cmTau=(K:ℂ) :=
  rootFromCuspChecks hu hd hz (actualExpQuarter hp hs hw) actualCMFourierQuarter

end
end Integration.Paper9CMExpWindow
