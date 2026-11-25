import Integration.Paper9CuspOrderFactorial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! SOURCE-WRITTEN, UNCOMPILED.
Use the actual Paper9 operator and its cusp factorization, not a
replacement order or finite coefficient fixture. No kernel receipt. -/
namespace Integration.Paper9AnalyticGermClosure

open Complex Filter FormalMultilinearSeries
open scoped Topology NNReal
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial

noncomputable section

def L2 (f : ℂ → ℂ) := L (L f)
def L3 (f : ℂ → ℂ) := L (L2 f)
def ode (f : ℂ → ℂ) (q : ℂ) : ℂ :=
  L3 f q-zCoord q*(L3 f q+3/2*L2 f q+23/36*L f q+5/72*f q)

theorem LAnalytic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (L f) 0 :=
  transportUnitAnalytic.mul (analyticAt_id.mul hf.deriv)

theorem Lcongr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    L f =ᶠ[𝓝 (0 : ℂ)] L g := by
  filter_upwards [h.deriv] with q hq
  simp only [L,euler,hq]

theorem LsubLocal (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    L (fun q => f q-g q) =ᶠ[𝓝 (0 : ℂ)] fun q => L f q-L g q := by
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with q h1 h2
  have hd := h1.differentiableAt.hasDerivAt.sub h2.differentiableAt.hasDerivAt
  unfold L euler
  rw [hd.deriv]
  ring

theorem odeSubLocal (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ode (fun q => f q-g q) =ᶠ[𝓝 (0 : ℂ)] fun q => ode f q-ode g q := by
  have h1 := LsubLocal f g hf hg
  have h2 : L2 (fun q => f q-g q) =ᶠ[𝓝 (0 : ℂ)] fun q => L2 f q-L2 g q :=
    (Lcongr h1).trans (LsubLocal (L f) (L g) (LAnalytic f hf) (LAnalytic g hg))
  have h3 : L3 (fun q => f q-g q) =ᶠ[𝓝 (0 : ℂ)] fun q => L3 f q-L3 g q :=
    (Lcongr h2).trans (LsubLocal (L2 f) (L2 g)
      (LAnalytic _ (LAnalytic f hf)) (LAnalytic _ (LAnalytic g hg)))
  filter_upwards [h1,h2,h3] with q hq1 hq2 hq3
  unfold ode
  rw [hq1,hq2,hq3]
  ring

-- All three levels of the actual filtered operator, not just n^3 at 0.
theorem odeFactor (n : ℕ) (w g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hw : w =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*g q) :
    ode w =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*residualUnit (n+1) g q := by
  let a := leadStep (n+1) g
  let b := leadStep (n+1) a
  have ha := leadStepAnalytic (n+1) g hg
  have hb := leadStepAnalytic (n+1) a ha
  have h1 : L w =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*a q :=
    leadTransport n w g (hg.eventually_analyticAt.mono fun _ h => h.differentiableAt) hw
  have h2 : L2 w =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*b q :=
    leadTransport n (L w) a (ha.eventually_analyticAt.mono fun _ h => h.differentiableAt) h1
  have h3 : L3 w =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*leadStep (n+1) b q :=
    leadTransport n (L2 w) b (hb.eventually_analyticAt.mono fun _ h => h.differentiableAt) h2
  filter_upwards [hw,h1,h2,h3] with q h0 h1 h2 h3
  unfold ode residualUnit
  rw [h0,h1,h2,h3]
  change q^(n+1)*leadStep (n+1) b q -
    zCoord q*(q^(n+1)*leadStep (n+1) b q+3/2*(q^(n+1)*b q)+
      23/36*(q^(n+1)*a q)+5/72*(q^(n+1)*g q)) = _
  ring

-- Endpoint-first: any nonzero germ difference has an impossible leading
-- residual. This is an all-order consumer, not a fixed truncation theorem.
theorem zeroGerm (w : ℂ → ℂ) (hw : AnalyticAt ℂ w 0) (h0 : w 0 = 0)
    (hode : ode w =ᶠ[𝓝 (0 : ℂ)] fun _ => 0) :
    w =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
  by_contra hn
  obtain ⟨n,g,hg,hg0,hfact⟩ := hw.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hn
  have hf : w =ᶠ[𝓝 (0 : ℂ)] fun q => q^n*g q := by
    filter_upwards [hfact] with q hq
    simpa [sub_zero,smul_eq_mul] using hq
  cases n with
  | zero =>
    have h := hf.eq_of_nhds
    exact hg0 (by simpa [h0] using h.symm)
  | succ n =>
    exact nonzeroLeadingObstruction (n+1) (Nat.succ_ne_zero n) g hg hg0
      ((odeFactor n w g hg hf).symm.trans hode)

theorem normalizedGermUnique (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h0 : f 0 = g 0)
    (hF : ode f =ᶠ[𝓝 (0 : ℂ)] fun _ => 0)
    (hG : ode g =ᶠ[𝓝 (0 : ℂ)] fun _ => 0) :
    f =ᶠ[𝓝 (0 : ℂ)] g := by
  have hsub := odeSubLocal f g hf hg
  have hz : ode (fun q => f q-g q) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hsub,hF,hG] with q hs h1 h2
    rw [hs,h1,h2,sub_zero]
  have hw := zeroGerm (fun q => f q-g q) (hf.sub hg)
    (sub_eq_zero.mpr h0) hz
  exact hw.mono fun q h => sub_eq_zero.mp h

-- Actual literal coefficient majorant and radius, no estimated ratio.
theorem ratioPositive (n : ℕ) : 0 < ratio n := by unfold ratio; positivity

theorem ratioLTOne (n : ℕ) : ratio n < 1 := by
  let t : ℚ := (n : ℚ)+1
  have ht : 0 < t := by dsimp [t]; positivity
  have h1 : 0 < (n : ℚ)+1/6 := by positivity
  have h2 : 0 < (n : ℚ)+1/2 := by positivity
  have h3 : 0 < (n : ℚ)+5/6 := by positivity
  have ha : (n : ℚ)+1/6 < t := by dsimp [t]; linarith
  have hb : (n : ℚ)+1/2 < t := by dsimp [t]; linarith
  have hc : (n : ℚ)+5/6 < t := by dsimp [t]; linarith
  unfold ratio
  apply (div_lt_iff₀ (pow_pos ht 3)).2
  have h12 : ((n : ℚ)+1/6)*((n : ℚ)+1/2) < t*t :=
    (mul_lt_mul_of_pos_right ha h2).trans (mul_lt_mul_of_pos_left hb ht)
  have h123 := (mul_lt_mul_of_pos_right h12 h3).trans
    (mul_lt_mul_of_pos_left hc (mul_pos ht ht))
  simpa [t,pow_succ] using h123

theorem coeffBand (n : ℕ) : 0 < coeff n ∧ coeff n ≤ 1 := by
  induction n with
  | zero => simp [coeffZero]
  | succ n ih =>
    rw [coeffSucc]
    exact ⟨mul_pos (ratioPositive n) ih.1,
      (mul_le_mul_of_nonneg_right (ratioLTOne n).le ih.1.le).trans
        (by simpa using ih.2)⟩

def hyperSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (fun n => (coeff n : ℂ))

def H : ℂ → ℂ := hyperSeries.sum

theorem hyperRadius : 1 ≤ hyperSeries.radius := by
  have h := hyperSeries.le_radius_of_bound 1 (r := (1 : ℝ≥0)) (fun n => by
    simp only [hyperSeries,ofScalars_norm,NNReal.coe_one,one_pow,mul_one]
    have hc := coeffBand n
    rw [show (coeff n : ℂ) = ((coeff n : ℝ) : ℂ) by norm_cast,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by exact_mod_cast hc.1.le)]
    exact_mod_cast hc.2)
  exact_mod_cast h

theorem HAnalytic (z : ℂ) (hz : ‖z‖ < 1) : AnalyticAt ℂ H z := by
  apply hyperSeries.analyticOnNhd z
  apply Metric.mem_eball_zero_iff.mpr
  exact lt_of_lt_of_le (by exact_mod_cast hz) hyperRadius

theorem HZero : H 0 = 1 := by
  change ofScalarsSum (fun n => (coeff n : ℂ)) (0 : ℂ) = 1
  simp [coeffZero]

theorem HSource (z : ℂ) : H z = ∑' n, (coeff n : ℂ)*z^n := by
  exact (ofScalars_sum_eq (fun n => (coeff n : ℂ)) z).trans
    (tsum_congr fun _ => smul_eq_mul _ _)

end
end Integration.Paper9AnalyticGermClosure
