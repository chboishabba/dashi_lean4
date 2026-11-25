import Integration.Paper9RootODE
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! SOURCE-WRITTEN, UNCOMPILED.
Original factorial coefficients, actual convergent scalar series,
and differentiated diagonal of the actual formal multilinear series.
For the selected CM disk only |z|<1/2 is needed. No numerical fitting. -/
namespace Integration.Paper9HypergeometricSeriesODE

open Complex Filter FormalMultilinearSeries
open scoped Topology NNReal
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9AnalyticGermClosure
open Integration.Paper9RootODE

noncomputable section

def jetCoeff (d n : ℕ) : ℂ := (n : ℂ)^d * (coeff n : ℂ)
def jetSeries (d : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (jetCoeff d)
def jet (d : ℕ) : ℂ → ℂ := (jetSeries d).sum

theorem jetZeroOrder : jet 0 = H := by
  unfold jet H jetSeries hyperSeries
  congr 2
  funext n
  simp [jetCoeff]

-- Elementary uniform bound for the first three weighted coefficient
-- streams at radius 1/2. This avoids a new convergence authority.
theorem cubeBound (n : ℕ) : (n+1)^3 ≤ 16*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases h : n < 3
    · interval_cases n <;> norm_num
    · have hn : 3 ≤ n := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
      have hstep : (3+k+2)^3 ≤ 2*(3+k+1)^3 := by
        have he : (3+k+2)^3+(k^3+9*k^2+21*k+3) = 2*(3+k+1)^3 := by ring
        omega
      calc
        (3+k+1+1)^3 ≤ 2*(3+k+1)^3 := by simpa [Nat.add_assoc] using hstep
        _ ≤ 2*(16*2^(3+k)) := Nat.mul_le_mul_left 2 ih
        _ = 16*2^(3+k+1) := by rw [pow_succ]; ring

theorem jetCoeffBound (d n : ℕ) (hd : d ≤ 3) :
    ‖jetCoeff d n‖ ≤ 16 * (2 : ℝ)^n := by
  have hc := coeffBand n
  have hn : ‖(coeff n : ℂ)‖ ≤ 1 := by
    rw [show (coeff n : ℂ) = ((coeff n : ℝ) : ℂ) by norm_cast,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by exact_mod_cast hc.1.le)]
    exact_mod_cast hc.2
  unfold jetCoeff
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    (n : ℝ)^d * ‖(coeff n : ℂ)‖ ≤ (n : ℝ)^d :=
      mul_le_of_le_one_right (by positivity) hn
    _ ≤ ((n : ℝ)+1)^3 := by
      calc
        (n : ℝ)^d ≤ ((n : ℝ)+1)^d := by gcongr; positivity
        _ ≤ ((n : ℝ)+1)^3 := pow_le_pow_right₀ (by positivity) hd
    _ ≤ _ := by exact_mod_cast cubeBound n

theorem jetRadius (d : ℕ) (hd : d ≤ 3) :
    (1/2 : ℝ≥0∞) ≤ (jetSeries d).radius := by
  have h := (jetSeries d).le_radius_of_bound 16 (r := (1/2 : ℝ≥0)) (fun n => by
    simp only [jetSeries,ofScalars_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    calc
      ‖jetCoeff d n‖*(1/2 : ℝ)^n ≤
        (16*(2 : ℝ)^n)*(1/2 : ℝ)^n :=
          mul_le_mul_of_nonneg_right (jetCoeffBound d n hd) (by positivity)
      _ = 16 := by rw [mul_assoc,← mul_pow]; norm_num)
  simpa using h

theorem jetMem (d : ℕ) (hd : d ≤ 3) (z : ℂ) (hz : ‖z‖ < 1/2) :
    z ∈ Metric.eball (0 : ℂ) (jetSeries d).radius := by
  apply Metric.mem_eball_zero_iff.mpr
  exact lt_of_lt_of_le (by exact_mod_cast hz) (jetRadius d hd)

theorem jetAnalytic (d : ℕ) (hd : d ≤ 3) (z : ℂ) (hz : ‖z‖ < 1/2) :
    AnalyticAt ℂ (jet d) z :=
  (jetSeries d).analyticOnNhd z (jetMem d hd z hz)

theorem jetHasSum (d : ℕ) (hd : d ≤ 3) (z : ℂ) (hz : ‖z‖ < 1/2) :
    HasSum (fun n => jetCoeff d n*z^n) (jet d z) := by
  simpa [jetSeries,jet,ofScalars_apply_eq,smul_eq_mul] using
    (jetSeries d).hasSum (jetMem d hd z hz)

-- Evaluating the true derivative multilinear series at z, not at 1,
-- is exactly the Euler q-factor. All source orders are retained.
theorem jetEuler (d : ℕ) (hd : d < 3) (z : ℂ) (hz : ‖z‖ < 1/2) :
    z*deriv (jet d) z = jet (d+1) z := by
  have hpos : 0 < (jetSeries d).radius :=
    lt_of_lt_of_le (by norm_num) (jetRadius d hd.le)
  have hp := (jetSeries d).hasFPowerSeriesOnBall hpos
  have h := hp.fderiv.hasSum (jetMem d hd.le z hz)
  have he := h.mapL (ContinuousLinearMap.apply ℂ ℂ z)
  have he' : HasSum (fun n => jetCoeff (d+1) (n+1)*z^(n+1))
      (z*deriv (jet d) z) := by
    convert he using 1
    · funext n
      change _ = (jetSeries d).derivSeries n (fun _ => z) z
      rw [derivSeries_apply_diag]
      simp [jetSeries,ofScalars_apply_eq,smul_eq_mul,nsmul_eq_mul,jetCoeff,pow_succ]
      ring
    · simp [zero_add,jet,fderiv_eq_deriv_mul,mul_comm]
  have hs := jetHasSum (d+1) (by omega) z hz
  have hshift := hs.summable.tsum_eq_zero_add
  rw [hs.tsum_eq,he'.tsum_eq] at hshift
  have hzero : jetCoeff (d+1) 0 = 0 := by simp [jetCoeff]
  simp [hzero] at hshift
  exact hshift.symm

theorem weightedSucc (n : ℕ) :
    jetCoeff 3 (n+1) = jetCoeff 3 n + 3/2*jetCoeff 2 n +
      23/36*jetCoeff 1 n + 5/72*jetCoeff 0 n := by
  have hn : (n : ℚ)+1 ≠ 0 := by positivity
  have h : ((n : ℚ)+1)^3*coeff (n+1) =
      ((n : ℚ)+1/6)*((n : ℚ)+1/2)*((n : ℚ)+5/6)*coeff n := by
    rw [coeffSucc]
    unfold ratio
    field_simp [hn] <;> ring
  have h' : ((n : ℂ)+1)^3*(coeff (n+1) : ℂ) =
      ((n : ℂ)+1/6)*((n : ℂ)+1/2)*((n : ℂ)+5/6)*(coeff n : ℂ) := by
    exact_mod_cast h
  unfold jetCoeff
  push_cast
  linear_combination h'

-- The shifted series and the combined unshifted series are the same
-- exact summable stream. Degree zero of the third Euler jet is zero.
theorem hyperODEJets (z : ℂ) (hz : ‖z‖ < 1/2) :
    jet 3 z = z*(jet 3 z+3/2*jet 2 z+23/36*jet 1 z+5/72*jet 0 z) := by
  have h0 := jetHasSum 0 (by decide) z hz
  have h1 := jetHasSum 1 (by decide) z hz
  have h2 := jetHasSum 2 (by decide) z hz
  have h3 := jetHasSum 3 (by decide) z hz
  have hs := (((h3.add (h2.mul_left (3/2 : ℂ))).add
      (h1.mul_left (23/36 : ℂ))).add (h0.mul_left (5/72 : ℂ))).mul_left z
  have hshift : HasSum (fun n => jetCoeff 3 (n+1)*z^(n+1))
      (z*(jet 3 z+3/2*jet 2 z+23/36*jet 1 z+5/72*jet 0 z)) := by
    convert hs using 1
    funext n
    rw [weightedSucc,pow_succ]
    ring
  have h := h3.summable.tsum_eq_zero_add
  rw [h3.tsum_eq,hshift.tsum_eq] at h
  simpa [jetCoeff] using h

def GoodZ (q : ℂ) : Prop := Good q ∧ ‖zCoord q‖ < 1/2

theorem goodZZero : GoodZ 0 := ⟨goodZero,by simp [zZero]⟩

theorem zDiff (q : ℂ) (hq : Good q) : DifferentiableAt ℂ zCoord q := by
  unfold zCoord
  exact (differentiableAt_const _).sub (((yDifferentiable q hq.1).pow 2).div
    ((xDifferentiable q hq.1).pow 3) (pow_ne_zero _ (Complex.slitPlane_ne_zero hq.2.1)))

theorem goodZLocal (q : ℂ) (hq : GoodZ q) : ∀ᶠ w in 𝓝 q, GoodZ w := by
  have hz : ∀ᶠ w in 𝓝 q, ‖zCoord w‖ < 1/2 :=
    ((zDiff q hq.1).continuousAt.norm.eventually_lt continuousAt_const hq.2)
  filter_upwards [goodLocal q hq.1,hz] with w h1 h2
  exact ⟨h1,h2⟩

def composedJet (d : ℕ) (q : ℂ) := jet d (zCoord q)

theorem composedEuler (d : ℕ) (hd : d < 3) (q : ℂ) (hq : GoodZ q) :
    L (composedJet d) q = composedJet (d+1) q := by
  have h := (jetAnalytic d hd.le _ hq.2).differentiableAt.hasDerivAt.comp q
    (zDiff q hq.1).hasDerivAt
  have hz := zFlowAll q hq.1
  unfold L euler at hz
  unfold composedJet L euler
  rw [h.deriv]
  calc
    _ = ((x q/y q)*(q*deriv zCoord q))*deriv (jet d) (zCoord q) := by ring
    _ = _ := by rw [hz,jetEuler d hd _ hq.2]

theorem composedSecond (q : ℂ) (hq : GoodZ q) :
    L2 (composedJet 0) q = composedJet 2 q := by
  have h : L (composedJet 0) =ᶠ[𝓝 q] composedJet 1 :=
    (goodZLocal q hq).mono fun w hw => composedEuler 0 (by decide) w hw
  change L (L (composedJet 0)) q = _
  rw [LcongrAt q h,composedEuler 1 (by decide) q hq]

theorem composedThird (q : ℂ) (hq : GoodZ q) :
    L3 (composedJet 0) q = composedJet 3 q := by
  have h : L2 (composedJet 0) =ᶠ[𝓝 q] composedJet 2 :=
    (goodZLocal q hq).mono fun w hw => composedSecond w hw
  change L (L2 (composedJet 0)) q = _
  rw [LcongrAt q h,composedEuler 2 (by decide) q hq]

theorem hyperComposedODE (q : ℂ) (hq : GoodZ q) :
    ode (H ∘ zCoord) q = 0 := by
  have hEq : H ∘ zCoord = composedJet 0 := by
    funext w
    simp [composedJet,jetZeroOrder]
  rw [hEq]
  unfold ode
  rw [composedThird q hq,composedSecond q hq,composedEuler 0 (by decide) q hq]
  exact sub_eq_zero.mpr (hyperODEJets _ hq.2)

theorem hyperODEGerm : ode (H ∘ zCoord) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 :=
  (goodZLocal 0 goodZZero).mono fun w hw => hyperComposedODE w hw

theorem goodZOpen : IsOpen {q : ℂ | GoodZ q} :=
  isOpen_iff_mem_nhds.mpr fun q hq => goodZLocal q hq

theorem rootAnalyticGoodZ (q : ℂ) (hq : GoodZ q) : AnalyticAt ℂ rootF q :=
  DifferentiableOn.analyticAt
    (fun w hw => (rootDiff w hw.1).differentiableWithinAt)
    (goodZOpen.mem_nhds hq)

theorem hyperAnalyticGoodZ (q : ℂ) (hq : GoodZ q) :
    AnalyticAt ℂ (H ∘ zCoord) q :=
  DifferentiableOn.analyticAt
    (fun w hw => ((HAnalytic _ (lt_trans hw.2 (by norm_num))).differentiableAt.comp w
      (zDiff w hw.1)).differentiableWithinAt)
    (goodZOpen.mem_nhds hq)

-- Intended original local analytic identity with no equation premise.
-- Global selected CM disk membership/reflection remains separate.
theorem actualHyperIdentityGerm :
    rootF =ᶠ[𝓝 (0 : ℂ)] H ∘ zCoord :=
  rootEqualsHyperGerm (rootAnalyticGoodZ 0 goodZZero)
    (hyperAnalyticGoodZ 0 goodZZero) hyperODEGerm


-- Reuse the analytic identity theorem on the actual selected disk;
-- never extend the modular/branch equality through a denominator zero.
theorem actualHyperIdentityOn (U : Set ℂ) (hU : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hgood : ∀ q ∈ U, GoodZ q) :
    Set.EqOn rootF (H ∘ zCoord) U :=
  (fun q hq => rootAnalyticGoodZ q (hgood q hq) :
    AnalyticOnNhd ℂ rootF U).eqOn_of_preconnected_of_eventuallyEq
      (fun q hq => hyperAnalyticGoodZ q (hgood q hq)) hU h0 actualHyperIdentityGerm

theorem actualHyperIdentityBall (R : ℝ) (hR : 0 < R)
    (hgood : ∀ q : ℂ, ‖q‖ < R → GoodZ q) (q : ℂ) (hq : ‖q‖ < R) :
    rootF q = H (zCoord q) :=
  actualHyperIdentityOn (Metric.ball 0 R)
    (convex_ball (0 : ℂ) R).isPreconnected
    (Metric.mem_ball_self hR)
    (fun w hw => hgood w (Metric.mem_ball_zero_iff.mp hw))
    (Metric.mem_ball_zero_iff.mpr hq)

-- Exact period algebra on the original selected nonzero branch.
-- The real-positive square-root identification is a separate source
-- statement; this lemma keeps x/y and F, and does not square away sign.
theorem periodAlgebra (e x y F p : ℂ) (hy : y ≠ 0) (hp : p ≠ 0) :
    ((e*x/y-1)/6)*F + (1-(x/y)*(e-3/p))/6*F =
      F*(x/y)/(2*p) := by
  field_simp [hy,hp] <;> ring

end
end Integration.Paper9HypergeometricSeriesODE
