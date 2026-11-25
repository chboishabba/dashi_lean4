import Integration.Paper9HypergeometricSeriesODE

/-! SOURCE-WRITTEN, UNCOMPILED.
Selected CM disk from the original Agda-shaped Eisenstein limit owners,
not a replacement Fourier model. The terminal signed normalization
keeps the positive branch and does not assume the CM certificate.
-/
namespace Integration.Paper9SelectedCMDomain

open Complex Function Filter UpperHalfPlane ArithmeticFunction
open scoped Topology Real Nat ArithmeticFunction.sigma
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9RootODE
open Integration.Paper9HypergeometricSeriesODE

noncomputable section

local notation "r" => (1 / 16 : ℝ)
local notation "R" => ((1 / 2 : ℝ)^36)
local notation "t" => ((1 / 2 : ℝ)^30)

theorem natLeTwoPow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ (2 : ℕ)^n := by positivity
    omega

-- Original shifted index n+1: no missing zero term.
theorem divisorMajorant (k m : ℕ) (hk : k ≤ 5) :
    (σ k m : ℝ) ≤ (64 : ℝ)^m := by
  have h := ArithmeticFunction.sigma_le_pow_succ k m
  calc
    (σ k m : ℝ) ≤ (m : ℝ)^(k+1) := by exact_mod_cast h
    _ ≤ ((2 : ℝ)^m)^(k+1) := by
      gcongr
      exact_mod_cast natLeTwoPow m
    _ ≤ ((2 : ℝ)^m)^6 := by
      apply pow_le_pow_right₀
      · exact one_le_pow₀ (by norm_num) _
      · omega
    _ = (64 : ℝ)^m := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

theorem shiftedTermBound (q : ℂ) (hq : ‖q‖ ≤ R)
    (k n c : ℕ) (hk : k ≤ 5) (hc : c ≤ 504) :
    ‖((c * σ k (n+1) : ℕ) : ℂ)*q^(n+1)‖ ≤ 504*t^(n+1) := by
  rw [norm_mul, Complex.norm_natCast, norm_pow, Nat.cast_mul]
  calc
    _ ≤ 504*(64 : ℝ)^(n+1)*R^(n+1) := by
      gcongr
      · exact_mod_cast hc
      · exact divisorMajorant k (n+1) hk
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

theorem geometricMajorant :
    HasSum (fun n : ℕ => 504*t^(n+1)) (504*t/(1-t)) := by
  have h := hasSum_geometric_of_norm_lt_one (r := t) (by norm_num)
  convert (h.mul_left (504*t)) using 1
  · funext n
    rw [pow_succ]
    ring
  · ring

theorem shiftedTail (f : ℕ → ℂ) (hs : Summable f)
    (hb : ∀ n, ‖f n‖ ≤ 504*t^(n+1)) : ‖∑' n, f n‖ ≤ r := by
  have hn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb geometricMajorant.summable
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, 504*t^(n+1) :=
      tsum_le_tsum hb hn geometricMajorant.summable
    _ = 504*t/(1-t) := geometricMajorant.tsum_eq
    _ ≤ r := by norm_num

-- Use the original convergent target, including its signed E6 tail.
theorem originalBandsAt (τ : ℍ)
    (hq : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ R) :
    ‖x (Periodic.qParam 1 τ)-1‖ ≤ r ∧
    ‖y (Periodic.qParam 1 τ)-1‖ ≤ r := by
  have hq' : Integration.MoonshineEisensteinAgdaTarget.qOfTarget τ =
      Periodic.qParam 1 (τ : ℂ) := by
    rw [Integration.MoonshineEisensteinAgdaTarget.qOfTarget_eq_qParam]
    simp [Integration.MoonshineEisensteinAnalytic.qParam, Periodic.qParam]
  have h4 := shiftedTail
    (Integration.MoonshineEisensteinAgdaTarget.e4Term τ)
    (Integration.MoonshineEisensteinAgdaTarget.summable_e4Term τ)
    (fun n => by
      simpa [Integration.MoonshineEisensteinAgdaTarget.e4Term,
        Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,hq'] using
        shiftedTermBound _ hq 3 n 240 (by decide) (by decide))
  have h6 := shiftedTail
    (Integration.MoonshineEisensteinAgdaTarget.e6Term τ)
    (Integration.MoonshineEisensteinAgdaTarget.summable_e6Term τ)
    (fun n => by
      simpa [Integration.MoonshineEisensteinAgdaTarget.e6Term,
        Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,hq'] using
        shiftedTermBound _ hq 5 n 504 (by decide) (by decide))
  rw [xAtQ,yAtQ,← Integration.MoonshineEisensteinAgdaTarget.e4Limit_eq_mathlib_E4,
    ← Integration.MoonshineEisensteinAgdaTarget.e6Limit_eq_mathlib_E6]
  constructor
  · simpa [Integration.MoonshineEisensteinAgdaTarget.e4Limit] using h4
  · have he : (1 - ∑' n, Integration.MoonshineEisensteinAgdaTarget.e6Term τ n) - 1 =
        -(∑' n, Integration.MoonshineEisensteinAgdaTarget.e6Term τ n) := by ring
    simpa [Integration.MoonshineEisensteinAgdaTarget.e6Limit,he] using h6

-- This is a q-parameter chart lift, not an inverse of j or z.
theorem originalBands (q : ℂ) (hq : ‖q‖ ≤ R) :
    ‖x q-1‖ ≤ r ∧ ‖y q-1‖ ≤ r := by
  by_cases hn : q = 0
  · subst q
    simp [xZero,yZero]
  · have hunit : ‖q‖ < 1 := lt_of_le_of_lt hq (by norm_num)
    let τ : ℍ := ⟨Periodic.invQParam 1 q,
      Periodic.im_invQParam_pos_of_norm_lt_one one_pos hunit hn⟩
    have he : Periodic.qParam 1 (τ : ℂ) = q :=
      Periodic.qParam_right_inv one_ne_zero hn
    have h := originalBandsAt τ (by rwa [he])
    rwa [he] at h

theorem cubeBand (X : ℂ) (h : ‖X-1‖ ≤ r) :
    ‖X^3-1‖ ≤ 817/4096 := by
  have he : X^3-1 = 3*(X-1)+3*(X-1)^2+(X-1)^3 := by ring
  rw [he]
  calc
    _ ≤ ‖3*(X-1)+3*(X-1)^2‖+‖(X-1)^3‖ := norm_add_le _ _
    _ ≤ ‖3*(X-1)‖+‖3*(X-1)^2‖+‖(X-1)^3‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 817/4096 := by
      simp only [norm_mul,norm_pow,norm_ofNat]
      nlinarith [sq_nonneg ‖X-1‖, pow_le_pow_left₀ (norm_nonneg _) h 2,
        pow_le_pow_left₀ (norm_nonneg _) h 3]

theorem squareBand (Y : ℂ) (h : ‖Y-1‖ ≤ r) :
    ‖Y^2-1‖ ≤ 528/4096 := by
  have he : Y^2-1 = 2*(Y-1)+(Y-1)^2 := by ring
  rw [he]
  calc
    _ ≤ ‖2*(Y-1)‖+‖(Y-1)^2‖ := norm_add_le _ _
    _ ≤ 528/4096 := by
      simp only [norm_mul,norm_pow,norm_ofNat]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2]

theorem lowerNorm (X : ℂ) (h : ‖X-1‖ ≤ r) : 15/16 ≤ ‖X‖ := by
  have ht := norm_add_le X (-(X-1))
  have he : X + -(X-1) = 1 := by ring
  rw [he,norm_one,norm_neg] at ht
  linarith

theorem positiveRe (X : ℂ) (h : ‖X-1‖ ≤ r) : 0 < X.re := by
  have he := Complex.abs_re_le_norm (X-1)
  have hh := (abs_le.mp (he.trans h)).1
  simp at hh
  linarith

theorem goodSelected (q : ℂ) (hq : ‖q‖ ≤ R) : GoodZ q := by
  obtain ⟨hx,hy⟩ := originalBands q hq
  have hxn : x q ≠ 0 := by
    intro he
    have hn := lowerNorm _ hx
    rw [he,norm_zero] at hn
    norm_num at hn
  have hyn : y q ≠ 0 := by
    intro he
    have hn := lowerNorm _ hy
    rw [he,norm_zero] at hn
    norm_num at hn
  have hgood : Good q := ⟨lt_of_le_of_lt hq (by norm_num),
    Or.inl (positiveRe _ hx),hyn⟩
  refine ⟨hgood,?_⟩
  have hdiff : ‖x q^3-y q^2‖ ≤ 1345/4096 := by
    have he : x q^3-y q^2 = (x q^3-1)-(y q^2-1) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [cubeBand _ hx,squareBand _ hy])
  have hden : (3375/4096 : ℝ) ≤ ‖x q‖^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 15/16) (lowerNorm _ hx) 3
    norm_num at h
    exact h
  have he : zCoord q = (x q^3-y q^2)/x q^3 := by
    unfold zCoord
    field_simp
  rw [he,norm_div,norm_pow]
  apply (div_lt_iff₀ (by positivity)).2
  linarith

theorem actualHyperIdentitySelected (q : ℂ) (hq : ‖q‖ < R) :
    rootF q = H (zCoord q) :=
  actualHyperIdentityBall R (by norm_num)
    (fun w hw => goodSelected w hw.le) q hq

-- Pay the local derivative correspondence on the same open disk.
theorem actualHyperFirstJetSelected (q : ℂ) (hq : ‖q‖ < R) :
    L rootF q = jet 1 (zCoord q) := by
  have hl : rootF =ᶠ[𝓝 q] composedJet 0 := by
    have hn : ∀ᶠ w in 𝓝 q, ‖w‖ < R :=
      continuous_norm.continuousAt.eventually_lt continuousAt_const hq
    filter_upwards [hn] with w hw
    simpa [composedJet,jetZeroOrder] using actualHyperIdentitySelected w hw
  rw [LcongrAt q hl,composedEuler 0 (by decide) q (goodSelected q hq.le)]
  rfl

-- Exact terminal scalar normalization with SIGN, not squared equality.
-- Inputs are the actual selected CM scalar values once reflected.
theorem cmConstants :
    (1-(77265280/90856689 : ℚ))/6 = 13591409/545140134 ∧
    (144 : ℤ)*545140134^2 = 163*(640320^3+1728) ∧
    (640320 : ℤ)^3 = 144*426880^2*10005 := by norm_num

theorem positiveNormalization (p v R0 : ℝ)
    (hp : 0 < p) (hv : 0 < v) (hR : 0 < R0)
    (hs : v^2 = 163*(1+1728/(640320^3 : ℝ)))
    (hr : R0^2 = 10005) :
    (545140134 : ℝ)/(p*v) = 426880*R0/p := by
  have he : (545140134 : ℝ)^2 = (426880*R0*v)^2 := by
    rw [mul_pow,mul_pow,hr,hs]
    norm_num
  have hf : ((545140134 : ℝ)-426880*R0*v)*
      (545140134+426880*R0*v) = 0 := by nlinarith [he]
  have hplus : (545140134 : ℝ)+426880*R0*v ≠ 0 := by positivity
  have h := (mul_eq_zero.mp hf).resolve_right hplus
  field_simp [hp.ne',hv.ne']
  linarith

end
end Integration.Paper9SelectedCMDomain
