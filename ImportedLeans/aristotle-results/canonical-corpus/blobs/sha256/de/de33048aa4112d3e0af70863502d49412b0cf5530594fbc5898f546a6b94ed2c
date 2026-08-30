/-
# G21 — the gate: what the pole-quotiented exterior observable can and cannot see

`ExteriorCore.lean` and `ExteriorPairKernel.lean` established the exact algebra of
the two-channel, pole-quotiented exterior observable.  This module answers the
two questions on which the whole architecture turns, and both answers are
negative at literal strength.

## 1.  Is the pole response of a contrastive-derivative channel pair rank one?

No.  The literal pole profile is
`m(x) = ∫_0^L e^{u/2} cos(xu) du` (the `u = log t` form of the G20 main term
`∫_1^N t^{-1/2}cos(x log t) dt`, with `L = log N`), and the second channel
`f₂ = ∂_x f₁` has pole response `m′`.  `poleProfile_deriv_not_proportional`
proves that no constant `c` satisfies `m′ = c·m`: the profile is even, so `m′(0) = 0`
forces `c = 0`, and `m` is not constant because `m(2π/L) < m(0)` exactly
(`poleProfile_two_pi_div_lt_zero_freq`).

So `commonPoleProfileFactorization` in the form `M_i = c_i·m` is **false** for
the contrastive-derivative pair, and three samples with one nuisance row do not
suffice.  The repair is exact and is already proved: adjoin **both** pole
profiles as nuisance rows and use four samples
(`augDet4_pole_annihilation`), leaving `4 − 2 = 2` transverse dimensions.

## 2.  Does an off-critical-line zero survive the exact pole quotient?

No — and for two independent, exactly provable reasons.

*Mode model.*  A single zero contributes a single mode `a e^{ixλ}` to the
channel, and its derivative channel is `iλ a e^{ixλ}`: the two channel rows are
then proportional, so the exterior observable is **identically zero**
(`augDet3_singleMode_annihilated`, `augDet4_singleMode_annihilated`),
independently of the amplitude `a` in which the off-line parameter `α` lives.
Hence no floor `c L^p |α|^q` can hold (`singleMode_gate_no_floor`).  This is the
exact same mechanism as `pairKernel_diag`: the exterior/determinant projection
annihilates *every* diagonal self-interaction, and the diagonal self-energy is
precisely where every positivity-based zero detector keeps its signal.

*General holomorphic obstruction.*  Any observable that depends holomorphically
on the zero parameter `ρ` near a point of the critical line and vanishes for
every on-line `ρ` there must vanish identically near that point
(`holomorphic_gate_local`), because the critical line is not an analytic
condition: it accumulates.  Consequently no such observable can both vanish
on-line and be nonzero off-line (`no_criticalLine_separation`).  Since the
augmented determinant is a polynomial in holomorphic row entries
(`differentiableOn_augDet3_of_rows`), it is exactly of this kind.

The conclusion for G21 is therefore the one the design document asked for: the
architecture is killed at lemma 3, cheaply, and for a structural reason —
detection of the critical line requires a conjugate-linear (positivity)
ingredient, and that ingredient lives on the diagonal that the exterior
projection annihilates by construction.
-/
import RiemannAnalytic.ExteriorPairKernel

open intervalIntegral Filter

namespace RiemannAnalytic

noncomputable section

/-! ## The literal pole profile and its derivative channel -/

/-- The literal pole (prime-number-theorem) profile in the `u = log t`
coordinate: `m(x) = ∫_0^L e^{u/2} cos(xu) du`, i.e. the G20 main term
`∫_1^N t^{-1/2} cos(x log t) dt` with `L = log N`. -/
def poleProfile (L x : ℝ) : ℝ := ∫ u in (0:ℝ)..L, Real.exp (u / 2) * Real.cos (x * u)

/-- The elementary antiderivative of the pole integrand. -/
def poleAntideriv (x u : ℝ) : ℝ :=
  Real.exp (u / 2) * ((1 / 2) * Real.cos (x * u) + x * Real.sin (x * u)) / (1 / 4 + x ^ 2)

theorem hasDerivAt_poleAntideriv (x u : ℝ) :
    HasDerivAt (poleAntideriv x) (Real.exp (u / 2) * Real.cos (x * u)) u := by
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
    simpa using (Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)
  have h2 : HasDerivAt (fun u : ℝ => Real.cos (x * u)) (-Real.sin (x * u) * x) u := by
    simpa using (Real.hasDerivAt_cos (x * u)).comp u ((hasDerivAt_id u).const_mul x)
  have h3 : HasDerivAt (fun u : ℝ => Real.sin (x * u)) (Real.cos (x * u) * x) u := by
    simpa using (Real.hasDerivAt_sin (x * u)).comp u ((hasDerivAt_id u).const_mul x)
  have h4 : HasDerivAt (fun u : ℝ => (1 / 2) * Real.cos (x * u) + x * Real.sin (x * u))
      ((1 / 2) * (-Real.sin (x * u) * x) + x * (Real.cos (x * u) * x)) u :=
    (h2.const_mul (1 / 2 : ℝ)).add (h3.const_mul x)
  have h5 := (h1.mul h4).div_const (1 / 4 + x ^ 2)
  refine h5.congr_deriv ?_
  have hx : (1 / 4 + x ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Closed form of the literal pole profile. -/
theorem poleProfile_closedForm (L x : ℝ) :
    poleProfile L x = (Real.exp (L / 2) * ((1 / 2) * Real.cos (x * L) + x * Real.sin (x * L))
      - 1 / 2) / (1 / 4 + x ^ 2) := by
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * Real.cos (x * u))
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := integral_eq_sub_of_hasDerivAt (f := poleAntideriv x)
    (f' := fun u => Real.exp (u / 2) * Real.cos (x * u)) (a := 0) (b := L)
    (fun u _ => hasDerivAt_poleAntideriv x u) hint
  rw [poleProfile, h, poleAntideriv, poleAntideriv]
  simp
  ring

/-- At zero frequency the profile is `2(e^{L/2} − 1)`, matching the G20 value
`2(√N − 1)`. -/
theorem poleProfile_zero_freq (L : ℝ) : poleProfile L 0 = 2 * (Real.exp (L / 2) - 1) := by
  rw [poleProfile_closedForm]
  norm_num
  ring

theorem poleProfile_even (L x : ℝ) : poleProfile L (-x) = poleProfile L x := by
  simp [poleProfile, neg_mul, Real.cos_neg]

/-- At the frequency `2π/L` the profile is strictly smaller than at zero
frequency: the pole profile is **not** constant. -/
theorem poleProfile_two_pi_div_lt_zero_freq {L : ℝ} (hL : 0 < L) :
    poleProfile L (2 * Real.pi / L) < poleProfile L 0 := by
  have hx : (2 * Real.pi / L) * L = 2 * Real.pi := by field_simp
  have hcos : Real.cos ((2 * Real.pi / L) * L) = 1 := by rw [hx]; simp [Real.cos_two_pi]
  have hsin : Real.sin ((2 * Real.pi / L) * L) = 0 := by rw [hx]; simp [Real.sin_two_pi]
  have hA : 1 < Real.exp (L / 2) := by
    have : (0 : ℝ) < L / 2 := by linarith
    simpa using Real.one_lt_exp_iff.mpr this
  have hnum : 0 < Real.exp (L / 2) / 2 - 1 / 2 := by linarith
  have hden : (1 : ℝ) / 4 < 1 / 4 + (2 * Real.pi / L) ^ 2 := by
    have hpos : 0 < (2 * Real.pi / L) ^ 2 := by
      have : 0 < 2 * Real.pi / L := by positivity
      positivity
    linarith
  rw [poleProfile_closedForm, poleProfile_zero_freq, hcos, hsin]
  have hval : Real.exp (L / 2) * ((1 / 2) * 1 + (2 * Real.pi / L) * 0) - 1 / 2
      = Real.exp (L / 2) / 2 - 1 / 2 := by ring
  rw [hval]
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num
  calc (Real.exp (L / 2) / 2 - 1 / 2) / (1 / 4 + (2 * Real.pi / L) ^ 2)
      < (Real.exp (L / 2) / 2 - 1 / 2) / (1 / 4) := by
        exact div_lt_div_of_pos_left hnum h4 hden
    _ = 2 * (Real.exp (L / 2) - 1) := by ring

/-- The pole profile is differentiable in the frequency. -/
theorem differentiable_poleProfile (L : ℝ) : Differentiable ℝ (poleProfile L) := by
  have : poleProfile L = fun x : ℝ =>
      (Real.exp (L / 2) * ((1 / 2) * Real.cos (x * L) + x * Real.sin (x * L)) - 1 / 2)
        / (1 / 4 + x ^ 2) := by
    funext x; exact poleProfile_closedForm L x
  rw [this]
  intro x
  have hden : (1 / 4 + x ^ 2) ≠ 0 := by positivity
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) hden

/-- **The rank-one pole hypothesis fails for the contrastive-derivative channel
pair.**  There is no constant `c` with `m′ = c·m`; equivalently, the pole
responses `m` (channel one) and `m′` (channel two) are not a rank-one family, so
three samples with a single nuisance row cannot annihilate the pole. -/
theorem poleProfile_deriv_not_proportional {L : ℝ} (hL : 0 < L) :
    ¬ ∃ c : ℝ, ∀ x : ℝ, HasDerivAt (poleProfile L) (c * poleProfile L x) x := by
  rintro ⟨c, hc⟩
  -- evenness forces the derivative at `0` to vanish
  have hzero : c * poleProfile L 0 = 0 := by
    have h1 : HasDerivAt (poleProfile L) (c * poleProfile L 0) 0 := hc 0
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).neg
    have h2 : HasDerivAt (fun x : ℝ => poleProfile L (-x)) (-(c * poleProfile L 0)) 0 := by
      have h1' : HasDerivAt (poleProfile L) (c * poleProfile L 0) (-(0:ℝ)) := by simpa using h1
      simpa using h1'.comp (0:ℝ) hneg
    have h3 : HasDerivAt (poleProfile L) (-(c * poleProfile L 0)) 0 := by
      have hfun : (fun x : ℝ => poleProfile L (-x)) = poleProfile L := by
        funext x; exact poleProfile_even L x
      rwa [hfun] at h2
    have := h1.unique h3
    linarith
  have hm0 : 0 < poleProfile L 0 := by
    rw [poleProfile_zero_freq]
    have : 1 < Real.exp (L / 2) := by
      have : (0 : ℝ) < L / 2 := by linarith
      simpa using Real.one_lt_exp_iff.mpr this
    linarith
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (ne_of_gt hm0)
  -- with `c = 0` the profile would be constant, contradicting its exact value at `2π/L`
  have hderiv : ∀ x : ℝ, deriv (poleProfile L) x = 0 := by
    intro x
    have := hc x
    rw [hc0] at this
    simpa using this.deriv
  have hconst := is_const_of_deriv_eq_zero (differentiable_poleProfile L) hderiv
    (2 * Real.pi / L) 0
  have hlt := poleProfile_two_pi_div_lt_zero_freq hL
  rw [hconst] at hlt
  exact lt_irrefl _ hlt

/-! ## The single-mode (single-zero) response is annihilated exactly -/

/-- A single mode with its derivative channel produces **exactly zero**: the two
channel rows are proportional, so the exterior observable cannot see it at all —
whatever the amplitude `a`. -/
theorem augDet3_singleMode_annihilated (a : ℂ) (l : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ) :
    augDet3 (a • modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l) m = 0 := by
  have hB := antisymBilin_augDet3 m
  have h := hB.smul_left a (modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l)
  have h2 := hB.smul_right (Complex.I * (l : ℂ) * a) (modeVector x l) (modeVector x l)
  have h3 := hB.self (modeVector x l)
  simp only at h h2 h3
  rw [h, h2, h3]
  ring

theorem augDet4_singleMode_annihilated (a : ℂ) (l : ℝ) (x : Fin 4 → ℝ) (p q : Fin 4 → ℂ) :
    augDet4 (a • modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l) p q = 0 := by
  have hB := antisymBilin_augDet4 p q
  have h := hB.smul_left a (modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l)
  have h2 := hB.smul_right (Complex.I * (l : ℂ) * a) (modeVector x l) (modeVector x l)
  have h3 := hB.self (modeVector x l)
  simp only at h h2 h3
  rw [h, h2, h3]
  ring

/-- **Lemma 3 is red in the mode model.**  No floor of the shape
`c·height^p·|α|^q` can hold for the single-zero exterior response, because that
response is identically zero. -/
theorem singleMode_gate_no_floor (l : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ)
    {cc height : ℝ} (hc : 0 < cc) (hheight : 0 < height) (p q : ℕ) :
    ¬ ∀ (alpha : ℝ) (a : ℂ), alpha ≠ 0 →
        cc * height ^ p * |alpha| ^ q
          ≤ ‖augDet3 (a • modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l) m‖ := by
  intro h
  have h1 := h 1 1 one_ne_zero
  rw [augDet3_singleMode_annihilated] at h1
  simp only [norm_zero, abs_one, one_pow, mul_one] at h1
  have : 0 < cc * height ^ p := by positivity
  linarith

/-! ## The general holomorphic obstruction -/

/-- **The critical line is not an analytic condition.**  An observable that is
holomorphic in the zero parameter on a disc and vanishes at every parameter of
the disc lying on the vertical line through its centre vanishes identically on
the disc. -/
theorem holomorphic_gate_local {F : ℂ → ℂ} {rho0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball rho0 r))
    (hline : ∀ z ∈ Metric.ball rho0 r, z.re = rho0.re → F z = 0) :
    ∀ z ∈ Metric.ball rho0 r, F z = 0 := by
  have hopen : IsOpen (Metric.ball rho0 r) := Metric.isOpen_ball
  have hanal : AnalyticOnNhd ℂ F (Metric.ball rho0 r) := hF.analyticOnNhd hopen
  have hconn : IsPreconnected (Metric.ball rho0 r) := (convex_ball rho0 r).isPreconnected
  have hmem : rho0 ∈ Metric.ball rho0 r := Metric.mem_ball_self hr
  obtain ⟨c, hcpos, hclt, hctend⟩ :
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧ (∀ n, c n < r) ∧ Filter.Tendsto c atTop (nhds 0) := by
    refine ⟨fun n => r / ((n : ℝ) + 2), fun n => by positivity, fun n => ?_, ?_⟩
    · exact div_lt_self hr (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    · have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact h1.const_div_atTop r
  have hfreq : ∃ᶠ z in nhdsWithin rho0 {rho0}ᶜ, F z = 0 := by
    have hC : Filter.Tendsto (fun n : ℕ => ((c n : ℝ) : ℂ)) atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hctend
    rw [Complex.ofReal_zero] at hC
    have htend : Filter.Tendsto (fun n : ℕ => rho0 + Complex.I * ((c n : ℝ) : ℂ))
        atTop (nhdsWithin rho0 {rho0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (tendsto_const_nhds.add (hC.const_mul Complex.I))
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h2 : Complex.I * ((c n : ℝ) : ℂ) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2 with h1 | h1
        · exact Complex.I_ne_zero h1
        · exact absurd (Complex.ofReal_eq_zero.mp h1) (ne_of_gt (hcpos n))
    refine htend.frequently (Filter.Frequently.of_forall ?_)
    intro n
    refine hline _ ?_ ?_
    · simp only [Metric.mem_ball, dist_eq_norm]
      have hsub : rho0 + Complex.I * ((c n : ℝ) : ℂ) - rho0 = Complex.I * ((c n : ℝ) : ℂ) := by
        ring
      rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hcpos n)]
      exact hclt n
    · simp
  have hEq := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn hmem hfreq
  intro z hz
  simpa using hEq hz

/-- **No holomorphic observable separates the critical line.**  A holomorphic
observable cannot both vanish at every on-line zero parameter of a disc centred
on the critical line and be nonzero at some off-line parameter of that disc. -/
theorem no_criticalLine_separation {F : ℂ → ℂ} {rho0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball rho0 r)) (hre : rho0.re = 1 / 2) :
    ¬ ((∀ z ∈ Metric.ball rho0 r, z.re = 1 / 2 → F z = 0)
        ∧ ∃ z ∈ Metric.ball rho0 r, z.re ≠ 1 / 2 ∧ F z ≠ 0) := by
  rintro ⟨hvanish, z, hz, _, hne⟩
  refine hne ?_
  refine holomorphic_gate_local hr hF ?_ z hz
  intro w hw hwre
  exact hvanish w hw (by rw [hwre, hre])

/-- The augmented three-sample determinant of holomorphic row families is
holomorphic, so it is exactly of the kind covered by `no_criticalLine_separation`. -/
theorem differentiableOn_augDet3_of_rows {U : Set ℂ} (u w : ℂ → (Fin 3 → ℂ)) (m : Fin 3 → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (fun z => u z j) U)
    (hw : ∀ j, DifferentiableOn ℂ (fun z => w z j) U) :
    DifferentiableOn ℂ (fun z => augDet3 (u z) (w z) m) U := by
  have : (fun z => augDet3 (u z) (w z) m)
      = fun z => u z 0 * (w z 1 * m 2 - w z 2 * m 1) - u z 1 * (w z 0 * m 2 - w z 2 * m 0)
        + u z 2 * (w z 0 * m 1 - w z 1 * m 0) := by
    funext z; exact augDet3_eq (u z) (w z) m
  rw [this]
  exact (((hu 0).mul (((hw 1).mul_const (m 2)).sub ((hw 2).mul_const (m 1)))).sub
      ((hu 1).mul (((hw 0).mul_const (m 2)).sub ((hw 2).mul_const (m 0))))).add
    ((hu 2).mul (((hw 0).mul_const (m 1)).sub ((hw 1).mul_const (m 0))))

end

end RiemannAnalytic
