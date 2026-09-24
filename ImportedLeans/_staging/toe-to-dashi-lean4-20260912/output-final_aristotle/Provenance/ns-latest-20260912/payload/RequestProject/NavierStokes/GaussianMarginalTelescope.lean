/-
# The marginal channel telescopes

`SimilarityNearFarAbsorption.lean` isolates the marginal channel `⟪N, P_V W⟫`
of the similarity pairing and insists that it be *computed*.
`GaussianMarginalChannel.lean` computes the scalar it is made of, exactly:

  `⟪N, V⟫_ρ = ∫ρ_ν⟪(V·∇)V + ∇p, V⟫ = (1/(4ν))∫ρ_ν⟪y,V⟫(|V|² + 2p) =: 𝒥(V,p)`.

This file performs the second half of that computation, the one that removes
the need for an *absolute* bound on the marginal channel.  With

  `A(τ) = ⟪V(τ),V(τ)⟫`,  `W = V_τ`,  `C(τ) = ⟪V,W⟫ = ½A′(τ)`,

the amplitude projection is `P_VW = (C/A)V`, so

  `⟪N, P_VW⟫ = (C/A)·⟪N,V⟫ = (A′/(2A))·𝒥 = ½(log A)′·𝒥`.      (M)

Hence the marginal channel is *never* an independent estimate: it is the
logarithmic derivative of the amplitude times an explicitly computed integral.
If `𝒥` is a function of the amplitude alone, `𝒥 = F(A)`, the channel is an
**exact derivative**,

  `⟪N, P_VW⟫ = d/dτ 𝒦(A(τ))`,  `𝒦′(a) = F(a)/(2a)`,

and with a transverse remainder, `𝒥 = F(A) + R`, it is that derivative plus
`(A′/(2A))R`, which is the only thing that ever has to be integrated.

## What is proved

* `ClayNS.hasDerivAt_ampSq` — `A′ = 2⟪V,W⟫`, i.e. `C = ½A′`;
* `ClayNS.amplitude_marginal_channel_logDeriv` — identity (M), with no
  positivity hypothesis (both sides degenerate consistently at `A = 0`);
* `ClayNS.gaussMarginalJ` and `ClayNS.gauss_amplitude_marginal_channel` — the
  physical form: `⟪N,P_VW⟫ = ½(log A)′·𝒥(V,p)` with `𝒥` the explicit Gaussian
  integral computed in `GaussianMarginalChannel.lean`;
* `ClayNS.marginal_channel_telescope` — the telescope with remainder:
  `d/dτ 𝒦(A) = ⟪N,P_VW⟫ − (A′/(2A))R`;
* `ClayNS.marginal_channel_telescope_exact` — the remainder-free case: the
  marginal channel *is* a total derivative;
* `ClayNS.hasDerivAt_ampPrimitive_rpow`, `ClayNS.hasDerivAt_ampPrimitive_log` —
  the primitives `𝒦` for the two model amplitude laws `𝒥 = κA^m` (`m ≠ 0`) and
  `𝒥 = κ` (`m = 0`), so the telescope is available in closed form;
* `ClayNS.marginal_channel_total_le` — the accumulated marginal channel of the
  window is bounded by the *variation of the primitive* plus the accumulated
  remainder: no absolute bound on `⟪N,P_VW⟫` is used anywhere.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityNearFarAbsorption
import RequestProject.NavierStokes.GaussianMarginalChannel

open Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## `C = ½A′` -/

/-- The amplitude `A(τ) = ⟪V,V⟫` has derivative `2⟪V,W⟫`: the Gram coefficient
`C = ⟪V,V_τ⟫` is exactly half the derivative of the amplitude. -/
theorem hasDerivAt_ampSq {V : ℝ → E} {W : E} {t : ℝ} (h : HasDerivAt V W t) :
    HasDerivAt (fun s => (⟪V s, V s⟫ : ℝ)) (2 * ⟪V t, W⟫) t := by
  have := h.inner ℝ h
  simpa [real_inner_comm (V t) W, two_mul] using this

/-! ## The marginal channel is a logarithmic derivative -/

/-- **Identity (M).**  Along a differentiable similarity curve the marginal
channel is the logarithmic derivative of the amplitude times the computed
scalar `⟪N,V⟫`:

  `⟪N, P_VW⟫ = (A′/(2A))·⟪N,V⟫`.

No positivity of `A` is needed: at `A = 0` the amplitude projection and the
right-hand side both vanish by the junk-value convention for division. -/
theorem amplitude_marginal_channel_logDeriv {V : ℝ → E} {W N : E} {t Ad : ℝ}
    (h : HasDerivAt V W t)
    (hA : HasDerivAt (fun s => (⟪V s, V s⟫ : ℝ)) Ad t) :
    (⟪N, amplitudeProj (V t) W⟫ : ℝ) = (Ad / (2 * ⟪V t, V t⟫)) * ⟪N, V t⟫ := by
  have hAd : Ad = 2 * ⟪V t, W⟫ := hA.unique (hasDerivAt_ampSq h)
  rw [amplitude_marginal_channel (V t) N W, hAd]
  rcases eq_or_ne (⟪V t, V t⟫ : ℝ) 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

/-! ## The physical scalar `𝒥` -/

/-- The exactly computed Gaussian marginal integral

  `𝒥(V,p) = (1/(4ν))∫ρ_ν⟪y,V⟫(|V|² + 2p)`,

the value of `⟪N,V⟫_ρ` for `N = (V·∇)V + ∇p`
(`ClayNS.gauss_weighted_marginal_channel`). -/
def gaussMarginalJ (nu : ℝ) (V : E3 → E3) (p : E3 → ℝ) : ℝ :=
  (1 / (4 * nu)) * ∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))

/-- **The physical marginal channel is `½(log A)′·𝒥`.**  The abstract inner
product `⟪N,V⟫` of the similarity Hilbert space is linked to the Gaussian
pairing by `hlink` (this is the definition of the weighted inner product, not
an estimate); with the exact computation of `GaussianMarginalChannel.lean` the
marginal channel of the amplitude projection is

  `⟪N, P_VW⟫ = (A′/(2A))·𝒥(V,p)`. -/
theorem gauss_amplitude_marginal_channel {nu : ℝ} (hnu : nu ≠ 0)
    {Vfun : E3 → E3} {p : E3 → ℝ}
    (hVfun : ContDiff ℝ (1 : ℕ) Vfun) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace Vfun y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → Vfun y = 0)
    {Vcur : ℝ → E} {W N : E} {t Ad : ℝ}
    (h : HasDerivAt Vcur W t)
    (hA : HasDerivAt (fun s => (⟪Vcur s, Vcur s⟫ : ℝ)) Ad t)
    (hlink : (⟪N, Vcur t⟫ : ℝ)
      = ∫ y : E3, gaussWeight nu y * ⟪advSpace Vfun y + gradSpace p y, Vfun y⟫) :
    (⟪N, amplitudeProj (Vcur t) W⟫ : ℝ)
      = (Ad / (2 * ⟪Vcur t, Vcur t⟫)) * gaussMarginalJ nu Vfun p := by
  rw [amplitude_marginal_channel_logDeriv h hA, hlink,
    gauss_weighted_marginal_channel hnu hVfun hp hdiv hL hsupp, gaussMarginalJ]

/-! ## The telescope -/

/-- **The marginal channel telescopes.**  Suppose the computed scalar splits as

  `𝒥(τ) = F(A(τ)) + R(τ)`

into an amplitude law and a transverse remainder, and `𝒦` is a primitive of
`a ↦ F(a)/(2a)`.  Then along the similarity curve

  `d/dτ 𝒦(A(τ)) = ⟪N,P_VW⟫ − (A′/(2A))·R`,

i.e. the whole marginal channel is a total derivative up to the remainder
`(A′/(2A))R`, which is the only quantity that ever needs integrating. -/
theorem marginal_channel_telescope {Acal Jcal Rmarg mchan Ad : ℝ → ℝ}
    {Kf F : ℝ → ℝ} {t : ℝ}
    (hA : HasDerivAt Acal (Ad t) t)
    (hK : HasDerivAt Kf (F (Acal t) / (2 * Acal t)) (Acal t))
    (hJ : Jcal t = F (Acal t) + Rmarg t)
    (hm : mchan t = (Ad t / (2 * Acal t)) * Jcal t) :
    HasDerivAt (fun s => Kf (Acal s))
      (mchan t - (Ad t / (2 * Acal t)) * Rmarg t) t := by
  have hcomp : HasDerivAt (fun s => Kf (Acal s))
      (F (Acal t) / (2 * Acal t) * Ad t) t := hK.comp t hA
  have hval : F (Acal t) / (2 * Acal t) * Ad t
      = mchan t - (Ad t / (2 * Acal t)) * Rmarg t := by
    rw [hm, hJ]
    field_simp
    ring
  rwa [hval] at hcomp

/-- **The remainder-free telescope.**  If the computed scalar is a function of
the amplitude alone, the marginal channel *is* the derivative of `𝒦(A)`: the
channel needs no bound at all. -/
theorem marginal_channel_telescope_exact {Acal Jcal mchan Ad : ℝ → ℝ}
    {Kf F : ℝ → ℝ} {t : ℝ}
    (hA : HasDerivAt Acal (Ad t) t)
    (hK : HasDerivAt Kf (F (Acal t) / (2 * Acal t)) (Acal t))
    (hJ : Jcal t = F (Acal t))
    (hm : mchan t = (Ad t / (2 * Acal t)) * Jcal t) :
    HasDerivAt (fun s => Kf (Acal s)) (mchan t) t := by
  have h := marginal_channel_telescope (Rmarg := fun _ => (0 : ℝ))
    hA hK (by simpa using hJ) hm
  simpa using h

/-! ## Closed-form primitives for the model amplitude laws -/

/-- The primitive for the power law `F(a) = κ·a^m`, `m ≠ 0`:
`𝒦(a) = κ·a^m/(2m)`. -/
theorem hasDerivAt_ampPrimitive_rpow {kappa m a : ℝ} (hm : m ≠ 0) (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => kappa * b ^ m / (2 * m))
      ((kappa * a ^ m) / (2 * a)) a := by
  have hpow : HasDerivAt (fun b : ℝ => b ^ m) (m * a ^ (m - 1)) a :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ha))
  have h := (hpow.const_mul kappa).div_const (2 * m)
  have hval : kappa * (m * a ^ (m - 1)) / (2 * m) = (kappa * a ^ m) / (2 * a) := by
    have hsub : a ^ (m - 1) = a ^ m / a := by
      rw [Real.rpow_sub ha, Real.rpow_one]
    rw [hsub]
    field_simp
  rwa [hval] at h

/-- The primitive for the constant law `F(a) = κ`: `𝒦(a) = (κ/2)·log a`. -/
theorem hasDerivAt_ampPrimitive_log {kappa a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun b : ℝ => kappa / 2 * Real.log b) (kappa / (2 * a)) a := by
  have h := (Real.hasDerivAt_log ha).const_mul (kappa / 2)
  have hval : kappa / 2 * a⁻¹ = kappa / (2 * a) := by
    field_simp
  rwa [hval] at h

/-! ## The accumulated marginal channel -/

/-- Two primitives of the same derivative have the same variation across a
closed interval. -/
theorem variation_eq_of_hasDerivAt_eq {f g f' : ℝ → ℝ} {t0 t1 : ℝ} (h01 : t0 ≤ t1)
    (hf : ∀ s ∈ Icc t0 t1, HasDerivAt f (f' s) s)
    (hg : ∀ s ∈ Icc t0 t1, HasDerivAt g (f' s) s) :
    f t1 - f t0 = g t1 - g t0 := by
  have hd : ∀ s ∈ Icc t0 t1, HasDerivAt (fun u => f u - g u) 0 s := by
    intro s hs
    simpa using (hf s hs).sub (hg s hs)
  have hd' : ∀ s ∈ Icc t0 t1, HasDerivAt (fun u => g u - f u) 0 s := by
    intro s hs
    simpa using (hg s hs).sub (hf s hs)
  have h1 := le_of_hasDerivAt_nonneg_on_Icc h01 hd (fun s _ => le_rfl)
  have h2 := le_of_hasDerivAt_nonneg_on_Icc h01 hd' (fun s _ => le_rfl)
  have : f t1 - g t1 = f t0 - g t0 := by linarith
  linarith

/-- **The accumulated marginal channel needs no absolute bound.**  If on the
window the marginal channel is the derivative of `𝒦(A) + ℛ` — the telescoped
primitive plus a primitive of the remainder — then its accumulated value over
the window is exactly the variation of that primitive, hence bounded by the
variation of `𝒦(A)` plus the accumulated remainder.  This is the statement
that replaces obligation (A-marg). -/
theorem marginal_channel_total_le {Kprim Rprim Mprim mchan : ℝ → ℝ}
    {t0 t1 Ctel Cmarg : ℝ} (h01 : t0 ≤ t1)
    (hM : ∀ s ∈ Icc t0 t1, HasDerivAt Mprim (mchan s) s)
    (hderiv : ∀ s ∈ Icc t0 t1, HasDerivAt (fun u => Kprim u + Rprim u) (mchan s) s)
    (hKtel : Kprim t1 - Kprim t0 ≤ Ctel)
    (hRm : Rprim t1 - Rprim t0 ≤ Cmarg) :
    Mprim t1 - Mprim t0 ≤ Ctel + Cmarg := by
  have heq := variation_eq_of_hasDerivAt_eq h01 hM hderiv
  rw [heq]
  linarith [hKtel, hRm]

end ClayNS
