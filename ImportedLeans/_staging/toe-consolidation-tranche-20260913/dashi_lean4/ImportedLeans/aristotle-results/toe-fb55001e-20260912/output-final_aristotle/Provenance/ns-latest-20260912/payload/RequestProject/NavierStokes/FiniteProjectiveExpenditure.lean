/-
# Finite projective expenditure and the almost-stationary sequence

If the A lane closes, the blow-up profile is not merely a bounded ancient
solution: its *normalized* similarity profile has finite total projective
expenditure,

  `∫₀^∞ ‖∂_τ V̂‖²_ρ dτ < ∞`,   `‖∂_τ V̂‖²_ρ = Δ/A² = ‖W_⊥‖²/A`.

This file turns that into usable information about the profile.

## What is proved

* `ClayNS.projective_speed_eq_transverse_div_amp` — the pointwise conversion
  `‖∂_τ V̂‖² = ‖W − P_VW‖²/A`: the projective speed is the transverse speed
  divided by the amplitude, so the transverse expenditure of the closure and
  the projective expenditure differ only by the amplitude.
* `ClayNS.projective_expenditure_of_transverse_expenditure` — consequently, on
  a window where the amplitude stays above `a₀ > 0`, finite transverse
  expenditure gives finite projective expenditure with constant `1/a₀`.
* `ClayNS.exists_small_value_of_finite_expenditure` — the elementary but
  essential step: a nonnegative density with a *bounded* primitive dips below
  every `ε` beyond every time.
* `ClayNS.exists_seq_tendsto_zero_of_finite_expenditure` — hence there is a
  sequence of similarity times `τ_j → ∞` along which the projective speed
  tends to `0`: **the profile is asymptotically stationary along a
  subsequence**.
* `ClayNS.finite_projective_expenditure_ancient_rigidity` — the resulting
  architecture of the C lane: finite expenditure ⟹ almost-stationary sequence
  ⟹ (with compactness and equation passage) a stationary similarity limit ⟹
  (with rigidity for stationary limits) the profile is trivial along that
  sequence.  Compactness/equation passage and stationary rigidity enter as
  explicit hypotheses; the first arrow is proved here.

This replaces the universal Liouville statement `ClayNS.DirectionalLevelDrop`
by a statement about the *actual* blow-up profile, which carries the extra
information that its projective motion is summable.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianSimilarityInteractionClosure

open Filter Set Topology
open RealInnerProductSpace

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Projective speed versus transverse speed -/

/-- **`‖∂_τ V̂‖² = ‖W − P_VW‖²/A`.**  The squared speed of the normalized
profile is the transverse (scale-Gram) speed divided by the amplitude. -/
theorem projective_speed_eq_transverse_div_amp {V W : E} (hA : (0 : ℝ) < ⟪V, V⟫) :
    ‖(Real.sqrt ⟪V, V⟫)⁻¹ • W - (⟪V, W⟫ / (⟪V, V⟫ * Real.sqrt ⟪V, V⟫)) • V‖ ^ 2
      = ‖W - amplitudeProj V W‖ ^ 2 / ⟪V, V⟫ := by
  rw [projective_speed_sq V W hA, amplitude_transverse_norm_sq hA W]
  field_simp

/-- **Finite transverse expenditure gives finite projective expenditure.**  On a
window where the amplitude stays above `a₀ > 0`,

  `∫‖∂_τ V̂‖² ≤ (1/a₀)·∫‖W_⊥‖²`,

stated between primitives.  Combined with
`ClayNS.gaussian_similarity_interaction_closure` this is the statement
`∫₀^∞‖∂_τ V̂‖² < ∞` for the actual blow-up profile. -/
theorem projective_expenditure_of_transverse_expenditure
    {Ecal Pcal q amp : ℝ → ℝ} {t0 t1 a0 : ℝ} (h01 : t0 ≤ t1) (ha0 : 0 < a0)
    (hq : ∀ s ∈ Icc t0 t1, 0 ≤ q s)
    (hamp : ∀ s ∈ Icc t0 t1, a0 ≤ amp s)
    (hE : ∀ s ∈ Icc t0 t1, HasDerivAt Ecal (q s) s)
    (hP : ∀ s ∈ Icc t0 t1, HasDerivAt Pcal (q s / amp s) s) :
    Pcal t1 - Pcal t0 ≤ (1 / a0) * (Ecal t1 - Ecal t0) := by
  have hd : ∀ s ∈ Icc t0 t1,
      HasDerivAt (fun u => (1 / a0) * Ecal u - Pcal u) ((1 / a0) * q s - q s / amp s) s :=
    fun s hs => ((hE s hs).const_mul (1 / a0)).sub (hP s hs)
  have hnn : ∀ s ∈ Icc t0 t1, 0 ≤ (1 / a0) * q s - q s / amp s := by
    intro s hs
    have hqs := hq s hs
    have hamps := hamp s hs
    have hpos : 0 < amp s := lt_of_lt_of_le ha0 hamps
    have h1 : q s / amp s ≤ q s / a0 := div_le_div_of_nonneg_left hqs ha0 hamps
    have h2 : q s / a0 = (1 / a0) * q s := by ring
    linarith [h1, h2.symm.le]
  have := le_of_hasDerivAt_nonneg_on_Icc h01 hd hnn
  linarith

/-! ## A summable density dips below every level -/

/-- **The elementary consequence of finite expenditure.**  If `f ≥ 0` has a
primitive bounded above by `C`, then beyond every time `T` there is a time at
which `f` is below any prescribed `ε > 0`.  (Otherwise the primitive would grow
linearly.) -/
theorem exists_small_value_of_finite_expenditure {f Fp : ℝ → ℝ} {C : ℝ}
    (hF : ∀ s, HasDerivAt Fp (f s) s) (hb : ∀ s, Fp s ≤ C)
    {eps : ℝ} (heps : 0 < eps) (T : ℝ) :
    ∃ tau : ℝ, T ≤ tau ∧ f tau < eps := by
  by_contra hcon
  push_neg at hcon
  set S : ℝ := T + (C - Fp T) / eps + 1 with hS
  have hTS : T ≤ S := by
    have hCF : 0 ≤ C - Fp T := by linarith [hb T]
    have : 0 ≤ (C - Fp T) / eps := div_nonneg hCF heps.le
    rw [hS]; linarith
  have hd : ∀ u ∈ Icc T S, HasDerivAt (fun v => Fp v - eps * v) (f u - eps) u := by
    intro u _
    simpa using (hF u).sub ((hasDerivAt_id u).const_mul eps)
  have hnn : ∀ u ∈ Icc T S, 0 ≤ f u - eps := by
    intro u hu
    have := hcon u hu.1
    linarith
  have hmono := le_of_hasDerivAt_nonneg_on_Icc hTS hd hnn
  -- `Fp T - εT ≤ Fp S - εS`, i.e. `ε(S − T) ≤ Fp S − Fp T ≤ C − Fp T`
  have hgap : eps * (S - T) ≤ Fp S - Fp T := by nlinarith [hmono]
  have hFS := hb S
  have hexp : eps * (S - T) = (C - Fp T) + eps := by
    rw [hS]
    field_simp
    ring
  nlinarith [hgap, hFS, hexp]

/-- **The almost-stationary sequence.**  Finite total expenditure of a
nonnegative density produces similarity times `τ_j → ∞` along which the density
tends to zero. -/
theorem exists_seq_tendsto_zero_of_finite_expenditure {f Fp : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s, 0 ≤ f s) (hF : ∀ s, HasDerivAt Fp (f s) s) (hb : ∀ s, Fp s ≤ C) :
    ∃ tau : ℕ → ℝ, Tendsto tau atTop atTop ∧
      Tendsto (fun j => f (tau j)) atTop (𝓝 0) := by
  have hstep : ∀ j : ℕ, ∃ s : ℝ, (j : ℝ) ≤ s ∧ f s < 1 / ((j : ℝ) + 1) := by
    intro j
    exact exists_small_value_of_finite_expenditure hF hb (by positivity) (j : ℝ)
  choose tau htau hfast using hstep
  refine ⟨tau, ?_, ?_⟩
  · exact tendsto_atTop_mono htau tendsto_natCast_atTop_atTop
  · refine squeeze_zero (fun j => hf (tau j)) (fun j => (hfast j).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## The C-lane architecture -/

/-- **`FiniteProjectiveExpenditureAncientRigidity`, as a reduction.**

Given

* finite total projective expenditure of the normalized profile (`hb`), which
  the A lane supplies,
* compactness together with passage of the equation to the limit (`hcpt`): any
  sequence of similarity times along which the projective speed vanishes has a
  subsequence along which the normalized profile converges to a *stationary*
  limit,
* rigidity for stationary limits (`hrigid`): a stationary limit of the
  normalized profile is the trivial one,

the normalized profile converges to the trivial profile along a sequence of
similarity times going to infinity.

The first arrow — finite expenditure to an almost-stationary sequence — is
proved here; `hcpt` and `hrigid` are the two remaining C-lane obligations, and
they are strictly weaker than a Liouville theorem for *every* bounded ancient
solution, because they only ever see profiles with summable projective
motion. -/
theorem finite_projective_expenditure_ancient_rigidity
    {X : Type*} [TopologicalSpace X] {Vhat : ℝ → X} {Stationary : X → Prop} {triv : X}
    {f Fp : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s, 0 ≤ f s) (hF : ∀ s, HasDerivAt Fp (f s) s) (hb : ∀ s, Fp s ≤ C)
    (hcpt : ∀ tau : ℕ → ℝ, Tendsto tau atTop atTop →
      Tendsto (fun j => f (tau j)) atTop (𝓝 0) →
      ∃ (sub : ℕ → ℕ) (Vinf : X), StrictMono sub ∧
        Tendsto (fun j => Vhat (tau (sub j))) atTop (𝓝 Vinf) ∧ Stationary Vinf)
    (hrigid : ∀ Vinf : X, Stationary Vinf → Vinf = triv) :
    ∃ sigma : ℕ → ℝ, Tendsto sigma atTop atTop ∧
      Tendsto (fun j => Vhat (sigma j)) atTop (𝓝 triv) := by
  obtain ⟨tau, htau, hzero⟩ := exists_seq_tendsto_zero_of_finite_expenditure hf hF hb
  obtain ⟨sub, Vinf, hsub, hconv, hstat⟩ := hcpt tau htau hzero
  refine ⟨fun j => tau (sub j), ?_, ?_⟩
  · exact htau.comp hsub.tendsto_atTop
  · rw [← hrigid Vinf hstat]
    exact hconv

end ClayNS
