/-
# Exponential decay of the similarity amplitude below the Reynolds threshold

The amplitude law of `SimilarityAmplitudeLaw.lean`,

  `½A′ = ⟪W,V⟫_ρ = −ν𝒟 − ½A − 𝒥`,

together with the relative bound `|𝒥| ≤ (LK/4ν)·A` of
`StationarySimilarityRigidity.lean`, is a *differential inequality* for the
Gaussian amplitude of the similarity profile:

  `½A′ ≤ −ν𝒟 − ½A + θA`,   `θ = LK/(4ν)`.

Below the Reynolds threshold `LK < 2ν` (that is `θ < ½`) this closes the A lane
in the small-data regime outright:

* the amplitude decays exponentially, `A(τ₁) ≤ A(τ₀)e^{−(1−2θ)(τ₁−τ₀)}`;
* the Gaussian Dirichlet energy has a finite total budget,
  `∫ν𝒟 ≤ ½A(τ₀)`;
* consequently a *normalized* similarity profile — the record-point
  normalization `A ≡ 1` of the blow-up construction — cannot exist on a window
  of positive length.

## Results

* `ClayNS.amplitude_differential_inequality` — the differential inequality,
  from the amplitude law and the relative bound;
* `ClayNS.amplitude_dirichlet_budget` — `∫ν𝒟 ≤ ½(A(τ₀) − A(τ₁)) ≤ ½A(τ₀)`;
* `ClayNS.amplitude_exponential_decay` — the exponential decay;
* `ClayNS.no_normalized_similarity_profile_of_smallReynolds` — no normalized
  profile below the threshold.

The scalar statements are proved at the level of calculus, so that the physical
theorems are exactly the amplitude law plus the relative bound and nothing
else.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityAmplitudeLaw

open MeasureTheory Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-! ## The differential inequality -/

/-- **The amplitude differential inequality.**  From the amplitude law
`½A′ = −ν𝒟 − ½𝒜 − 𝒥` and the relative bound `|𝒥| ≤ θ𝒜`,

  `½A′ ≤ −ν𝒟 − ½𝒜 + θ𝒜`. -/
theorem amplitude_differential_inequality {nu theta Ad Dv Av J : ℝ}
    (hlaw : Ad / 2 = -(nu * Dv) - (1 / 2) * Av - J) (hJ : |J| ≤ theta * Av) :
    Ad / 2 ≤ -(nu * Dv) - (1 / 2) * Av + theta * Av := by
  have : -J ≤ theta * Av := by
    have := neg_le_abs J
    linarith
  linarith [hlaw, this]

/-! ## The consequences of the differential inequality -/

/-- **The Dirichlet budget.**  If `½A′ ≤ −ν𝒟 − ½A + θA` with `θ ≤ ½`, `A ≥ 0`,
then the accumulated Gaussian Dirichlet energy is at most half the initial
amplitude. -/
theorem amplitude_dirichlet_budget {A Ad Pd Dv : ℝ → ℝ} {t0 t1 nu theta : ℝ}
    (h01 : t0 ≤ t1) (hth : theta ≤ 1 / 2)
    (hAnn : ∀ s ∈ Icc t0 t1, 0 ≤ A s)
    (hA : ∀ s ∈ Icc t0 t1, HasDerivAt A (Ad s) s)
    (hP : ∀ s ∈ Icc t0 t1, HasDerivAt Pd (nu * Dv s) s)
    (hineq : ∀ s ∈ Icc t0 t1, Ad s / 2 ≤ -(nu * Dv s) - (1 / 2) * A s + theta * A s) :
    Pd t1 - Pd t0 ≤ (1 / 2) * (A t0 - A t1) := by
  have hd : ∀ s ∈ Icc t0 t1,
      HasDerivAt (fun u => -((1 / 2) * A u + Pd u)) (-((1 / 2) * Ad s + nu * Dv s)) s := by
    intro s hs
    exact (((hA s hs).const_mul (1 / 2 : ℝ)).add (hP s hs)).neg
  have hnn : ∀ s ∈ Icc t0 t1, 0 ≤ -((1 / 2) * Ad s + nu * Dv s) := by
    intro s hs
    have h1 := hineq s hs
    have h2 := hAnn s hs
    nlinarith [h1, h2, hth]
  have hmono := le_of_hasDerivAt_nonneg_on_Icc h01 hd hnn
  linarith [hmono]

/-- **Exponential decay of the amplitude.**  If `½A′ ≤ −ν𝒟 − ½A + θA` with
`𝒟 ≥ 0`, `A ≥ 0` and `θ < ½`, then `A(τ₁) ≤ A(τ₀)e^{−(1−2θ)(τ₁−τ₀)}`. -/
theorem amplitude_exponential_decay {A Ad Dv : ℝ → ℝ} {t0 t1 nu theta : ℝ}
    (h01 : t0 ≤ t1) (hnu : 0 < nu)
    (hAnn : ∀ s ∈ Icc t0 t1, 0 ≤ A s) (hDnn : ∀ s ∈ Icc t0 t1, 0 ≤ Dv s)
    (hA : ∀ s ∈ Icc t0 t1, HasDerivAt A (Ad s) s)
    (hineq : ∀ s ∈ Icc t0 t1, Ad s / 2 ≤ -(nu * Dv s) - (1 / 2) * A s + theta * A s) :
    A t1 ≤ A t0 * Real.exp (-(1 - 2 * theta) * (t1 - t0)) := by
  set kap : ℝ := 1 - 2 * theta with hkap
  have hd : ∀ s ∈ Icc t0 t1,
      HasDerivAt (fun u => -(A u * Real.exp (kap * u)))
        (-(Ad s * Real.exp (kap * s) + A s * (kap * Real.exp (kap * s)))) s := by
    intro s hs
    have he : HasDerivAt (fun u : ℝ => Real.exp (kap * u)) (kap * Real.exp (kap * s)) s := by
      have h1 : HasDerivAt (fun u : ℝ => kap * u) kap s := by
        simpa using (hasDerivAt_id s).const_mul kap
      simpa [mul_comm] using h1.exp
    exact ((hA s hs).mul he).neg
  have hnn : ∀ s ∈ Icc t0 t1,
      0 ≤ -(Ad s * Real.exp (kap * s) + A s * (kap * Real.exp (kap * s))) := by
    intro s hs
    have h1 := hineq s hs
    have h2 := hAnn s hs
    have h3 := hDnn s hs
    have hexp : 0 < Real.exp (kap * s) := Real.exp_pos _
    have hAd : Ad s ≤ -kap * A s := by
      have : 0 ≤ nu * Dv s := mul_nonneg hnu.le h3
      rw [hkap]
      nlinarith [h1, this]
    nlinarith [hAd, hexp]
  have hmono := le_of_hasDerivAt_nonneg_on_Icc h01 hd hnn
  have hkey : A t1 * Real.exp (kap * t1) ≤ A t0 * Real.exp (kap * t0) := by linarith
  have hexp1 : 0 < Real.exp (kap * t1) := Real.exp_pos _
  have hfac : A t0 * Real.exp (-kap * (t1 - t0))
      = (A t0 * Real.exp (kap * t0)) / Real.exp (kap * t1) := by
    rw [eq_div_iff (ne_of_gt hexp1), mul_assoc, ← Real.exp_add]
    ring_nf
  rw [show -(1 - 2 * theta) * (t1 - t0) = -kap * (t1 - t0) by rw [hkap], hfac,
    le_div_iff₀ hexp1]
  linarith [hkey]

/-! ## No normalized profile below the threshold -/

/-- **A normalized similarity profile cannot exist below the Reynolds
threshold.**  If the amplitude is pinned at `1` on a window of positive length —
the record-point normalization of the blow-up construction — while satisfying
the differential inequality with `θ < ½`, we get a contradiction. -/
theorem no_normalized_similarity_profile_of_smallReynolds
    {A Ad Dv : ℝ → ℝ} {t0 t1 nu theta : ℝ}
    (h01 : t0 < t1) (hnu : 0 < nu) (hth : theta < 1 / 2)
    (hnorm : ∀ s ∈ Icc t0 t1, A s = 1)
    (hDnn : ∀ s ∈ Icc t0 t1, 0 ≤ Dv s)
    (hA : ∀ s ∈ Icc t0 t1, HasDerivAt A (Ad s) s)
    (hineq : ∀ s ∈ Icc t0 t1, Ad s / 2 ≤ -(nu * Dv s) - (1 / 2) * A s + theta * A s) :
    False := by
  have hAnn : ∀ s ∈ Icc t0 t1, 0 ≤ A s := fun s hs => by rw [hnorm s hs]; norm_num
  have hdecay := amplitude_exponential_decay h01.le hnu hAnn hDnn hA hineq
  rw [hnorm t1 (right_mem_Icc.2 h01.le), hnorm t0 (left_mem_Icc.2 h01.le)] at hdecay
  have hlt : Real.exp (-(1 - 2 * theta) * (t1 - t0)) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have h1 : 0 < 1 - 2 * theta := by linarith
    have h2 : 0 < t1 - t0 := by linarith
    nlinarith [h1, h2]
  linarith [hdecay, hlt]


/-! ## The physical statements -/

/-- **The physical amplitude differential inequality.**  For a compactly
supported, divergence-free `C²` profile evolving by the similarity equation
with a Bernoulli head dominated by `K|V|`,

  `½A′ ≤ −ν𝒟 − ½𝒜 + (LK/4ν)𝒜`. -/
theorem gauss_amplitude_differential_inequality {nu L K Ad : ℝ} (hnu : 0 < nu) (hL : 0 < L)
    {V W : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖)
    (heq : IsSimilarityEvolution nu V W p)
    (hC : (∫ y : E3, gaussWeight nu y * ⟪W y, V y⟫) = Ad / 2) :
    Ad / 2 ≤ -(nu * gaussDirichlet nu V) - (1 / 2) * gaussAmp nu V
      + (L * K / (4 * nu)) * gaussAmp nu V := by
  have hlaw := gaussMarginalJ_eq_of_ampDeriv hnu hV hp hdiv hL hsupp heq hC
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) :=
    integrable_gauss_amp (nu := nu) hV1.continuous hsupp
  have hJ := gaussMarginalJ_relative_bound hnu hL.le hsupp hhead hI3
  refine amplitude_differential_inequality (J := gaussMarginalJ nu V p) ?_ hJ
  linarith [hlaw]

/-- **No normalized similarity profile below the Reynolds threshold.**  A family
of compactly supported, divergence-free `C²` similarity profiles with dominated
Bernoulli heads, evolving by the similarity equation on a window of positive
length with amplitude pinned at `1` — the record-point normalization of the
blow-up construction — cannot exist once `L·K < 2ν`. -/
theorem smallReynolds_no_normalized_similarity_family
    {nu L K : ℝ} (hnu : 0 < nu) (hL : 0 < L) (hsmall : L * K < 2 * nu)
    {Vf Wf : ℝ → (E3 → E3)} {pf : ℝ → (E3 → ℝ)} {A Ad : ℝ → ℝ} {t0 t1 : ℝ}
    (h01 : t0 < t1)
    (hprofC2 : ∀ s ∈ Icc t0 t1, ContDiff ℝ (2 : ℕ) (Vf s))
    (hprofP : ∀ s ∈ Icc t0 t1, ContDiff ℝ (1 : ℕ) (pf s))
    (hdiv : ∀ s ∈ Icc t0 t1, ∀ y, divSpace (Vf s) y = 0)
    (hsupp : ∀ s ∈ Icc t0 t1, ∀ y : E3, L ≤ ‖y‖ → Vf s y = 0)
    (hhead : ∀ s ∈ Icc t0 t1, ∀ y : E3, |‖Vf s y‖ ^ 2 + 2 * pf s y| ≤ K * ‖Vf s y‖)
    (heq : ∀ s ∈ Icc t0 t1, IsSimilarityEvolution nu (Vf s) (Wf s) (pf s))
    (hAdef : ∀ s ∈ Icc t0 t1, A s = gaussAmp nu (Vf s))
    (hAderiv : ∀ s ∈ Icc t0 t1, HasDerivAt A (Ad s) s)
    (hC : ∀ s ∈ Icc t0 t1, (∫ y : E3, gaussWeight nu y * ⟪Wf s y, Vf s y⟫) = Ad s / 2)
    (hnorm : ∀ s ∈ Icc t0 t1, A s = 1) : False := by
  refine no_normalized_similarity_profile_of_smallReynolds (nu := nu)
    (theta := L * K / (4 * nu)) (Dv := fun s => gaussDirichlet nu (Vf s))
    h01 hnu ?_ hnorm (fun s _ => gaussDirichlet_nonneg nu (Vf s)) hAderiv ?_
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * nu)]
    linarith
  · intro s hs
    have h := gauss_amplitude_differential_inequality (nu := nu) (L := L) (K := K)
      (Ad := Ad s) hnu hL (hprofC2 s hs) (hprofP s hs) (hdiv s hs) (hsupp s hs)
      (hhead s hs) (heq s hs) (hC s hs)
    rw [← hAdef s hs] at h
    exact h

end ClayNS
