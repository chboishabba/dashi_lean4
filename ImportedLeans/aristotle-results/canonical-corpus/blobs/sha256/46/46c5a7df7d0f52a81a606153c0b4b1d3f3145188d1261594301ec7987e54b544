/-
# The A arrow from the near/far relative absorption package

`SimilarityScaleCharge.lean` derives `A_dyn` from the similarity equation, but
it still carries **two** quantitative inputs:

* `hrembound` — a uniform bound on the accumulated Young remainder
  `∫‖N‖²/(4η)` (obligation **A1**), and
* `hdrop` — a uniform bound on the similarity energy drop
  `ℋ(τ₀) − ℋ(τ₁)` (obligation **A2**).

This file replaces both by the single near/far relative-absorption package of
`SimilarityNearFarAbsorption.lean`:

* `N = N_near + N_far + N_marg` with `N_marg` marginal (so it is *computed*,
  through the exact channel `⟪N,PW⟫`, never estimated);
* `|⟪N_near^⊥, W^⊥⟫| ≤ η‖W^⊥‖²` with `η < 1` — the near interaction is charged
  **relatively** to the transverse expenditure already present;
* `|⟪N_far^⊥, W^⊥⟫| ≤ R_far(τ)` with a finite accumulated primitive — the far
  interaction is a summable tail;
* the similarity energy is bounded at the **initial** similarity time only.

The energy drop is then *derived*, using that the Dirichlet form is positive
semidefinite, so `ℋ ≥ 0`: the endpoint at the small-scale end of the window
needs no bound of its own.

* `ClayNS.clay_A_dyn_of_nearfar_relative_absorption` — `A_dyn` from that
  package, for an arbitrary family of marginal projections.
* `ClayNS.clay_A_dyn_of_amplitude_nearfar_absorption` — the same with the
  marginal direction taken to be the physical amplitude direction `ℝ·V(τ)`:
  the projection hypotheses are discharged, the coercive quantity is the
  scale-Gram defect `(AB − C²)/A`, and the marginal remainder is the exactly
  computable scalar `⟪N,V⟫⟪V,W⟫/⟪V,V⟫`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityNearFarAbsorption
import RequestProject.NavierStokes.SimilarityScaleCharge

open Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- **`A_dyn` from near/far relative absorption and a one-endpoint energy
bound.**

Compared with `ClayNS.clay_A_dyn_of_similarity_equation`:

* the absolute Young remainder `‖N‖²/(4η)` is gone; the near interaction is
  paid by a fraction `η < 1` of the transverse speed it is measured against,
  and only the far tail and the exactly computed marginal channel accumulate;
* the uniform energy-drop hypothesis is gone; it is replaced by a bound on the
  similarity energy at the *initial* similarity time, the drop being derived
  from positivity of the Dirichlet form.

The coercive quantity carried through the cascade is the **transverse** speed
`‖W − PW‖²`, which is exactly the projective/Gram speed of
`ClayNS.projective_gram_speed`, so the domination hypothesis `hdom` is the
identity (P) rather than a new estimate. -/
theorem clay_A_dyn_of_nearfar_relative_absorption
    {Ehil : Type*} [NormedAddCommGroup Ehil] [InnerProductSpace ℝ Ehil]
    {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ} {x : ℕ → E3}
    {F Qd Delta Rem Phi Psi Theta Ecal Rcal Rfar : ℕ → ℝ → ℝ}
    {Vsim Wsim Nnear Nfar Nmarg : ℕ → ℝ → Ehil}
    {eps cinv Crem K eta Cdrop Cabs : ℝ}
    (bil : Ehil →L[ℝ] Ehil →L[ℝ] ℝ) (hsymm : ∀ u v : Ehil, bil u v = bil v u)
    (hpsd : ∀ v : Ehil, 0 ≤ bil v v)
    (P : ℕ → ℝ → (Ehil →L[ℝ] Ehil))
    (hidem : ∀ k s, ∀ v : Ehil, P k s (P k s v) = P k s v)
    (hsym : ∀ k s, ∀ u v : Ehil, ⟪P k s u, v⟫ = ⟪u, P k s v⟫)
    (heps : 0 < eps) (hM : ∀ k, 0 < M k) (hcinv : 0 ≤ cinv)
    (hK : 0 ≤ K) (heta1 : eta < 1)
    (hle : ∀ k, 1 / M k ≤ cascadeStart (M k))
    (hpos : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), 0 < QgradCyl (G k) (t k) (x k) r)
    (hderiv : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (fun s => QgradCyl (G k) (t k) (x k) s) (Qd k r) r)
    (hexact : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), r * Qd k r = F k r)
    (hsplit : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      max (F k r) 0 ≤ cinv * Delta k r + Rem k r)
    (hPhi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Phi k) (nsLogDefect (F k) (fun s => QgradCyl (G k) (t k) (x k) s) r) r)
    (hPsi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Psi k) (Delta k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hTheta : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Theta k) (Rem k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    -- the similarity dynamics
    (hV : ∀ k s, HasDerivAt (Vsim k) (Wsim k s) s)
    (heq : ∀ k s, ∀ w : Ehil, ⟪Wsim k s, w⟫
      = -bil (Vsim k s) w - (1 / 2) * ⟪Vsim k s, w⟫
        - ⟪Nnear k s + Nfar k s + Nmarg k s, w⟫)
    -- the near/far/marginal package
    (hmarg : ∀ k s, P k s (Nmarg k s) = Nmarg k s)
    (hnear : ∀ k s, |⟪Nnear k s - P k s (Nnear k s), Wsim k s - P k s (Wsim k s)⟫|
      ≤ eta * ‖Wsim k s - P k s (Wsim k s)‖ ^ 2)
    (hfar : ∀ k s, |⟪Nfar k s - P k s (Nfar k s), Wsim k s - P k s (Wsim k s)⟫| ≤ Rfar k s)
    (hEc : ∀ k, ∀ s : ℝ, HasDerivAt (Ecal k) (‖Wsim k s - P k s (Wsim k s)‖ ^ 2) s)
    (hRc : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Rcal k)
        (|⟪Nnear k s + Nfar k s + Nmarg k s, P k s (Wsim k s)⟫| + Rfar k s) s)
    (hrembound : ∀ k, Rcal k (-Real.log (1 / M k))
      - Rcal k (-Real.log (cascadeStart (M k))) ≤ Cabs)
    -- the single endpoint bound on the similarity energy
    (hinit : ∀ k,
      (1 / 2) * bil (Vsim k (-Real.log (cascadeStart (M k))))
          (Vsim k (-Real.log (cascadeStart (M k))))
        + (1 / 4) * ⟪Vsim k (-Real.log (cascadeStart (M k))),
            Vsim k (-Real.log (cascadeStart (M k)))⟫ ≤ Cdrop)
    (hdom : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      Delta k r / QgradCyl (G k) (t k) (x k) r
        ≤ K * ‖Wsim k (-Real.log r) - P k (-Real.log r) (Wsim k (-Real.log r))‖ ^ 2)
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  refine clay_A_dyn_of_similarity_absorption
    (Hcal := fun k s => (1 / 2) * bil (Vsim k s) (Vsim k s) + (1 / 4) * ⟪Vsim k s, Vsim k s⟫)
    (Ecal := Ecal) (Rcal := Rcal)
    (Hd := fun k s => -⟪Wsim k s, Wsim k s⟫ - ⟪Nnear k s + Nfar k s + Nmarg k s, Wsim k s⟫)
    (q := fun k s => ‖Wsim k s - P k s (Wsim k s)‖ ^ 2)
    (rem := fun k s => |⟪Nnear k s + Nfar k s + Nmarg k s, P k s (Wsim k s)⟫| + Rfar k s)
    (Cdrop := Cdrop) (Cabs := Cabs)
    heps hM hcinv hK heta1 hle hpos hderiv hexact hsplit hPhi hPsi hTheta
    ?_ ?_ hEc hRc hrembound ?_ hdom hrem hstart
  · intro k s _
    exact similarity_energy_identity bil hsymm (hV k s) (heq k s)
  · intro k s _
    exact similarity_energy_deriv_le_transverse_nearfar (P k s) (hidem k s) (hsym k s)
      (Nnear k s) (Nfar k s) (Nmarg k s) (Wsim k s) (hmarg k s) (hnear k s) (hfar k s)
  · intro k
    have hnn := similarity_energy_nonneg bil hpsd (Vsim k (-Real.log (1 / M k)))
    linarith [hinit k]

/-! ## The physical marginal direction -/

/-- **`A_dyn` with the marginal channel taken along the amplitude direction.**

Here the projection is not an abstract input: it is the orthogonal projection
`ClayNS.amplitudeProj` onto `ℝ·V(τ)`, the direction that carries no
coercivity.  Its idempotence and symmetry are discharged, and the coercive
transverse quantity becomes literally the scale-Gram defect

  `‖W − P W‖² = (AB − C²)/A`,  `A = ⟪V,V⟫`, `B = ⟪W,W⟫`, `C = ⟪V,W⟫`,

so `hdom` is now stated directly in terms of the Gram defect of the pair
`(V, V_τ)` (identity (P) of `SimilarityEnergy.lean`), and the marginal
remainder is the scalar `⟪N,V⟫⟪V,W⟫/⟪V,V⟫`, which
`GaussianMarginalChannel.lean` computes exactly for the physical nonlinear and
pressure terms. -/
theorem clay_A_dyn_of_amplitude_nearfar_absorption
    {Ehil : Type*} [NormedAddCommGroup Ehil] [InnerProductSpace ℝ Ehil]
    {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ} {x : ℕ → E3}
    {F Qd Delta Rem Phi Psi Theta Ecal Rcal Rfar : ℕ → ℝ → ℝ}
    {Vsim Wsim Nnear Nfar Nmarg : ℕ → ℝ → Ehil}
    {eps cinv Crem K eta Cdrop Cabs : ℝ}
    (bil : Ehil →L[ℝ] Ehil →L[ℝ] ℝ) (hsymm : ∀ u v : Ehil, bil u v = bil v u)
    (hpsd : ∀ v : Ehil, 0 ≤ bil v v)
    (hVpos : ∀ k s, (0 : ℝ) < ⟪Vsim k s, Vsim k s⟫)
    (heps : 0 < eps) (hM : ∀ k, 0 < M k) (hcinv : 0 ≤ cinv)
    (hK : 0 ≤ K) (heta1 : eta < 1)
    (hle : ∀ k, 1 / M k ≤ cascadeStart (M k))
    (hpos : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), 0 < QgradCyl (G k) (t k) (x k) r)
    (hderiv : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (fun s => QgradCyl (G k) (t k) (x k) s) (Qd k r) r)
    (hexact : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), r * Qd k r = F k r)
    (hsplit : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      max (F k r) 0 ≤ cinv * Delta k r + Rem k r)
    (hPhi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Phi k) (nsLogDefect (F k) (fun s => QgradCyl (G k) (t k) (x k) s) r) r)
    (hPsi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Psi k) (Delta k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hTheta : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Theta k) (Rem k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hV : ∀ k s, HasDerivAt (Vsim k) (Wsim k s) s)
    (heq : ∀ k s, ∀ w : Ehil, ⟪Wsim k s, w⟫
      = -bil (Vsim k s) w - (1 / 2) * ⟪Vsim k s, w⟫
        - ⟪Nnear k s + Nfar k s + Nmarg k s, w⟫)
    (hmarg : ∀ k s, amplitudeProj (Vsim k s) (Nmarg k s) = Nmarg k s)
    (hnear : ∀ k s,
      |⟪Nnear k s - amplitudeProj (Vsim k s) (Nnear k s),
        Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)⟫|
      ≤ eta * ((⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
          / ⟪Vsim k s, Vsim k s⟫))
    (hfar : ∀ k s,
      |⟪Nfar k s - amplitudeProj (Vsim k s) (Nfar k s),
        Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)⟫| ≤ Rfar k s)
    (hEc : ∀ k, ∀ s : ℝ, HasDerivAt (Ecal k)
      ((⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
        / ⟪Vsim k s, Vsim k s⟫) s)
    (hRc : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Rcal k)
        (|⟪Nnear k s + Nfar k s + Nmarg k s, Vsim k s⟫ * ⟪Vsim k s, Wsim k s⟫
            / ⟪Vsim k s, Vsim k s⟫| + Rfar k s) s)
    (hrembound : ∀ k, Rcal k (-Real.log (1 / M k))
      - Rcal k (-Real.log (cascadeStart (M k))) ≤ Cabs)
    (hinit : ∀ k,
      (1 / 2) * bil (Vsim k (-Real.log (cascadeStart (M k))))
          (Vsim k (-Real.log (cascadeStart (M k))))
        + (1 / 4) * ⟪Vsim k (-Real.log (cascadeStart (M k))),
            Vsim k (-Real.log (cascadeStart (M k)))⟫ ≤ Cdrop)
    (hdom : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      Delta k r / QgradCyl (G k) (t k) (x k) r
        ≤ K * ((⟪Vsim k (-Real.log r), Vsim k (-Real.log r)⟫
              * ⟪Wsim k (-Real.log r), Wsim k (-Real.log r)⟫
            - ⟪Vsim k (-Real.log r), Wsim k (-Real.log r)⟫ ^ 2)
          / ⟪Vsim k (-Real.log r), Vsim k (-Real.log r)⟫))
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  have htr : ∀ k s, ‖Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)‖ ^ 2
      = (⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
        / ⟪Vsim k s, Vsim k s⟫ := fun k s =>
    amplitude_transverse_norm_sq (hVpos k s) (Wsim k s)
  refine clay_A_dyn_of_nearfar_relative_absorption
    (Ecal := Ecal) (Rcal := Rcal) (Rfar := Rfar)
    (Nnear := Nnear) (Nfar := Nfar) (Nmarg := Nmarg)
    bil hsymm hpsd (fun k s => amplitudeProj (Vsim k s))
    (fun k s => amplitudeProj_idem (hVpos k s))
    (fun k s => amplitudeProj_symm (Vsim k s))
    heps hM hcinv hK heta1 hle hpos hderiv hexact hsplit hPhi hPsi hTheta hV heq
    hmarg ?_ hfar ?_ ?_ hrembound hinit ?_ hrem hstart
  · intro k s
    rw [htr k s]
    exact hnear k s
  · intro k s
    rw [htr k s]
    exact hEc k s
  · intro k s hs
    have := hRc k s hs
    rwa [← amplitude_marginal_channel (Vsim k s) (Nnear k s + Nfar k s + Nmarg k s)
      (Wsim k s)] at this
  · intro k r hr
    rw [htr k (-Real.log r)]
    exact hdom k r hr

end ClayNS
