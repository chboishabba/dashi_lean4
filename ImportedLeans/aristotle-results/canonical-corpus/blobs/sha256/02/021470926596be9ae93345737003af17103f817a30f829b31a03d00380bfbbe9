/-
# The A arrow with `hstar` eliminated

`ScaleGramChargeAssembly.lean` proves `A-charge ⟹ A_dyn`, but takes the
telescopic payment of the scale-Gram expenditure,

  `hstar :  Ψ_k(b_k) − Ψ_k(a_k) ≤ C_*`,

as an unproved analytic input: a *global integral* statement about the
scale-Gram defect over the whole cascade range.

`SimilarityEnergy.lean` shows that this quantity is a scale-space expenditure
and can be paid by a single energy drop.  This file carries that through the
cascade, so that `A_dyn` follows without ever assuming `hstar`:

* `ClayNS.clay_A_dyn_of_similarity_absorption` — same conclusion as
  `ClayNS.clay_A_dyn_of_scaleGram_absorption`, with `hstar` replaced by the
  similarity-variable package
  1. `hH` — the similarity energy `ℋ_k` has derivative `ℋ_k′` (identity (S) of
     `SimilarityEnergy.lean`; exact calculus once the equation is written in
     similarity variables);
  2. `hHle` — the marginal/transverse absorption
     `ℋ_k′ ≤ −(1−η)·q_k + ℛ_k`, i.e. the nonlinear and pressure pairing is
     absorbed into a fraction of the transverse speed plus a remainder;
  3. `hdom` — the scale-Gram ratio at radius `r` is at most `K` times the
     projective speed at similarity time `−log r` (this is the identity (P),
     `ClayNS.projective_gram_speed`);
  4. `hdrop`, `hrembound` — the energy drop and the remainder are bounded
     uniformly along the singular sequence.

Nothing here is a new physical assumption: 1 and 3 are the two exact
identities, and 2 is the single remaining physical estimate.  The point of the
file is the bookkeeping metric: the A side now has **one** unproved continuum
estimate (absorption) plus **one** uniform bound (the energy drop), where it
previously had the two independent inputs `hFG` and `hstar`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityEnergy
import RequestProject.NavierStokes.SimilarityAbsorption

open Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- **`A-charge ⟹ A_dyn` with the telescopic payment derived, not assumed.**

The scale-Gram expenditure is paid by the similarity-variable energy drop:
`hstar` of `ClayNS.clay_A_dyn_of_scaleGram_absorption` is *proved* here from
the similarity energy identity, the absorption estimate, and the pointwise
identification of the scale-Gram ratio with the projective speed. -/
theorem clay_A_dyn_of_similarity_absorption {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ}
    {t : ℕ → ℝ} {x : ℕ → E3} {F Qd Delta Rem Phi Psi Theta : ℕ → ℝ → ℝ}
    {Hcal Ecal Rcal Hd q rem : ℕ → ℝ → ℝ}
    {eps cinv Crem K eta Cdrop Cabs : ℝ}
    (heps : 0 < eps) (hM : ∀ k, 0 < M k) (hcinv : 0 ≤ cinv)
    (hK : 0 ≤ K) (heta : eta < 1)
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
    -- the similarity-variable package replacing `hstar`
    (hH : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Hcal k) (Hd k s) s)
    (hHle : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      Hd k s ≤ -(1 - eta) * q k s + rem k s)
    (hE : ∀ k, ∀ s : ℝ, HasDerivAt (Ecal k) (q k s) s)
    (hR : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Rcal k) (rem k s) s)
    (hrembound : ∀ k, Rcal k (-Real.log (1 / M k))
      - Rcal k (-Real.log (cascadeStart (M k))) ≤ Cabs)
    (hdrop : ∀ k, Hcal k (-Real.log (cascadeStart (M k)))
      - Hcal k (-Real.log (1 / M k)) ≤ Cdrop)
    (hdom : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      Delta k r / QgradCyl (G k) (t k) (x k) r ≤ K * q k (-Real.log r))
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  have h1e : 0 < 1 - eta := by linarith
  have hstar : ∀ k, Psi k (cascadeStart (M k)) - Psi k (1 / M k)
      ≤ K * ((Cdrop + Cabs) / (1 - eta)) := by
    intro k
    have hak : (0 : ℝ) < 1 / M k := by have := hM k; positivity
    have hpay := scaleGram_payment_of_similarity_absorption
      (Delta := Delta k) (Dsc := fun r => QgradCyl (G k) (t k) (x k) r) (Psi := Psi k)
      (Hcal := Hcal k) (Ecal := Ecal k) (Rcal := Rcal k) (Hd := Hd k) (q := q k)
      (rem := rem k) (a := 1 / M k) (b := cascadeStart (M k)) (K := K) (eta := eta)
      (Crem := Cabs) hak (hle k) hK heta (hpos k) (hPsi k) (hH k) (hHle k)
      (hE k) (hR k) (hrembound k) (hdom k)
    have hmono : (Hcal k (-Real.log (cascadeStart (M k)))
        - Hcal k (-Real.log (1 / M k)) + Cabs) / (1 - eta)
        ≤ (Cdrop + Cabs) / (1 - eta) := by
      rw [div_le_div_iff_of_pos_right h1e]
      linarith [hdrop k]
    calc Psi k (cascadeStart (M k)) - Psi k (1 / M k)
        ≤ K * ((Hcal k (-Real.log (cascadeStart (M k)))
            - Hcal k (-Real.log (1 / M k)) + Cabs) / (1 - eta)) := hpay
      _ ≤ K * ((Cdrop + Cabs) / (1 - eta)) := by
          exact mul_le_mul_of_nonneg_left hmono hK
  exact clay_A_dyn_of_scaleGram_absorption heps hM hcinv hle hpos hderiv hexact hsplit
    hPhi hPsi hTheta hstar hrem hstart

/-! ## The same, starting from the similarity equation itself -/

/-- **`A_dyn` from the similarity equation and a finite nonlinear budget.**

Here nothing about the energy is assumed: the similarity energy, its
derivative and the absorption are all produced from

* `hV`  — the solution is differentiable in similarity time;
* `heq` — it satisfies the weak form of the similarity equation, with `N` the
  nonlinear and pressure terms;

so the only remaining inputs on this side are quantitative:

* `hdrop`     — a uniform bound on the similarity energy drop;
* `hrembound` — a uniform bound on the total weighted mass of `N` over the
  window (the remainder `‖N‖²/(4η)`);
* `hdom`      — the scale-Gram ratio is at most `K` times the scale speed,
  which is the identity `ClayNS.projective_gram_speed`;
* `hsplit`    — the flux splitting, unchanged.

This is the A side with a single physical estimate (the size of `N`) in place
of the two independent analytic inputs it previously carried. -/
theorem clay_A_dyn_of_similarity_equation
    {Ehil : Type*} [NormedAddCommGroup Ehil] [InnerProductSpace ℝ Ehil]
    {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ} {x : ℕ → E3}
    {F Qd Delta Rem Phi Psi Theta Ecal Rcal : ℕ → ℝ → ℝ}
    {Vsim Wsim Nsim : ℕ → ℝ → Ehil}
    {eps cinv Crem K eta Cdrop Cabs : ℝ}
    (bil : Ehil →L[ℝ] Ehil →L[ℝ] ℝ) (hsymm : ∀ u v : Ehil, bil u v = bil v u)
    (heps : 0 < eps) (hM : ∀ k, 0 < M k) (hcinv : 0 ≤ cinv)
    (hK : 0 ≤ K) (heta0 : 0 < eta) (heta1 : eta < 1)
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
      = -bil (Vsim k s) w - (1 / 2) * ⟪Vsim k s, w⟫ - ⟪Nsim k s, w⟫)
    (hEc : ∀ k, ∀ s : ℝ, HasDerivAt (Ecal k) (‖Wsim k s‖ ^ 2) s)
    (hRc : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Rcal k) (‖Nsim k s‖ ^ 2 / (4 * eta)) s)
    (hrembound : ∀ k, Rcal k (-Real.log (1 / M k))
      - Rcal k (-Real.log (cascadeStart (M k))) ≤ Cabs)
    (hdrop : ∀ k,
      ((1 / 2) * bil (Vsim k (-Real.log (cascadeStart (M k))))
          (Vsim k (-Real.log (cascadeStart (M k))))
        + (1 / 4) * ⟪Vsim k (-Real.log (cascadeStart (M k))),
            Vsim k (-Real.log (cascadeStart (M k)))⟫)
      - ((1 / 2) * bil (Vsim k (-Real.log (1 / M k))) (Vsim k (-Real.log (1 / M k)))
        + (1 / 4) * ⟪Vsim k (-Real.log (1 / M k)), Vsim k (-Real.log (1 / M k))⟫)
      ≤ Cdrop)
    (hdom : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      Delta k r / QgradCyl (G k) (t k) (x k) r ≤ K * ‖Wsim k (-Real.log r)‖ ^ 2)
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  refine clay_A_dyn_of_similarity_absorption
    (Hcal := fun k s => (1 / 2) * bil (Vsim k s) (Vsim k s) + (1 / 4) * ⟪Vsim k s, Vsim k s⟫)
    (Ecal := Ecal) (Rcal := Rcal)
    (Hd := fun k s => -⟪Wsim k s, Wsim k s⟫ - ⟪Nsim k s, Wsim k s⟫)
    (q := fun k s => ‖Wsim k s‖ ^ 2)
    (rem := fun k s => ‖Nsim k s‖ ^ 2 / (4 * eta))
    (Cdrop := Cdrop) (Cabs := Cabs)
    heps hM hcinv hK heta1 hle hpos hderiv hexact hsplit hPhi hPsi hTheta
    ?_ ?_ hEc hRc hrembound hdrop hdom hrem hstart
  · intro k s _
    exact similarity_energy_identity bil hsymm (hV k s) (heq k s)
  · intro k s _
    exact similarity_energy_deriv_le (Nsim k s) (Wsim k s) heta0

end ClayNS
