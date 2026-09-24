/-
# The signed Gram flux on the literal Galerkin trajectory

`SignedGramWienerAssembly.sum_gram_debt_le_wiener` is the assembled consumer of
the resolvent/flux route, but it is stated for an *abstract* time-dependent
Fourier field `u` and an *abstract* cell family `A`, and it carries a long list
of hypotheses which the caller has to supply: the kinematic constraints, the
damped tangent `dA_α = −λ_α A_α + F_α` of the cells, and five interval
integrability assumptions.

This file discharges every one of those hypotheses on the *actual* trajectory
produced in `GalerkinExistence.lean`.  Concretely:

* `exists_damped_forced` — the ordinary Duhamel theorem.  For a real rate `λ`
  and a continuous complex forcing `f`, the function
  `A(t) = e^{−λ t} ∫₀^t e^{λ s} f(s) ds` is differentiable everywhere and obeys
  `A' = −λ A + f`.  This is the piece of genuine real analysis: it is the
  fundamental theorem of calculus for a continuous integrand, and it is what
  turns the formal algebraic tangent of the cell family into an actual time
  derivative.

* the continuity lemmas — every object built polynomially from the Fourier
  coefficients of a Galerkin flow (the raw slot kernel, the Leray projection,
  the inner forcing, the outer cells) is continuous in time, because the
  coefficients are.

* `exists_outCell_family` — hence at every output frequency there is a genuine
  cell family solving the literal damped tangent whose forcing is the literal
  outer cell family of the trajectory.

* `galerkin_signed_gram_bound` — the assembled conclusion, with *no* remaining
  analytic hypothesis: on any compact time window the signed integrated Gram
  debt of that family is bounded by the initial resolvent energy, an
  arbitrarily small multiple of the integrated resolvent energy, and an
  explicit multiple of the Wiener–energy budget `M` of the trajectory on the
  window.  `M` exists here because a *fixed* truncation has a continuous,
  hence bounded, Wiener–energy product on a compact interval.

**What this does not close.**  The bound produced here is not uniform in the
Galerkin truncation: the constant `M` is obtained from compactness on the fixed
mode set, and `WaleffeWienerSupercritical.wiener_norm_not_controlled_by_energy`
shows that no energy-based bound for it can be uniform.  That supercritical
input is exactly the surviving wall.  No Package-A or Clay-level claim is made.
-/
import RequestProject.NavierStokes.GalerkinExistence
import RequestProject.NavierStokes.SignedGramWienerAssembly

noncomputable section

open MeasureTheory Set intervalIntegral

namespace ClayNS.GalerkinFlux

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar

/-! ## The Duhamel solution of a damped–forced scalar equation -/

/-- **The linear damped–forced equation has a global solution.**  For a real
decay rate `λ` and a continuous complex forcing `f`, the Duhamel formula
`A(t) = e^{−λt}∫₀^t e^{λs}f(s)ds` produces an everywhere-differentiable `A` with
`A' = −λ A + f`.  This is the fundamental theorem of calculus for a continuous
integrand; it is the analytic content behind the cell tangent. -/
theorem exists_damped_forced (lam : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    ∃ A : ℝ → ℂ, A 0 = 0 ∧ Continuous A ∧
      ∀ t, HasDerivAt A (-(lam : ℂ) * A t + f t) t := by
  have hcont : Continuous fun s : ℝ => ((Real.exp (lam * s) : ℝ) : ℂ) * f s := by fun_prop
  set g : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, ((Real.exp (lam * s) : ℝ) : ℂ) * f s with hg
  have hgd : ∀ t, HasDerivAt g (((Real.exp (lam * t) : ℝ) : ℂ) * f t) t := fun t =>
    (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hgdiff : Differentiable ℝ g := fun t => (hgd t).differentiableAt
  have hed : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Real.exp (-(lam * t)) : ℝ) : ℂ))
      (((-lam * Real.exp (-(lam * t)) : ℝ) : ℂ)) t := by
    intro t
    have h : HasDerivAt (fun t : ℝ => Real.exp (-(lam * t))) (-lam * Real.exp (-(lam * t))) t := by
      have := (((hasDerivAt_id t).const_mul lam).neg).exp
      simpa [mul_comm] using this
    exact h.ofReal_comp
  refine ⟨fun t => ((Real.exp (-(lam * t)) : ℝ) : ℂ) * g t, by simp [hg], ?_, ?_⟩
  · exact (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-(lam * t)) : ℝ) : ℂ)).mul
      hgdiff.continuous
  · intro t
    have h := (hed t).mul (hgd t)
    convert h using 1
    have hE : Complex.exp (-((lam : ℂ) * (t : ℂ))) * Complex.exp ((lam : ℂ) * (t : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    push_cast
    linear_combination (-(f t)) * hE

/-! ## Continuity of the literal cell objects along a Galerkin flow -/

theorem continuous_leray_of {v : ℝ → Fin 3 → ℂ} (hv : ∀ i, Continuous fun t => v t i)
    (k : Wave) (i : Fin 3) : Continuous fun t => leray k (v t) i := by
  show Continuous fun t =>
    v t i - (herm (wC k) (v t) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ)
  refine (hv i).sub (Continuous.mul ?_ continuous_const)
  exact (continuous_herm_of (f := fun _ => wC k) (fun _ => continuous_const) hv).div_const _

theorem continuous_rawKernel_of {u v : ℝ → Fin 3 → ℂ}
    (hu : ∀ i, Continuous fun t => u t i) (hv : ∀ i, Continuous fun t => v t i)
    (a b : Wave) (i : Fin 3) :
    Continuous fun t => rawKernel a b (u t) (v t) i := by
  show Continuous fun t =>
    cross (cross (wC a) (u t)) (v t) i - cross (u t) (cross (wC b) (v t)) i
  refine Continuous.sub ?_ ?_
  · exact continuous_cross_of
      (fun j => continuous_cross_of (f := fun _ => wC a) (fun _ => continuous_const) hu j) hv i
  · exact continuous_cross_of hu
      (fun j => continuous_cross_of (f := fun _ => wC b) (fun _ => continuous_const) hv j) i

theorem continuous_innerForcing (G : GalerkinFlow) (p : Wave) (i : Fin 3) :
    Continuous fun t => innerForcing G.modes (G.u t) p i := by
  show Continuous fun t => ∑ a ∈ G.modes, innerCell (G.u t) p a i
  refine continuous_finset_sum _ fun a _ => ?_
  show Continuous fun t => leray p (rawKernel a (p - a) (G.u t a) (G.u t (p - a))) i
  exact continuous_leray_of
    (fun j => continuous_rawKernel_of (G.continuous_u a) (G.continuous_u (p - a)) a (p - a) j) p i

theorem continuous_outCells (G : GalerkinFlow) (k : Wave) (i : ↥G.modes) (c : Fin 3) :
    Continuous fun t =>
      outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k i c := by
  show Continuous fun t =>
    leray k (cross (innerForcing G.modes (G.u t) (i : Wave)) (G.u t (k - (i : Wave)))) c
  refine continuous_leray_of (fun j => ?_) k c
  exact continuous_cross_of (fun m => continuous_innerForcing G (i : Wave) m)
    (G.continuous_u (k - (i : Wave))) j

/-! ## Continuity of the quadratic observables of a cell family -/

theorem continuous_form_of {X Y : ℝ → Fin 3 → ℂ}
    (hX : ∀ i, Continuous fun t => X t i) (hY : ∀ i, Continuous fun t => Y t i) :
    Continuous fun t => nsPSD.form (X t) (Y t) :=
  Complex.continuous_re.comp (continuous_herm_of hX hY)

theorem continuous_gramRemainder_of {ι : Type*} {X Y : ℝ → ι → Fin 3 → ℂ}
    (hX : ∀ i c, Continuous fun t => X t i c) (hY : ∀ i c, Continuous fun t => Y t i c)
    (i j : ι) : Continuous fun t => nsPSD.gramRemainder (X t) (Y t) i j := by
  show Continuous fun t =>
    2 * nsPSD.form (Y t i) (X t j) + 2 * nsPSD.form (X t i) (Y t j)
  exact (continuous_const.mul (continuous_form_of (hY i) (hX j))).add
    (continuous_const.mul (continuous_form_of (hX i) (hY j)))

theorem continuous_resForm_of {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    {X Y : ℝ → ι → Fin 3 → ℂ}
    (hX : ∀ i c, Continuous fun t => X t i c) (hY : ∀ i c, Continuous fun t => Y t i c) :
    Continuous fun t => nsPSD.resForm lam (X t) (Y t) := by
  show Continuous fun t => ∑ i, ∑ j, nsPSD.form (X t i) (Y t j) / (lam i + lam j)
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_form_of (hX i) (hY j)).div_const _

/-! ## The cell family on the literal trajectory -/

/-- **The cell family exists on the actual trajectory.**  At every output
frequency there is a family of two-leg cells, continuous in time, obeying the
literal damped tangent whose forcing is the literal outer cell family of the
Galerkin flow.  Nothing is assumed: the family is produced by Duhamel from the
(continuous) outer cells. -/
theorem exists_outCell_family (G : GalerkinFlow) (k : Wave) :
    ∃ A : ℝ → ↥G.modes → Fin 3 → ℂ,
      (∀ (i : ↥G.modes) (c : Fin 3), Continuous fun t => A t i c) ∧
      (∀ (t : ℝ) (i : ↥G.modes) (c : Fin 3), HasDerivAt (fun t => A t i c)
        (-((outRate G.nu G.modes k i : ℝ) : ℂ) * A t i c
          + outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k i c) t) := by
  choose a _ hacont haderiv using fun (i : ↥G.modes) (c : Fin 3) =>
    exists_damped_forced (outRate G.nu G.modes k i) (continuous_outCells G k i c)
  exact ⟨fun t i c => a i c t, fun i c => hacont i c, fun t i c => haderiv i c t⟩

/-! ## The exact temporal flux identity on the literal trajectory -/

/-- **The signed Gram flux identity, unconditionally, on the actual
trajectory.**  At every output frequency of a Galerkin flow there is a genuine
cell family for which the *signed* integrated Gram debt equals the endpoint
difference of the resolvent energies plus the integrated resolvent pairing with
the literal outer cells:

  `∫ D_Gram = 2·resForm(A(t₀)) − 2·resForm(A(t₁)) + 4·∫ resForm(A, F)`.

This is the fundamental theorem of calculus applied to the literal flux
observable of the trajectory: no integrability, differentiability or
same-object hypothesis is left for the caller — the tangent comes from Duhamel
and the integrability from continuity. -/
theorem galerkin_gram_flux_identity (G : GalerkinFlow) (hnu : 0 < G.nu)
    (hp : ∀ p ∈ G.modes, wsq p ≠ 0) (k : Wave) (t₀ t₁ : ℝ) :
    ∃ A : ℝ → ↥G.modes → Fin 3 → ℂ,
      (∀ (t : ℝ) (i : ↥G.modes) (c : Fin 3), HasDerivAt (fun s => A s i c)
        (-((outRate G.nu G.modes k i : ℝ) : ℂ) * A t i c
          + outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k i c) t) ∧
      ∫ t in t₀..t₁, nsPSD.gramDebt (A t)
        = 2 * nsPSD.resForm (outRate G.nu G.modes k) (A t₀) (A t₀)
          - 2 * nsPSD.resForm (outRate G.nu G.modes k) (A t₁) (A t₁)
          + 4 * ∫ t in t₀..t₁, nsPSD.resForm (outRate G.nu G.modes k) (A t)
              (outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k) := by
  obtain ⟨A, hAcont, hAderiv⟩ := exists_outCell_family G k
  refine ⟨A, hAderiv, ?_⟩
  set F : ℝ → ↥G.modes → Fin 3 → ℂ :=
    fun t => outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k with hF
  have hFcont : ∀ (i : ↥G.modes) (c : Fin 3), Continuous fun t => F t i c :=
    fun i c => continuous_outCells G k i c
  refine nsPSD.integral_gramDebt_eq (outRate G.nu G.modes k) (outRate_pos hnu hp) A F t₀ t₁
    (fun i j t _ => nsPSD_gram_hasDerivAt _ A F i j t (fun m c => hAderiv t m c)) ?_
  intro i j
  exact (continuous_gramRemainder_of hAcont hFcont i j).intervalIntegrable _ _

/-! ## The assembled bound, with every analytic hypothesis discharged -/

/-- **The signed Gram flux bound on the literal Galerkin trajectory.**  For a
Galerkin flow with positive viscosity on a mode set avoiding the zero mode and
any finite set of output frequencies, there is an actual cell family — obeying
the literal damped tangent forced by the literal outer cells — and an actual
Wiener–energy budget `M` on the window, for which the signed integrated Gram
debt satisfies the assembled resolvent bound.

All of the analytic hypotheses of `sum_gram_debt_le_wiener` (the kinematic
constraints, the cell tangent, and the five interval-integrability conditions)
are discharged here from the trajectory itself: they are consequences of the
Galerkin ODE and continuity.

The constant `M` comes from compactness of the window on the *fixed* mode set
and is therefore not uniform in the truncation; that non-uniformity is the
surviving obstruction, not something this statement hides. -/
theorem galerkin_signed_gram_bound (G : GalerkinFlow) (hnu : 0 < G.nu)
    (hp : ∀ p ∈ G.modes, wsq p ≠ 0) (outs : Finset Wave) (hk : ∀ k ∈ outs, wsq k ≠ 0)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : Wave → ℝ → ↥G.modes → Fin 3 → ℂ) (M : ℝ),
      (∀ t ∈ Icc t₀ t₁, wienerA G.modes (G.u t) ^ 4 * energy G.modes (G.u t) ≤ M) ∧
      (∀ (k : Wave) (t : ℝ) (i : ↥G.modes) (c : Fin 3), HasDerivAt (fun s => A k s i c)
        (-((outRate G.nu G.modes k i : ℝ) : ℂ) * A k t i c
          + outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k i c) t) ∧
      ∑ k ∈ outs, ∫ t in t₀..t₁, nsPSD.gramDebt (A k t)
        ≤ (∑ k ∈ outs, 2 * nsPSD.resForm (outRate G.nu G.modes k) (A k t₀) (A k t₀))
          + ε * (∑ k ∈ outs, ∫ t in t₀..t₁,
              nsPSD.resForm (outRate G.nu G.modes k) (A k t) (A k t))
          + (4 / ε) * (9 * M * (t₁ - t₀) / (2 * G.nu)) := by
  classical
  choose A hAcont hAderiv using fun k : Wave => exists_outCell_family G k
  -- the Wiener–energy product is continuous, hence bounded on the compact window
  have hWcont : Continuous fun t => wienerA G.modes (G.u t) ^ 4 * energy G.modes (G.u t) := by
    have h1 : Continuous fun t => wienerA G.modes (G.u t) :=
      continuous_finset_sum _ fun a _ => G.continuous_nrm_u a
    have h2 : Continuous fun t => energy G.modes (G.u t) :=
      continuous_finset_sum _ fun a _ =>
        continuous_finset_sum _ fun c _ => Complex.continuous_normSq.comp (G.continuous_u a c)
    exact (h1.pow 4).mul h2
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun t =>
    wienerA G.modes (G.u t) ^ 4 * energy G.modes (G.u t)) hWcont.continuousOn
  have hMle : ∀ t ∈ Icc t₀ t₁,
      wienerA G.modes (G.u t) ^ 4 * energy G.modes (G.u t) ≤ M :=
    fun t htm => le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM t htm)
  refine ⟨A, M, hMle, hAderiv, ?_⟩
  -- the forcing family and its continuity
  set F : Wave → ℝ → ↥G.modes → Fin 3 → ℂ :=
    fun k t => outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k with hF
  have hFcont : ∀ (k : Wave) (i : ↥G.modes) (c : Fin 3), Continuous fun t => F k t i c :=
    fun k i c => continuous_outCells G k i c
  refine sum_gram_debt_le_wiener hnu G.modes outs G.u A t₀ t₁ M ht hε hk hp ?_ ?_ hMle
    (fun k _ t _ i c => hAderiv k t i c) ?_ ?_ ?_ ?_
  · intro t c
    have h : herm (wC c) (G.u t c) = 0 := G.transverse t c
    simpa [dotb, herm, wC, map_intCast] using h
  · intro t b hb
    exact G.support t b hb
  · intro k _ i j
    exact ((continuous_gramRemainder_of (hAcont k) (hFcont k) i j)).intervalIntegrable _ _
  · intro k _
    exact (continuous_resForm_of _ (hAcont k) (hFcont k)).intervalIntegrable _ _
  · intro k _
    exact (continuous_resForm_of _ (hAcont k) (hAcont k)).intervalIntegrable _ _
  · intro k _
    exact (continuous_resForm_of _ (hFcont k) (hFcont k)).intervalIntegrable _ _

/-! ## End to end, from the initial datum -/

open ClayNS.GalerkinODE in
/-- **From an admissible datum straight to the exact flux identity.**  For any
finite symmetric mode set avoiding the zero mode, any positive viscosity and any
transverse real datum, there is an actual Galerkin flow realising the datum,
and on it, at every output frequency, a genuine cell family for which the exact
signed Gram flux identity holds.  Both the trajectory and the temporal identity
are constructed: neither is assumed. -/
theorem exists_flow_with_flux_identity {modes : Finset Wave}
    (hzero : (0 : Wave) ∉ modes) (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hp : ∀ p ∈ modes, wsq p ≠ 0) {nu : ℝ} (hnu : 0 < nu) (v₀ : State modes)
    (htr0 : ∀ k : Wave, herm (wC k) (spread modes v₀ k) = 0)
    (hre0 : reflSt hsym v₀ = v₀) :
    ∃ G : GalerkinFlow, G.nu = nu ∧ G.modes = modes ∧ G.u 0 = spread modes v₀ ∧
      ∀ (k : Wave) (t₀ t₁ : ℝ), ∃ A : ℝ → ↥G.modes → Fin 3 → ℂ,
        (∀ (t : ℝ) (i : ↥G.modes) (c : Fin 3), HasDerivAt (fun s => A s i c)
          (-((outRate G.nu G.modes k i : ℝ) : ℂ) * A t i c
            + outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k i c) t) ∧
        ∫ t in t₀..t₁, nsPSD.gramDebt (A t)
          = 2 * nsPSD.resForm (outRate G.nu G.modes k) (A t₀) (A t₀)
            - 2 * nsPSD.resForm (outRate G.nu G.modes k) (A t₁) (A t₁)
            + 4 * ∫ t in t₀..t₁, nsPSD.resForm (outRate G.nu G.modes k) (A t)
                (outCells (innerForcing G.modes (G.u t)) (G.u t) G.modes k) := by
  obtain ⟨G, hnuG, hmodes, hu0⟩ :=
    exists_galerkinFlow hzero hsym hnu.le v₀ htr0 hre0
  refine ⟨G, hnuG, hmodes, hu0, fun k t₀ t₁ => ?_⟩
  refine galerkin_gram_flux_identity G (by rw [hnuG]; exact hnu) ?_ k t₀ t₁
  intro p hpm
  exact hp p (by rwa [hmodes] at hpm)

end ClayNS.GalerkinFlux
