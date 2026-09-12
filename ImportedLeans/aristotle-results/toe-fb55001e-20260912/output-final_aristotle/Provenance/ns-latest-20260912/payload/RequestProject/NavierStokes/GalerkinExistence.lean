/-
# Existence of the physical Galerkin trajectory

This file removes the cutoff of `GalerkinTruncatedField.lean` and constructs a
genuine `ClayNS.Waleffe.GalerkinFlow`: for *any* admissible initial datum — a
finite symmetric mode set avoiding the zero mode, a transverse and real Fourier
state, and any nonnegative viscosity — there is a trajectory defined for all
time which is differentiable, supported on the retained modes, transverse, real,
and which solves the literal truncated Navier–Stokes system

  `u̇_k = −ν|k|² u_k − P_k((u·∇)u)^_k`.

The mechanism is the a-priori energy estimate: along the cut-off flow the energy
obeys `d/dt E = −2 φ ν 𝔇 ≤ 0` (energy neutrality of the projected nonlinearity,
available because transversality and reality propagate) and
`𝔇 ≤ (∑_k |k|²) E`, so `E` can never leave the region where the cutoff is
inactive.  Since the bound is uniform on every bounded time window, the local
solutions patch to a solution on all of `ℝ`: the finite Galerkin system has no
blow-up, forwards or backwards.
-/
import RequestProject.NavierStokes.GalerkinInvariants

noncomputable section

open Set

namespace ClayNS.GalerkinODE

open ClayNS.Waleffe

variable {modes : Finset Wave}

/-! ## The dissipation of a state -/

/-- The Galerkin dissipation (enstrophy) of a state. -/
def dissip (modes : Finset Wave) (v : State modes) : ℝ :=
  ∑ k ∈ modes, wsq k * nsq (spread modes v k)

/-- The total squared frequency of the retained mode set; it is the constant in
the elementary inequality `𝔇 ≤ C E` available on a finite truncation. -/
def wsqSum (modes : Finset Wave) : ℝ := ∑ k ∈ modes, wsq k

theorem dissip_nonneg (v : State modes) : 0 ≤ dissip modes v :=
  Finset.sum_nonneg fun k _ => mul_nonneg (wsq_nonneg k) (nsq_nonneg _)

theorem wsqSum_nonneg (modes : Finset Wave) : 0 ≤ wsqSum modes :=
  Finset.sum_nonneg fun k _ => wsq_nonneg k

/-- On a finite truncation the dissipation is controlled by the energy. -/
theorem dissip_le_wsqSum_mul_en (v : State modes) :
    dissip modes v ≤ wsqSum modes * en modes v := by
  have hle : ∀ k ∈ modes, wsq k * nsq (spread modes v k)
      ≤ wsqSum modes * nsq (spread modes v k) := by
    intro k hk
    refine mul_le_mul_of_nonneg_right ?_ (nsq_nonneg _)
    exact Finset.single_le_sum (f := fun m => wsq m) (fun m _ => wsq_nonneg m) hk
  calc dissip modes v ≤ ∑ k ∈ modes, wsqSum modes * nsq (spread modes v k) :=
        Finset.sum_le_sum hle
    _ = wsqSum modes * en modes v := by
        rw [← Finset.mul_sum, en_spread]

/-! ## The energy along a solution of the cut-off equation -/

/-- **The energy identity along the cut-off flow.**  The nonlinear term is
energy neutral (it is transverse and real along the flow, by the invariants), so
only the viscous term survives, damped by the cutoff factor. -/
theorem en_hasDerivAt_of_solution {nu R a b : ℝ} {α : ℝ → State modes}
    (hsym : ∀ k ∈ modes, -k ∈ modes)
    (hsol : ∀ t ∈ Ioo a b, HasDerivAt α (tvfield modes nu R (α t)) t)
    (htr : ∀ t ∈ Ioo a b, ∀ k : Wave, herm (wC k) (spread modes (α t) k) = 0)
    (hre : ∀ t ∈ Ioo a b, reflSt hsym (α t) = α t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => en modes (α s))
      (-2 * cut modes R (α t) * nu * dissip modes (α t)) t := by
  classical
  set u : Wave → Fin 3 → ℂ := spread modes (α t) with hu
  -- the derivative of each modal square
  have hterm : ∀ k ∈ (Finset.univ : Finset ↥modes),
      HasDerivAt (fun s => nsq (α s k))
        (2 * (herm (α t k) (tvfield modes nu R (α t) k)).re) t := by
    intro k _
    exact nsq_hasDerivAt (fun s => α s k) (tvfield modes nu R (α t) k) t
      (fun i => hasDerivAt_coord (hsol t ht) k i)
  have hsum : HasDerivAt (fun s => en modes (α s))
      (∑ k : ↥modes, 2 * (herm (α t k) (tvfield modes nu R (α t) k)).re) t := by
    have h := HasDerivAt.sum hterm
    have hfun : (∑ k : ↥modes, fun s => nsq (α s k)) = fun s => en modes (α s) := by
      funext s
      simp [en, Finset.sum_apply]
    rwa [hfun] at h
  -- evaluate the sum
  have hval : (∑ k : ↥modes, 2 * (herm (α t k) (tvfield modes nu R (α t) k)).re)
      = -2 * cut modes R (α t) * nu * dissip modes (α t) := by
    have hentry : ∀ k : ↥modes, 2 * (herm (α t k) (tvfield modes nu R (α t) k)).re
        = cut modes R (α t) * (-2 * nu * (wsq (k : Wave) * nsq (spread modes (α t) (k : Wave)))
            + 2 * (herm (spread modes (α t) (k : Wave))
                (modalForcing modes u (k : Wave))).re) := by
      intro k
      have hcoe : α t k = spread modes (α t) (k : Wave) := (spread_coe (α t) k).symm
      have hfield : tvfield modes nu R (α t) k
          = fun i => ((cut modes R (α t) : ℝ) : ℂ) *
              (-((nu * wsq (k : Wave) : ℝ) : ℂ) * spread modes (α t) (k : Wave) i
                + modalForcing modes u (k : Wave) i) := by
        funext i
        simp [tvfield, vfield_apply, Complex.real_smul, hu]
        ring
      rw [hcoe, hfield]
      have hherm : herm (spread modes (α t) (k : Wave))
          (fun i => ((cut modes R (α t) : ℝ) : ℂ) *
            (-((nu * wsq (k : Wave) : ℝ) : ℂ) * spread modes (α t) (k : Wave) i
              + modalForcing modes u (k : Wave) i))
          = ((cut modes R (α t) : ℝ) : ℂ) *
              (-((nu * wsq (k : Wave) : ℝ) : ℂ)
                  * ((nsq (spread modes (α t) (k : Wave)) : ℝ) : ℂ)
                + herm (spread modes (α t) (k : Wave)) (modalForcing modes u (k : Wave))) := by
        rw [herm_smul_right, herm_add_right, herm_smul_right, herm_self]
      rw [hherm]
      simp [Complex.add_re, Complex.mul_re]
      ring
    rw [Finset.sum_congr rfl fun k _ => hentry k, ← Finset.mul_sum]
    have hsplit : (∑ k : ↥modes, (-2 * nu * (wsq (k : Wave) * nsq (spread modes (α t) (k : Wave)))
          + 2 * (herm (spread modes (α t) (k : Wave)) (modalForcing modes u (k : Wave))).re))
        = -2 * nu * dissip modes (α t)
          + 2 * (∑ k ∈ modes, herm (u k) (modalForcing modes u k)).re := by
      rw [Finset.sum_add_distrib]
      have h1 : (∑ k : ↥modes, -2 * nu * (wsq (k : Wave) * nsq (spread modes (α t) (k : Wave))))
          = -2 * nu * dissip modes (α t) := by
        rw [Finset.sum_coe_sort modes
          (fun k => -2 * nu * (wsq k * nsq (spread modes (α t) k))), dissip, Finset.mul_sum]
      have h2 : (∑ k : ↥modes, 2 * (herm (spread modes (α t) (k : Wave))
            (modalForcing modes u (k : Wave))).re)
          = 2 * (∑ k ∈ modes, herm (u k) (modalForcing modes u k)).re := by
        rw [Finset.sum_coe_sort modes
          (fun k => 2 * (herm (u k) (modalForcing modes u k)).re), Complex.re_sum, Finset.mul_sum]
      rw [h1, h2]
    rw [hsplit]
    have hneutral : (∑ k ∈ modes, herm (u k) (modalForcing modes u k)).re = 0 := by
      refine force_energy_neutral_of ?_ (htr t ht) ?_
      · intro k hk
        funext i
        simp [hu, spread_of_not_mem _ hk]
      · intro k i
        exact reality_spread hsym (hre t ht) k i
    rw [hneutral, mul_zero, add_zero]
    ring
  rwa [hval] at hsum

/-! ## The a-priori energy bound -/

section EnergyBound

variable {nu R a b : ℝ} {α : ℝ → State modes}

/-- The derivative of the energy along the cut-off flow is nonpositive, and it
is bounded below by `−2ν(∑|k|²)E`: the finite truncation cannot lose or gain
energy faster than exponentially. -/
theorem en_deriv_bounds {nu R : ℝ} (hnu : 0 ≤ nu) (v : State modes) :
    -(2 * nu * wsqSum modes * en modes v) ≤ -2 * cut modes R v * nu * dissip modes v ∧
      -2 * cut modes R v * nu * dissip modes v ≤ 0 := by
  have hcut0 : 0 ≤ cut modes R v := cut_nonneg R v
  have hcut1 : cut modes R v ≤ 1 := cut_le_one R v
  have hdis : 0 ≤ dissip modes v := dissip_nonneg v
  have hdisle : dissip modes v ≤ wsqSum modes * en modes v := dissip_le_wsqSum_mul_en v
  have hs1 : cut modes R v * (nu * dissip modes v) ≤ nu * dissip modes v := by
    nlinarith [mul_nonneg hnu hdis]
  have hs2 : nu * dissip modes v ≤ nu * (wsqSum modes * en modes v) :=
    mul_le_mul_of_nonneg_left hdisle hnu
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hnu hdis]

/-- **No blow-up on the finite truncation.**  Along any solution of the cut-off
equation whose kinematic constraints hold, the energy is bounded on every
bounded time window, with a bound depending only on the initial energy, the
viscosity and the retained frequencies — never on the solution itself. -/
theorem en_le_exp_of_solution (hsym : ∀ k ∈ modes, -k ∈ modes) (hnu : 0 ≤ nu)
    (hsol : ∀ t ∈ Ioo a b, HasDerivAt α (tvfield modes nu R (α t)) t)
    (htr : ∀ t ∈ Ioo a b, ∀ k : Wave, herm (wC k) (spread modes (α t) k) = 0)
    (hre : ∀ t ∈ Ioo a b, reflSt hsym (α t) = α t)
    (h0mem : (0 : ℝ) ∈ Ioo a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    en modes (α t) ≤ en modes (α 0) * Real.exp (2 * nu * wsqSum modes * |t|) := by
  set c : ℝ := 2 * nu * wsqSum modes with hc
  have hc0 : 0 ≤ c := by
    have := wsqSum_nonneg modes
    positivity
  have hE : ∀ s ∈ Ioo a b, HasDerivAt (fun r => en modes (α r))
      (-2 * cut modes R (α s) * nu * dissip modes (α s)) s :=
    fun s hs => en_hasDerivAt_of_solution hsym hsol htr hre hs
  rcases le_or_gt 0 t with htpos | htneg
  · have hsub : Icc (0 : ℝ) t ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le h0mem.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
        HasDerivAt (fun r => en modes (α r) * Real.exp (-(c * r)))
          ((-2 * cut modes R (α s) * nu * dissip modes (α s) - c * en modes (α s))
            * Real.exp (-(c * s))) s := by
      intro s hs
      have hs' : s ∈ Ioo a b := hsub (Ioo_subset_Icc_self hs)
      have h1 := hE s hs'
      have h2 : HasDerivAt (fun r : ℝ => Real.exp (-(c * r)))
          (-c * Real.exp (-(c * s))) s := by
        have := (((hasDerivAt_id s).const_mul c).neg).exp
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
      have h3 := h1.mul h2
      convert h3 using 1
      ring
    have hanti : AntitoneOn (fun r => en modes (α r) * Real.exp (-(c * r))) (Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
      · refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (by fun_prop)).continuousOn
        exact fun s hs => ((hE s (hsub hs)).continuousAt).continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hderiv s hs).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hderiv s hs).deriv]
        have hs' : s ∈ Ioo a b := hsub (Ioo_subset_Icc_self hs)
        obtain ⟨-, hD⟩ := en_deriv_bounds (R := R) hnu (α s)
        have hen : 0 ≤ en modes (α s) := en_nonneg (α s)
        have hexp : 0 < Real.exp (-(c * s)) := Real.exp_pos _
        have hneg : (-2 * cut modes R (α s) * nu * dissip modes (α s) - c * en modes (α s))
            ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg hneg hexp.le
    have hle := hanti (left_mem_Icc.2 htpos) (right_mem_Icc.2 htpos) htpos
    dsimp only at hle
    have hexp : 0 < Real.exp (-(c * t)) := Real.exp_pos _
    have h0 : en modes (α 0) * Real.exp (-(c * 0)) = en modes (α 0) := by simp
    rw [h0] at hle
    have hbound : en modes (α t) ≤ en modes (α 0) * Real.exp (c * t) := by
      calc en modes (α t) = en modes (α t) * Real.exp (-(c * t)) / Real.exp (-(c * t)) := by
            field_simp
        _ ≤ en modes (α 0) / Real.exp (-(c * t)) := by
            gcongr
        _ = en modes (α 0) * Real.exp (c * t) := by
            rw [Real.exp_neg]
            field_simp
    rwa [abs_of_nonneg htpos]
  · have htle : t ≤ 0 := le_of_lt htneg
    have hsub : Icc t (0 : ℝ) ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 h0mem.2⟩
    have hderiv : ∀ s ∈ Ioo t (0 : ℝ),
        HasDerivAt (fun r => en modes (α r) * Real.exp (c * r))
          ((-2 * cut modes R (α s) * nu * dissip modes (α s) + c * en modes (α s))
            * Real.exp (c * s)) s := by
      intro s hs
      have hs' : s ∈ Ioo a b := hsub (Ioo_subset_Icc_self hs)
      have h1 := hE s hs'
      have h2 : HasDerivAt (fun r : ℝ => Real.exp (c * r)) (c * Real.exp (c * s)) s := by
        have := ((hasDerivAt_id s).const_mul c).exp
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
      have h3 := h1.mul h2
      convert h3 using 1
      ring
    have hmono : MonotoneOn (fun r => en modes (α r) * Real.exp (c * r)) (Icc t 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t 0) ?_ ?_ ?_
      · refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (by fun_prop)).continuousOn
        exact fun s hs => ((hE s (hsub hs)).continuousAt).continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hderiv s hs).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hderiv s hs).deriv]
        have hs' : s ∈ Ioo a b := hsub (Ioo_subset_Icc_self hs)
        obtain ⟨hD, -⟩ := en_deriv_bounds (R := R) hnu (α s)
        have hexp : 0 < Real.exp (c * s) := Real.exp_pos _
        have hpos : 0 ≤ (-2 * cut modes R (α s) * nu * dissip modes (α s)
            + c * en modes (α s)) := by nlinarith
        exact mul_nonneg hpos hexp.le
    have hle := hmono (left_mem_Icc.2 htle) (right_mem_Icc.2 htle) htle
    dsimp only at hle
    have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
    have h0 : en modes (α 0) * Real.exp (c * 0) = en modes (α 0) := by simp
    rw [h0] at hle
    have hbound : en modes (α t) ≤ en modes (α 0) * Real.exp (-(c * t)) := by
      calc en modes (α t) = en modes (α t) * Real.exp (c * t) / Real.exp (c * t) := by
            field_simp
        _ ≤ en modes (α 0) / Real.exp (c * t) := by gcongr
        _ = en modes (α 0) * Real.exp (-(c * t)) := by
            rw [Real.exp_neg]
            field_simp
    rw [abs_of_neg htneg]
    calc en modes (α t) ≤ en modes (α 0) * Real.exp (-(c * t)) := hbound
      _ = en modes (α 0) * Real.exp (c * -t) := by ring_nf

end EnergyBound

/-! ## Global existence: removing the cutoff -/

section Global

/-- **The literal finite Galerkin system has a global solution.**  For any
finite symmetric mode set avoiding the zero mode, any nonnegative viscosity and
any transverse real initial state, there is a trajectory defined for *all* real
times which is differentiable everywhere and satisfies the literal truncated
Navier–Stokes equation `u̇ = −ν|k|²u + f(u)` (no cutoff), keeping
transversality and reality for all time.

The cutoff is removed by the a-priori energy bound: on the window `|t| < n+1`
the energy of the cut-off flow never exceeds `E₀ exp(2ν(∑|k|²)(n+1))`, which is
exactly the level at which the cutoff of that window is inactive. -/
theorem exists_global_solution (hzero : (0 : Wave) ∉ modes)
    (hsym : ∀ k ∈ modes, -k ∈ modes) {nu : ℝ} (hnu : 0 ≤ nu) (v₀ : State modes)
    (htr0 : ∀ k : Wave, herm (wC k) (spread modes v₀ k) = 0)
    (hre0 : reflSt hsym v₀ = v₀) :
    ∃ sol : ℝ → State modes, sol 0 = v₀ ∧
      (∀ t : ℝ, HasDerivAt sol (vfield modes nu (sol t)) t) ∧
      (∀ (t : ℝ) (k : Wave), herm (wC k) (spread modes (sol t) k) = 0) ∧
      (∀ t : ℝ, reflSt hsym (sol t) = sol t) := by
  classical
  set c : ℝ := 2 * nu * wsqSum modes with hc
  have hc0 : 0 ≤ c := by
    have := wsqSum_nonneg modes
    positivity
  set Rr : ℕ → ℝ := fun n => en modes v₀ * Real.exp (c * ((n : ℝ) + 1)) with hRr
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have h0mem : ∀ n : ℕ, (0 : ℝ) ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    intro n
    have := hnn n
    exact ⟨by linarith, by linarith⟩
  -- a cut-off solution on every window
  have hchoice : ∀ n : ℕ, ∃ α : ℝ → State modes, α 0 = v₀ ∧
      ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivAt α (tvfield modes nu (Rr n) (α t)) t := by
    intro n
    exact exists_solution_tvfield modes nu (Rr n) v₀
      (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1) (t₀ := 0)
      (Ioo_subset_Icc_self (h0mem n))
  choose α hα0 hαsol using hchoice
  -- the kinematic constraints propagate on each window
  have htr : ∀ (n : ℕ), ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      ∀ k : Wave, herm (wC k) (spread modes (α n t) k) = 0 := by
    intro n
    refine transverse_of_solution hzero (hαsol n) (h0mem n) ?_
    rw [hα0 n]; exact htr0
  have hre : ∀ (n : ℕ), ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      reflSt hsym (α n t) = α n t := by
    intro n
    refine reality_of_solution hsym (hαsol n) (h0mem n) ?_
    rw [hα0 n]; exact hre0
  -- the a-priori bound puts the trajectory inside the region where the cutoff is `1`
  have hen : ∀ (n : ℕ), ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      en modes (α n t) ≤ Rr n := by
    intro n t ht
    have hb := en_le_exp_of_solution hsym hnu (hαsol n) (htr n) (hre n) (h0mem n) ht
    rw [hα0 n] at hb
    refine hb.trans ?_
    have habs : |t| ≤ (n : ℝ) + 1 := by
      rw [abs_le]; exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have : Real.exp (c * |t|) ≤ Real.exp (c * ((n : ℝ) + 1)) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul_of_nonneg_left this (en_nonneg v₀)
  have hvf : ∀ (n : ℕ), ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivAt (α n) (vfield modes nu (α n t)) t := by
    intro n t ht
    have h := hαsol n t ht
    rwa [tvfield_eq_vfield (hen n t ht)] at h
  -- monotonicity of the cutoff levels
  have hRmono : ∀ m n : ℕ, m ≤ n → Rr m ≤ Rr n := by
    intro m n hmn
    have hcast : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (en_nonneg v₀)
    nlinarith
  -- the local solutions agree
  have hglue : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1),
      α m t = α n t := by
    intro m n hmn
    obtain ⟨K, hK⟩ := exists_lipschitzWith_tvfield modes nu (Rr n)
    have hsub : Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      have hcast : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hm : ∀ s ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1),
        HasDerivAt (α m) (tvfield modes nu (Rr n) (α m s)) s := by
      intro s hs
      rw [tvfield_eq_vfield ((hen m s hs).trans (hRmono m n hmn))]
      exact hvf m s hs
    have hn : ∀ s ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1),
        HasDerivAt (α n) (tvfield modes nu (Rr n) (α n s)) s :=
      fun s hs => hαsol n s (hsub hs)
    have heq : EqOn (α m) (α n) (Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1)) :=
      ODE_solution_unique_of_mem_Ioo (K := K) (v := fun _ v => tvfield modes nu (Rr n) v)
        (s := fun _ => univ) (fun s _ => hK.lipschitzOnWith) (h0mem m)
        (fun s hs => ⟨hm s hs, mem_univ _⟩) (fun s hs => ⟨hn s hs, mem_univ _⟩)
        (by rw [hα0 m, hα0 n])
    exact fun t ht => heq ht
  -- the glued global solution
  have hself : ∀ t : ℝ, t ∈ Ioo (-((⌊|t|⌋₊ : ℝ) + 1)) ((⌊|t|⌋₊ : ℝ) + 1) := by
    intro t
    have h1 := Nat.lt_floor_add_one |t|
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hlocal : ∀ (n : ℕ), ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      α ⌊|t|⌋₊ t = α n t := by
    intro n t ht
    have habs : |t| < (n : ℝ) + 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    have hfl : (⌊|t|⌋₊ : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    have hle : ⌊|t|⌋₊ ≤ n := by
      by_contra hcon
      push_neg at hcon
      have hcast : ((n : ℝ) + 1) ≤ (⌊|t|⌋₊ : ℝ) := by
        have hrw : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hrw]
        exact Nat.cast_le.2 hcon
      linarith
    exact hglue _ n hle t (hself t)
  refine ⟨fun t => α ⌊|t|⌋₊ t, by simpa using hα0 0, ?_, ?_, ?_⟩
  · intro t
    have hev : (fun s => α ⌊|s|⌋₊ s) =ᶠ[nhds t] α ⌊|t|⌋₊ := by
      filter_upwards [Ioo_mem_nhds (hself t).1 (hself t).2] with s hs
      exact hlocal ⌊|t|⌋₊ s hs
    have hd := (hvf ⌊|t|⌋₊ t (hself t)).congr_of_eventuallyEq hev
    simpa [hlocal ⌊|t|⌋₊ t (hself t)] using hd
  · intro t k
    exact htr _ t (hself t) k
  · intro t
    exact hre _ t (hself t)

/-- **The `GalerkinFlow` carrier is inhabited by a genuine trajectory.**  Every
admissible initial datum on a finite symmetric mode set avoiding the zero mode
is the initial value of an actual `ClayNS.Waleffe.GalerkinFlow`.

This discharges the standing assumption of the Waleffe/Galerkin lane: the
structure `GalerkinFlow` postulates a globally differentiable solution of the
truncated system, and the postulate is now a theorem. -/
theorem exists_galerkinFlow (hzero : (0 : Wave) ∉ modes)
    (hsym : ∀ k ∈ modes, -k ∈ modes) {nu : ℝ} (hnu : 0 ≤ nu) (v₀ : State modes)
    (htr0 : ∀ k : Wave, herm (wC k) (spread modes v₀ k) = 0)
    (hre0 : reflSt hsym v₀ = v₀) :
    ∃ G : GalerkinFlow, G.nu = nu ∧ G.modes = modes ∧ G.u 0 = spread modes v₀ := by
  obtain ⟨sol, hsol0, hsol, htr, hre⟩ := exists_global_solution hzero hsym hnu v₀ htr0 hre0
  refine ⟨{ nu := nu
            nu_nonneg := hnu
            modes := modes
            zero_not_mem := hzero
            u := fun t => spread modes (sol t)
            support := fun t k hk => spread_of_not_mem _ hk
            transverse := htr
            reality := fun t k i => reality_spread hsym (hre t) k i
            ode := ?_ }, rfl, rfl, by show spread modes (sol 0) = _; rw [hsol0]⟩
  intro t k hk i
  have h := hasDerivAt_coord (hsol t) ⟨k, hk⟩ i
  simpa [vfield_apply, spread_of_mem _ hk] using h

/-! ## Non-vacuity -/

/-- **The carrier is not vacuous.**  There is a Galerkin flow, with any
prescribed nonnegative viscosity, whose state is not identically zero: take the
symmetric pair of modes `±(1,0,0)` and the transverse real datum `(0,1,0)` on
both.  Without this the previous theorem could be satisfied by the zero field
alone. -/
theorem exists_nonzero_galerkinFlow {nu : ℝ} (hnu : 0 ≤ nu) :
    ∃ G : GalerkinFlow, G.nu = nu ∧ ∃ k : Wave, G.u 0 k ≠ fun _ => 0 := by
  classical
  set e : Wave := ![1, 0, 0] with he
  have h0e : (0 : Wave) ≠ e := by
    intro h
    have := congrFun h 0
    simp [he] at this
  have h0ne : (0 : Wave) ≠ -e := by
    intro h
    have := congrFun h 0
    simp [he] at this
  set modes : Finset Wave := {e, -e} with hm
  have hmem : e ∈ modes := by simp [hm]
  have hzero : (0 : Wave) ∉ modes := by
    simp only [hm, Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim h0e h0ne
  have hsym : ∀ k ∈ modes, -k ∈ modes := by
    intro k hk
    simp only [hm, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg e)
  set v₀ : State modes := fun _ => ![0, 1, 0] with hv
  have hcoord : ∀ k ∈ modes, ((k : Wave) 1 : ℤ) = 0 := by
    intro k hk
    simp only [hm, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [he]
  have htr0 : ∀ k : Wave, herm (wC k) (spread modes v₀ k) = 0 := by
    intro k
    by_cases hk : k ∈ modes
    · rw [spread_of_mem _ hk]
      show ∑ i, (starRingEnd ℂ) (wC k i) * (![0, 1, 0] : Fin 3 → ℂ) i = 0
      have := hcoord k hk
      simp [wC, Fin.sum_univ_three, this]
    · rw [spread_of_not_mem _ hk]
      simp [herm]
  have hre0 : reflSt hsym v₀ = v₀ := by
    funext k i
    show (starRingEnd ℂ) ((![0, 1, 0] : Fin 3 → ℂ) i) = (![0, 1, 0] : Fin 3 → ℂ) i
    fin_cases i <;> simp
  obtain ⟨G, hnuG, hmodes, hu0⟩ := exists_galerkinFlow hzero hsym hnu v₀ htr0 hre0
  refine ⟨G, hnuG, e, ?_⟩
  rw [hu0, spread_of_mem _ hmem]
  intro hcon
  have := congrFun hcon 1
  simp [hv] at this

end Global

end ClayNS.GalerkinODE
