/-
# The literal physical Galerkin network, and the exact statement of the
# Round 105 wall `PhysicalWeightedPositiveWaleffeNetworkForcingBudget`

The Waleffe lane reduces the adverse heterochiral critical production to one
quantity: a cutoff-uniform bound on the *weighted positive network forcing*
of the triad amplitudes.  In the Agda development the forcing `f_j` in the
damped–forced amplitude equation is an abstract remainder ("physical Galerkin
forcing identification" is recorded there as **not** closed).  This file makes
the whole object literal in Lean:

* the integer Fourier lattice `Wave = ℤ³`, the wavenumber square `|k|²`, and
  the **Leray projection** `P_k v = v − (k·v)k/|k|²` at a wavevector;
* the **Galerkin advection** `((u·∇)u)^_k = ∑_{p+q=k} i (u_p·q) u_q` truncated
  to a finite mode set, and the physical modal forcing
  `f_k = −P_k ((u·∇)u)^_k`;
* a `GalerkinFlow`: a finite mode set together with a time-dependent Fourier
  field solving the truncated Navier–Stokes system
  `u̇_k = −ν|k|² u_k + f_k`;
* the **triad amplitude** `A_τ = Re⟪u_k, u_p×u_q⟫` for a resonant triad
  `k = p + q`, its viscous phase-damping rate `γ_τ = ν(|k|²+|p|²+|q|²)`, and
  the **network forcing** `F_τ` obtained by inserting `f` into the three
  product-rule slots;
* the theorem `galerkin_triad_amplitude_ode`, which identifies the physical
  Galerkin forcing: for any Galerkin flow the amplitude of every triad solves
  the scalar damped–forced equation `Ȧ_τ = −γ_τ A_τ + F_τ` with `F_τ` the
  literal network forcing above.  This closes, in Lean, the identification
  step that the Agda lane leaves open;
* the definition of the open wall
  `PhysicalWeightedPositiveWaleffeNetworkForcingBudget`, and the theorem
  `weighted_integrated_production_payment` showing precisely what it buys:
  the weighted integrated adverse production of the whole network is paid by
  the initial positive amplitudes plus the budget.

Nothing here is postulated: the only hypotheses are the Galerkin equations
themselves and the pointwise production comparison already proved in
`WaleffeIntegratedPayment.lean`.
-/
import RequestProject.NavierStokes.WaleffeAmplitude
import RequestProject.NavierStokes.WaleffeIntegratedPayment

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-! ## The integer Fourier lattice and the Leray projection -/

/-- Wavevectors of the periodic problem. -/
abbrev Wave := Fin 3 → ℤ

/-- `|k|²` as a real number. -/
def wsq (k : Wave) : ℝ := ∑ i, ((k i : ℝ)) ^ 2

/-- A wavevector as a complex 3-vector. -/
def wC (k : Wave) : Fin 3 → ℂ := fun i => (k i : ℂ)

/-- The Leray projection at the wavevector `k`: `P_k v = v − (k·v) k/|k|²`. -/
def leray (k : Wave) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => v i - (herm (wC k) v / (wsq k : ℂ)) * (k i : ℂ)

theorem wsq_cast (k : Wave) : ((wsq k : ℝ) : ℂ) = (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 := by
  push_cast [wsq, Fin.sum_univ_three]
  ring

theorem herm_self (u : Fin 3 → ℂ) : herm u u = (nsq u : ℂ) := by
  simp [herm, nsq, Complex.ext_iff, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im]
  ring

theorem herm_conj (u v : Fin 3 → ℂ) : (starRingEnd ℂ) (herm u v) = herm v u := by
  simp [herm, map_sum, mul_comm]

theorem herm_add_right (u v w : Fin 3 → ℂ) :
    herm u (fun i => v i + w i) = herm u v + herm u w := by
  simp [herm, mul_add, Finset.sum_add_distrib]

theorem herm_smul_right (c : ℂ) (u v : Fin 3 → ℂ) :
    herm u (fun i => c * v i) = c * herm u v := by
  simp [herm, Finset.mul_sum]
  congr 1
  funext i
  ring

/-- The Leray projection produces a divergence-free (transverse) mode. -/
theorem herm_wC_leray (k : Wave) (v : Fin 3 → ℂ) (hk : wsq k ≠ 0) :
    herm (wC k) (leray k v) = 0 := by
  have hk' : ((wsq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  have hc := wsq_cast k
  simp only [herm, leray, wC, Fin.sum_univ_three, mul_sub, map_intCast]
  field_simp
  rw [hc]
  ring

/-- The pairing of a Leray-projected vector with the original vector is its own
squared norm; in particular it is real and nonnegative.  This is the exact
"self-forcing is a square" mechanism of the Waleffe channel. -/
theorem herm_leray_self (k : Wave) (v : Fin 3 → ℂ) (hk : wsq k ≠ 0) :
    herm (leray k v) v = (nsq (leray k v) : ℂ) := by
  have hsplit : v = fun i => leray k v i + (herm (wC k) v / (wsq k : ℂ)) * (wC k i) := by
    funext i
    simp [leray, wC]
  have hz : herm (leray k v) (wC k) = 0 := by
    have := herm_wC_leray k v hk
    have h2 := herm_conj (wC k) (leray k v)
    rw [this] at h2
    simpa using h2.symm
  calc herm (leray k v) v
      = herm (leray k v) (fun i => leray k v i + (herm (wC k) v / (wsq k : ℂ)) * (wC k i)) := by
        rw [← hsplit]
    _ = herm (leray k v) (leray k v)
          + herm (leray k v) (fun i => (herm (wC k) v / (wsq k : ℂ)) * (wC k i)) :=
        herm_add_right _ _ _
    _ = (nsq (leray k v) : ℂ) := by
        rw [herm_self, herm_smul_right, hz, mul_zero, add_zero]

/-! ## The physical Galerkin network -/

/-- The truncated Fourier transform of the advective term:
`((u·∇)u)^_k = ∑_{p+q=k} i (u_p · q) u_q`, the sum running over the retained
mode set. -/
def advection (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave) : Fin 3 → ℂ :=
  fun i => ∑ p ∈ modes, (Complex.I * (∑ j, u p j * (((k - p) j : ℤ) : ℂ))) * u (k - p) i

/-- The physical modal forcing of the Galerkin system: minus the Leray
projection of the advective term. -/
def modalForcing (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave) : Fin 3 → ℂ :=
  fun i => -(leray k (advection modes u k) i)

/-- The Euclidean length of a wavevector. -/
def wlen (k : Wave) : ℝ := Real.sqrt (wsq k)

/-- A Galerkin flow: a finite mode set of nonzero wavevectors together with a
time-dependent Fourier field supported on it, transverse (divergence free),
satisfying the reality condition of a real velocity field, and solving the
truncated Navier–Stokes system `u̇_k = −ν|k|² u_k + f_k` with the literal
projected nonlinear forcing `f_k`. -/
structure GalerkinFlow where
  /-- kinematic viscosity -/
  nu : ℝ
  /-- the viscosity is nonnegative -/
  nu_nonneg : 0 ≤ nu
  /-- retained Fourier modes -/
  modes : Finset Wave
  /-- the zero mode is not retained -/
  zero_not_mem : (0 : Wave) ∉ modes
  /-- the Fourier coefficients as functions of time -/
  u : ℝ → Wave → Fin 3 → ℂ
  /-- the field is supported on the retained modes -/
  support : ∀ (t : ℝ) (k : Wave), k ∉ modes → u t k = 0
  /-- incompressibility -/
  transverse : ∀ (t : ℝ) (k : Wave), herm (wC k) (u t k) = 0
  /-- the velocity field is real -/
  reality : ∀ (t : ℝ) (k : Wave) (i : Fin 3), u t (-k) i = (starRingEnd ℂ) (u t k i)
  /-- the truncated Navier–Stokes system, on the retained modes -/
  ode : ∀ (t : ℝ) (k : Wave), k ∈ modes → ∀ (i : Fin 3),
    HasDerivAt (fun s => u s k i)
      (-((nu * wsq k : ℝ) : ℂ) * u t k i + modalForcing modes (u t) k i) t

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The forcing of the mode `k` at time `t`. -/
def force (t : ℝ) (k : Wave) : Fin 3 → ℂ := modalForcing G.modes (G.u t) k

/-- The Waleffe amplitude of the ordered triad `(k,p,q)` at time `t`. -/
def amp (k p q : Wave) (t : ℝ) : ℝ := amplitude (G.u t k) (G.u t p) (G.u t q)

/-- The viscous phase-damping rate of the triad. -/
def gamma (k p q : Wave) : ℝ := G.nu * (wsq k + wsq p + wsq q)

/-- The network forcing of the triad at time `t`. -/
def force3 (k p q : Wave) (t : ℝ) : ℝ :=
  netForcing (G.u t k) (G.u t p) (G.u t q) (G.force t k) (G.force t p) (G.force t q)

/-- **Physical Galerkin forcing identification.**  For every Galerkin flow and
every ordered triad, the Waleffe amplitude solves the scalar damped–forced
equation with viscous rate `γ = ν(|k|²+|p|²+|q|²)` and with the *literal*
network forcing coming from the projected nonlinearity. -/
theorem triad_amplitude_ode {k p q : Wave} (hk : k ∈ G.modes) (hp : p ∈ G.modes)
    (hq : q ∈ G.modes) (t : ℝ) :
    HasDerivAt (G.amp k p q) (-(G.gamma k p q) * G.amp k p q t + G.force3 k p q t) t := by
  have h := amplitude_hasDerivAt_damped (fun s => G.u s k) (fun s => G.u s p) (fun s => G.u s q)
    (G.force t k) (G.force t p) (G.force t q)
    (G.nu * wsq k) (G.nu * wsq p) (G.nu * wsq q) t
    (fun i => G.ode t k hk i) (fun i => G.ode t p hp i) (fun i => G.ode t q hq i)
  have hg : G.nu * wsq k + G.nu * wsq p + G.nu * wsq q = G.gamma k p q := by
    simp [gamma]; ring
  rw [hg] at h
  exact h

end GalerkinFlow

/-! ## The open wall -/

/-- Ordered resonant triads `k = p + q` inside a mode set. -/
def triads (modes : Finset Wave) : Finset (Wave × Wave × Wave) :=
  (modes ×ˢ modes ×ˢ modes).filter (fun t => t.1 = t.2.1 + t.2.2)

theorem mem_triads {modes : Finset Wave} {τ : Wave × Wave × Wave} (h : τ ∈ triads modes) :
    τ.1 ∈ modes ∧ τ.2.1 ∈ modes ∧ τ.2.2 ∈ modes ∧ τ.1 = τ.2.1 + τ.2.2 := by
  simp only [triads, Finset.mem_filter, Finset.mem_product] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

/-- Rapid decay of the Fourier coefficients: the Lean rendering of "arbitrary
smooth periodic datum". -/
def RapidlyDecaying (u0 : Wave → Fin 3 → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ k : Wave, nrm (u0 k) ≤ C / (1 + wlen k) ^ N

/-- The weighted positive network-forcing expenditure of a Galerkin flow on a
time window: `∑_τ w_τ ∫_{t₀}^{t₁} (F_τ)₊`. -/
def weightedPositiveForcing (G : GalerkinFlow) (w : Wave × Wave × Wave → ℝ)
    (t₀ t₁ : ℝ) : ℝ :=
  ∑ τ ∈ triads G.modes,
    w τ * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0

/-- **`PhysicalWeightedPositiveWaleffeNetworkForcingBudget`.**  The Round 105
wall, stated literally: for arbitrary smooth (rapidly decaying) initial Fourier
data and a fixed viscosity there is a bound on the weighted positive
network-forcing expenditure over `[0,T]` which is *uniform over all Galerkin
truncations* of that datum.

The smoothness hypothesis is not decoration: without decay of `u0` the
truncation-uniform statement is hopeless already at `t = 0`, since the modal
forcing at a fixed wavevector is a convolution over the whole retained mode
set.  The mathematical content of the wall is entirely in the uniformity over
the mode set `G.modes` at fixed smooth data. -/
def PhysicalWeightedPositiveWaleffeNetworkForcingBudget
    (nu T : ℝ) (w : Wave × Wave × Wave → ℝ) : Prop :=
  ∀ u0 : Wave → Fin 3 → ℂ, RapidlyDecaying u0 → ∃ C : ℝ,
    ∀ G : GalerkinFlow, G.nu = nu → (∀ k ∈ G.modes, G.u 0 k = u0 k) →
      weightedPositiveForcing G w 0 T ≤ C

/-- **What the budget buys.**  If every triad of a finite adverse family obeys
the pointwise phase-damping comparison `ν P_τ ≤ 2 γ_τ (A_τ)₊`, then the
weighted integrated adverse production of the family is paid by the initial
positive amplitudes and by the weighted positive network forcing — i.e. by the
budget.  This is the Round 105 reduction, as an analytic theorem. -/
theorem weighted_integrated_production_payment (G : GalerkinFlow)
    (S : Finset (Wave × Wave × Wave)) (w : Wave × Wave × Wave → ℝ)
    (P : Wave × Wave × Wave → ℝ → ℝ) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hS : S ⊆ triads G.modes)
    (hw : ∀ τ ∈ S, 0 ≤ w τ)
    (hgam : ∀ τ ∈ S, 0 ≤ G.gamma τ.1 τ.2.1 τ.2.2)
    (hFc : ∀ τ ∈ S, Continuous (G.force3 τ.1 τ.2.1 τ.2.2))
    (hPc : ∀ τ ∈ S, Continuous (P τ))
    (hpay : ∀ τ ∈ S, ∀ t, G.nu * P τ t
      ≤ 2 * G.gamma τ.1 τ.2.1 τ.2.2 * max (G.amp τ.1 τ.2.1 τ.2.2 t) 0) :
    G.nu * ∑ τ ∈ S, w τ * ∫ t in t₀..t₁, P τ t
      ≤ 2 * ∑ τ ∈ S, w τ * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0
        + 2 * ∑ τ ∈ S, w τ * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := by
  have cell : ∀ τ ∈ S, G.nu * (w τ * ∫ t in t₀..t₁, P τ t)
      ≤ w τ * (2 * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0)
        + w τ * (2 * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0) := by
    intro τ hτ
    obtain ⟨hk, hp, hq, -⟩ := mem_triads (hS hτ)
    have h := cell_integrated_production_payment (A := G.amp τ.1 τ.2.1 τ.2.2)
      (F := G.force3 τ.1 τ.2.1 τ.2.2) (P := P τ) (nu := G.nu)
      (gam := G.gamma τ.1 τ.2.1 τ.2.2) (hgam τ hτ) ht (hFc τ hτ) (hPc τ hτ)
      (fun t => G.triad_amplitude_ode hk hp hq t) (hpay τ hτ)
    have hmul := mul_le_mul_of_nonneg_left h (hw τ hτ)
    calc G.nu * (w τ * ∫ t in t₀..t₁, P τ t)
        = w τ * (G.nu * ∫ t in t₀..t₁, P τ t) := by ring
      _ ≤ w τ * (2 * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0
            + 2 * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0) := hmul
      _ = w τ * (2 * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0)
            + w τ * (2 * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0) := by ring
  have hsum := Finset.sum_le_sum cell
  rw [← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have e1 : ∑ τ ∈ S, w τ * (2 * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0)
      = 2 * ∑ τ ∈ S, w τ * max (G.amp τ.1 τ.2.1 τ.2.2 t₀) 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  have e2 : ∑ τ ∈ S, w τ * (2 * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
      = 2 * ∑ τ ∈ S, w τ * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e1, e2] at hsum
  exact hsum

end ClayNS.Waleffe
