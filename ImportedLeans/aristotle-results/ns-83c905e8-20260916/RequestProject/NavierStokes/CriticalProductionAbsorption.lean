/-
# S2b: the literal production-absorption target, and what it cannot be

The primary open coordinate of the periodic-B control cut is

```text
S2b :  N_N(T)  ≤  a · D_N(T) + ∫₀ᵀ R(N,t) dt
```

for the *constructed* production `N_N` of `CriticalWeightedGalerkin.lean` — not
for a similarly named signed scalar, not for a record field accepting the
estimate, and not for a compiler consuming it.

This file does three things.

1. It states the target on the literal carrier (`S2bAbsorption`) and proves the
   consumer that S2b is for: together with the unconditional S1b identity, an
   S2b payment with `a < 2ν` yields the retained-viscosity budget
   `X_N(T) + (2ν − a) ∫D_N ≤ X_N(0) + ∫R` (`retained_viscosity_budget`).  The
   corresponding Agda compiler is `NSTriadKNLuoCriticalProductionGronwallClosure`;
   here the objects are the literal Lean-carrier folds, and the *hypothesis*
   remains exactly the unpaid S2b estimate.

2. It computes the homogeneity of the three literal folds under amplitude
   scaling `u ↦ c·u`: energy and dissipation are quadratic, production is
   **cubic** (`critProductionOf_scale` etc.).  This is the exact scaling content
   of the literal fold, proved rather than quoted.

3. It derives the resulting no-go: for any field of strictly positive critical
   production, **no** state-independent constant `a` together with a remainder
   that grows at most quadratically in the amplitude can dominate the literal
   production (`no_subcubic_remainder_absorption`).  So S2b is not payable by a
   critical-energy reservoir, a dissipation multiple, or any other quadratic
   quantity: the whole content of S2b sits in the *superquadratic* part of the
   R406 remainder (its pair remainder is quintic in the state).  This is the
   literal-fold form of the scaling audit recorded in
   `NSTriadKNCriticalCompanionEnergyScalingNoGoRound151Exact`.

Nothing here proves or refutes S2b itself.
-/
import RequestProject.NavierStokes.CriticalWeightedGalerkin

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## The literal folds as functionals of a static state -/

/-- `X_N(u) = ∑_k w(k)|u_k|²` for a static field. -/
def critEnergyOf (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ modes, critWeight k * nsq (u k)

/-- `D_N(u) = ∑_k w(k)|k|²|u_k|²` for a static field. -/
def critDissipationOf (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ modes, critWeight k * wsq k * nsq (u k)

/-- `N_N(u) = 2∑_k w(k) Re⟨f_k(u),u_k⟩` for a static field, with `f` the literal
projected Galerkin nonlinearity. -/
def critProductionOf (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  2 * ∑ k ∈ modes, critWeight k * (herm (modalForcing modes u k) (u k)).re

theorem critEnergyOf_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ critEnergyOf modes u :=
  Finset.sum_nonneg fun k _ => mul_nonneg (critWeight_nonneg k) (nsq_nonneg _)

theorem critDissipationOf_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ critDissipationOf modes u :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (critWeight_nonneg k) (wsq_nonneg k)) (nsq_nonneg _)

namespace GalerkinFlow

variable (G : GalerkinFlow)

theorem critEnergy_eq (t : ℝ) : G.critEnergy t = critEnergyOf G.modes (G.u t) := rfl

theorem critDissipationRate_eq (t : ℝ) :
    G.critDissipationRate t = critDissipationOf G.modes (G.u t) := rfl

theorem critProductionRate_eq (t : ℝ) :
    G.critProductionRate t = critProductionOf G.modes (G.u t) := rfl

end GalerkinFlow

/-! ## 1. The S2b target and its consumer -/

/-- **The literal S2b target.**  For the constructed production of a Galerkin
flow: the time-integrated signed production is dominated by `a` times the
integrated critical dissipation plus the integrated remainder `R`. -/
def S2bAbsorption (G : GalerkinFlow) (a : ℝ) (R : ℝ → ℝ) (t₀ t₁ : ℝ) : Prop :=
  (∫ t in t₀..t₁, G.critProductionRate t)
    ≤ a * (∫ t in t₀..t₁, G.critDissipationRate t) + ∫ t in t₀..t₁, R t

/-- **The consumer of S2b.**  An S2b payment with absorbed coefficient `a`
converts the unconditional S1b identity into the retained-viscosity budget: the
terminal critical energy plus `(2ν − a)` times the integrated critical
dissipation is paid by the initial critical energy and the remainder.  The
retained coefficient is positive exactly when `a < 2ν`, which is the separate
S4 coordinate. -/
theorem retained_viscosity_budget (G : GalerkinFlow) (a : ℝ) (R : ℝ → ℝ) (t₀ t₁ : ℝ)
    (h : S2bAbsorption G a R t₀ t₁) :
    G.critEnergy t₁ + (2 * G.nu - a) * (∫ t in t₀..t₁, G.critDissipationRate t)
      ≤ G.critEnergy t₀ + ∫ t in t₀..t₁, R t := by
  have hbal := G.critEnergy_balance t₀ t₁
  have h' := h
  unfold S2bAbsorption at h'
  nlinarith [hbal, h']

/-! ## 2. Homogeneity of the literal folds -/

/-- Amplitude scaling of a state by a real factor. -/
def scaleField (c : ℝ) (u : Wave → Fin 3 → ℂ) : Wave → Fin 3 → ℂ :=
  fun k i => (c : ℂ) * u k i

theorem nsq_scaleField (c : ℝ) (u : Wave → Fin 3 → ℂ) (k : Wave) :
    nsq (scaleField c u k) = c ^ 2 * nsq (u k) := by
  simp only [nsq, scaleField, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem critEnergyOf_scale (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℝ) :
    critEnergyOf modes (scaleField c u) = c ^ 2 * critEnergyOf modes u := by
  simp only [critEnergyOf, nsq_scaleField, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem critDissipationOf_scale (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℝ) :
    critDissipationOf modes (scaleField c u) = c ^ 2 * critDissipationOf modes u := by
  simp only [critDissipationOf, nsq_scaleField, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem advection_scale (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℝ) (k : Wave) :
    advection modes (scaleField c u) k = fun i => (c : ℂ) ^ 2 * advection modes u k i := by
  funext i
  simp only [advection, scaleField]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hs : ∑ j, (c : ℂ) * u p j * (((k - p) j : ℤ) : ℂ)
      = (c : ℂ) * ∑ j, u p j * (((k - p) j : ℤ) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

theorem herm_wC_scale (c : ℂ) (k : Wave) (v : Fin 3 → ℂ) :
    herm (wC k) (fun i => c * v i) = c * herm (wC k) v := herm_smul_right c _ v

theorem leray_scale (c : ℂ) (k : Wave) (v : Fin 3 → ℂ) :
    leray k (fun i => c * v i) = fun i => c * leray k v i := by
  funext i
  simp only [leray, herm_wC_scale]
  ring

theorem modalForcing_scale (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℝ) (k : Wave) :
    modalForcing modes (scaleField c u) k = fun i => (c : ℂ) ^ 2 * modalForcing modes u k i := by
  funext i
  simp only [modalForcing, advection_scale, leray_scale]
  ring

/-- **The literal production is cubic in the amplitude.** -/
theorem critProductionOf_scale (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℝ) :
    critProductionOf modes (scaleField c u) = c ^ 3 * critProductionOf modes u := by
  have hterm : ∀ k : Wave,
      (herm (modalForcing modes (scaleField c u) k) (scaleField c u k)).re
        = c ^ 3 * (herm (modalForcing modes u k) (u k)).re := by
    intro k
    have h1 : herm (modalForcing modes (scaleField c u) k) (scaleField c u k)
        = ((c ^ 3 : ℝ) : ℂ) * herm (modalForcing modes u k) (u k) := by
      rw [modalForcing_scale]
      simp only [herm, scaleField]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, Complex.conj_ofReal]
      push_cast
      ring
    rw [h1, Complex.re_ofReal_mul]
  have hsum : ∑ k ∈ modes,
        critWeight k * (herm (modalForcing modes (scaleField c u) k) (scaleField c u k)).re
      = c ^ 3 * ∑ k ∈ modes, critWeight k * (herm (modalForcing modes u k) (u k)).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hterm k]; ring
  simp only [critProductionOf, hsum]
  ring

/-! ## 3. The no-go: S2b cannot be paid by a quadratic reservoir -/

/-- **No state-independent absorption with a subcubic remainder.**  Let `u` be a
state with strictly positive literal critical production.  Then for every
constant `a` and every remainder functional whose value along the amplitude ray
`c ↦ c·u` is at most quadratic in `c`, there is an amplitude at which the S2b
inequality fails.

Consequently the R406 remainder cannot be replaced, in S2b, by any multiple of
the critical energy, of the critical dissipation, or of any other quadratic
functional of the state: the payment must come from a genuinely superquadratic
object. -/
theorem no_subcubic_remainder_absorption {modes : Finset Wave} {u : Wave → Fin 3 → ℂ}
    (hP : 0 < critProductionOf modes u) (a K : ℝ)
    (R : (Wave → Fin 3 → ℂ) → ℝ)
    (hR : ∀ c : ℝ, 1 ≤ c → R (scaleField c u) ≤ K * c ^ 2) :
    ∃ c : ℝ, 1 ≤ c ∧
      a * critDissipationOf modes (scaleField c u) + R (scaleField c u)
        < critProductionOf modes (scaleField c u) := by
  set D := critDissipationOf modes u with hD
  set P := critProductionOf modes u with hPdef
  set c : ℝ := max 1 ((a * D + K) / P + 1) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcbig : (a * D + K) / P + 1 ≤ c := le_max_right _ _
  have hkey : a * D + K < c * P := by
    have h1 : (a * D + K) / P < c := by linarith
    rw [div_lt_iff₀ hP] at h1
    linarith [h1]
  refine ⟨c, hc1, ?_⟩
  rw [critDissipationOf_scale, critProductionOf_scale]
  have hRc := hR c hc1
  have hsq : (0 : ℝ) < c ^ 2 := by positivity
  have : a * (c ^ 2 * D) + K * c ^ 2 < c ^ 3 * P := by
    have h := mul_lt_mul_of_pos_left hkey hsq
    nlinarith [h]
  linarith

end ClayNS.Waleffe
