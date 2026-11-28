import Synthesis.NavierStokesOriginalGlobalFullPhysicalLedgerExact
import Synthesis.NavierStokesActualFractionalSignedFTCExact

/-!
Section 31: the ORIGINAL Galerkin quarter-weight physical energy
has a cutoff-independent integrated FOURTH-power bound.

Crucial donor recovered from source:
  quarter_energy_fourth_le :
    fractionalEnergy(quarter)^4 <= periodicEnergy^3*periodicDissipation
This is already an exact same-source Fourier interpolation theorem,
not a new abstract subcritical norm. Combine it with the original
physical energy and integrated viscosity budgets on ONE Galerkin X.

This is L4_t of the quarter-ENERGY (not H1 uniform in time and
not the missing signed nonlinear-transfer bound). The actual
finite-flow differentiability/integrability is explicitly required
rather than silently inferred.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- The physical E_{1/4} fourth moment has a uniform in cutoff
time-integrated estimate, provided initial physical energy and
genuine source trajectory integrability are paid. -/
theorem original_quarter_energy_L4_time_paid_by_physical_dissipation
    (N : ℕ) (ν E₀ T : ℝ)
    (X : ℝ → FiniteState N)
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hE₀ : 0 ≤ E₀)
    (henergy : ∀ t, 0 ≤ t →
      stateEnergy (X t) ≤ E₀)
    (hvisc : 2 * ν * (∫ t in 0..T,
      periodicDissipation N (fun k s => zeroExtend (X s) k) t) ≤ E₀)
    (hq : IntervalIntegrable
      (fun t => (fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X s) k) t)^4) volume 0 T)
    (hd : IntervalIntegrable
      (fun t => periodicDissipation N
        (fun k s => zeroExtend (X s) k) t) volume 0 T) :
    2 * ν * (∫ t in 0..T,
      (fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X s) k) t)^4) ≤ E₀^4 := by
  let U : Vec3 → ℝ → CVec3 := fun k s => zeroExtend (X s) k
  have hp (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fractionalEnergy N quarterWeight U t)^4 ≤
        E₀^3 * periodicDissipation N U t := by
    have hinterp := quarter_energy_fourth_le N U t
    have hE : periodicEnergy N U t ≤ E₀ := by
      change stateEnergy (X t) ≤ E₀
      exact henergy t ht.1
    have hEpos : 0 ≤ periodicEnergy N U t := by
      change 0 ≤ stateEnergy (X t)
      exact stateEnergy_nonneg _
    have hDpos := periodicDissipation_nonneg N U t
    have hcub := pow_le_pow_left₀ hEpos hE 3
    exact hinterp.trans (mul_le_mul_of_nonneg_right hcub hDpos)
  have hmono := intervalIntegral.integral_mono_on hT
    hq (hd.const_mul (E₀^3)) hp
  rw [intervalIntegral.integral_const_mul] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hν)
  calc
    2 * ν * (∫ t in 0..T, (fractionalEnergy N quarterWeight U t)^4)
        ≤ 2 * ν * (E₀^3 * (∫ t in 0..T,
            periodicDissipation N U t)) := by
          simpa [mul_assoc] using hmul
    _ = E₀^3 * (2 * ν * (∫ t in 0..T,
          periodicDissipation N U t)) := by ring
    _ ≤ E₀^3 * E₀ := mul_le_mul_of_nonneg_left hvisc
      (pow_nonneg hE₀ 3)
    _ = E₀^4 := by ring


/-- The original global finite Galerkin equation pays its OWN interval
integrability: on a fixed finite [0,T], every Fourier component has
a physical derivative, hence the finite quarter-energy sum and
physical dissipation are continuous, and so integrable. This avoids
postulating a separate analytic scalar trajectory. -/
theorem original_actual_finite_quarter_and_dissipation_integrable
    (N : ℕ) (ν T a : ℝ) (hT : 0 ≤ T) (ha : a < 0)
    (X : ℝ → FiniteState N)
    (hODE : DASHI.NavierStokes.RealContinuation.SolvesOn
      (finiteForce N ν) X (Ioi a)) :
    IntervalIntegrable
      (fun t => (fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X s) k) t)^4) volume 0 T ∧
    IntervalIntegrable
      (fun t => periodicDissipation N
        (fun k s => zeroExtend (X s) k) t) volume 0 T := by
  let U : Vec3 → ℝ → CVec3 := fun k s => zeroExtend (X s) k
  have ho (t : ℝ) (ht : t ∈ uIcc 0 T)
      (k : Vec3) (i : Fin 3) :
      HasDerivAt (fun s => U k s i)
        (-((ν * massSq k : ℝ) : ℂ) * U k t i +
          galerkinForce N U k t i) t := by
    have h0 : 0 ≤ t := by rw [uIcc_of_le hT] at ht; exact ht.1
    exact zeroExtend_ODE_of_derivative N ν X t
      (hODE t (ha.trans_le h0)) k i
  have hc (k : Vec3) (i : Fin 3) :
      ContinuousOn (fun t => U k t i) (uIcc 0 T) :=
    fun t ht => (ho t ht k i).continuousAt.continuousWithinAt
  have hcE : ContinuousOn (fractionalEnergy N quarterWeight U) (uIcc 0 T) := by
    unfold fractionalEnergy
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.const_mul
    unfold realHermitian
    simp only [Fin.sum_univ_three]
    fun_prop
  have hcD : ContinuousOn (periodicDissipation N U) (uIcc 0 T) := by
    unfold periodicDissipation
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.const_mul
    unfold realHermitian
    simp only [Fin.sum_univ_three]
    fun_prop
  exact ⟨(hcE.pow 4).intervalIntegrable, hcD.intervalIntegrable⟩

/-- One actual globally defined finite physical flow owns ALL
fourth-moment payment inputs. The interval integrability is produced
by the actual original ODE rather than hypothesized, and the energy
and viscosity budgets are the same global-flow source. -/
theorem actual_global_original_quarter_L4_time_payment
    (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      DASHI.NavierStokes.RealContinuation.SolvesOn
        (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k,
        outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ T : ℝ, 0 ≤ T →
        2 * ν * (∫ t in 0..T,
          (fractionalEnergy N quarterWeight
            (fun k s => zeroExtend (X s) k) t)^4)
        ≤ (stateEnergy x₀)^4) := by
  obtain ⟨a, ha, X, hzero, hODE, hreal, htrans, hledger⟩ :=
    actual_global_finite_energy_and_dissipation_payment N ν hν.le x₀ hr ht
  refine ⟨a, ha, X, hzero, hODE, hreal, htrans, ?_⟩
  intro T hT
  obtain ⟨hq, hd⟩ :=
    original_actual_finite_quarter_and_dissipation_integrable
      N ν T a hT ha X hODE
  exact original_quarter_energy_L4_time_paid_by_physical_dissipation
    N ν (stateEnergy x₀) T X hT hν.le
    (stateEnergy_nonneg x₀)
    (fun t ht => (hledger t ht).1)
    (hledger T hT).2 hq hd

end
end DASHI.NavierStokes.PhysicalMixed
