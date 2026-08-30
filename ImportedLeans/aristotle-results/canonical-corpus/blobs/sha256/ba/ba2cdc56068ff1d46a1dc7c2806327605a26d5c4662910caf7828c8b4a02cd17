/-
# The three obligations of the critical Sobolev/Simon upgrade

Alongside the network-forcing budget, the second theorem-sized obligation of the
current Navier–Stokes frontier is the *critical Sobolev/Simon upgrade*: the
passage from a cutoff-uniform critical barrier for the Galerkin approximations
to the same barrier for the limit solution, in the critical topology.

The purpose of this file is **identification, not proof**: it writes down, in
the Fourier-lattice language already used by
`WaleffeNetworkForcingBudget.lean`, the exact three statements that the upgrade
consists of.  Each is a `Prop`-valued definition; none of them is asserted, and
nothing downstream depends on them.  They are:

1. `CriticalTimeRegularity` — a cutoff-uniform bound for the time derivative of
   the Galerkin flow in `L^{4/3}_t H^{-1/2}_x`;
2. `StrongCriticalCompactness` — strong `L^2_t H^{1/2}_x` convergence of a
   subsequence of Galerkin flows to a limit element (the Simon/Aubin–Lions step
   at the critical exponent);
3. `CriticalBarrierLowerSemicontinuity` — the critical barrier
   `sup_t ‖·‖_{H^{1/2}}²` passes to the limit element (necessarily only for
   almost every time, which is the honest form of the statement).

The Sobolev quantities are the literal Fourier ones on the lattice:
`‖v‖²_{H^s} = ∑_k (1+|k|²)^s ‖v_k‖²`.
-/
import RequestProject.NavierStokes.WaleffeNetworkForcingBudget

open MeasureTheory Filter Topology

noncomputable section

namespace ClayNS.Waleffe

/-- The squared `H^s` norm of a Fourier-lattice field,
`∑_k (1+|k|²)^s ‖v_k‖²`. -/
def sobolevSq (s : ℝ) (v : Wave → Fin 3 → ℂ) : ℝ :=
  ∑' k : Wave, (1 + wsq k) ^ s * nsq (v k)

/-- The `H^s` norm of a Fourier-lattice field. -/
def sobolevNorm (s : ℝ) (v : Wave → Fin 3 → ℂ) : ℝ := Real.sqrt (sobolevSq s v)

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The time derivative of the Galerkin flow, mode by mode (zero off the
retained modes). -/
def dt (t : ℝ) (k : Wave) : Fin 3 → ℂ :=
  if k ∈ G.modes then
    fun i => -((G.nu * wsq k : ℝ) : ℂ) * G.u t k i + modalForcing G.modes (G.u t) k i
  else fun _ => 0

end GalerkinFlow

/-- **Obligation 1: critical time regularity.**  For arbitrary smooth data the
time derivatives of the Galerkin flows are bounded in `L^{4/3}_t H^{-1/2}_x`
uniformly in the truncation. -/
def CriticalTimeRegularity (nu T : ℝ) : Prop :=
  ∀ u0 : Wave → Fin 3 → ℂ, RapidlyDecaying u0 → ∃ C : ℝ,
    ∀ G : GalerkinFlow, G.nu = nu → (∀ k ∈ G.modes, G.u 0 k = u0 k) →
      (∫ t in (0:ℝ)..T, (sobolevNorm (-(1:ℝ)/2) (G.dt t)) ^ ((4:ℝ)/3)) ≤ C

/-- **Obligation 2: strong critical compactness (Simon/Aubin–Lions at the
critical exponent).**  A sequence of Galerkin flows with a common smooth datum
and exhausting mode sets has a subsequence converging strongly in
`L^2_t H^{1/2}_x` to a limit element. -/
def StrongCriticalCompactness (nu T : ℝ) : Prop :=
  ∀ (Gs : ℕ → GalerkinFlow) (u0 : Wave → Fin 3 → ℂ), RapidlyDecaying u0 →
    (∀ n, (Gs n).nu = nu) →
    (∀ n, ∀ k ∈ (Gs n).modes, (Gs n).u 0 k = u0 k) →
    (∀ k : Wave, ∃ N : ℕ, ∀ n ≥ N, k ∈ (Gs n).modes) →
    ∃ (v : ℝ → Wave → Fin 3 → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto
        (fun n => ∫ t in (0:ℝ)..T,
          sobolevSq (1/2) (fun k i => (Gs (φ n)).u t k i - v t k i))
        atTop (𝓝 0)

/-- **Obligation 3: lower semicontinuity of the critical barrier.**  If a
sequence converges strongly in `L^2_t H^{1/2}_x` and obeys a uniform critical
barrier, the limit element obeys the same barrier at almost every time. -/
def CriticalBarrierLowerSemicontinuity (T M : ℝ) : Prop :=
  ∀ (un : ℕ → ℝ → Wave → Fin 3 → ℂ) (v : ℝ → Wave → Fin 3 → ℂ),
    Tendsto (fun n => ∫ t in (0:ℝ)..T, sobolevSq (1/2) (fun k i => un n t k i - v t k i))
      atTop (𝓝 0) →
    (∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, sobolevSq (1/2) (un n t) ≤ M) →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), sobolevSq (1/2) (v t) ≤ M

end ClayNS.Waleffe
