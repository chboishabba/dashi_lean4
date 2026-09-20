import Mathlib
import RequestProject.NavierStokes.WaleffeGalerkinEnergy
import RequestProject.NavierStokes.R571HermitianStateVariation
import RequestProject.NavierStokes.R571PeriodicLatticeStateEnvelope

noncomputable section

namespace RequestProject.NavierStokes.R571PeriodicHermitianEnergy

open ClayNS.Waleffe
open RequestProject.NavierStokes.R571
open RequestProject.NavierStokes.R571HermitianStateVariation
open RequestProject.NavierStokes.R571PeriodicLattice

/-- One modal C^3 norm is bounded by the finite L^2 norm of the whole supported
Fourier field. -/
theorem nrm_mode_le_wienerL2_of_mem
    {modes : Finset Wave} {u : Wave → Fin 3 → ℂ}
    {k : Wave} (hk : k ∈ modes) :
    nrm (u k) ≤ wienerL2 modes u := by
  have hsum :
      nsq (u k) ≤ ∑ q ∈ modes, nsq (u q) := by
    exact Finset.single_le_sum
      (fun q _ => nsq_nonneg (u q)) hk
  simpa only [nrm, wienerL2] using Real.sqrt_le_sqrt hsum

/-- Supported-field version, valid for every wavevector, including modes outside
the truncation (where the coefficient is exactly zero). -/
theorem nrm_mode_le_wienerL2_of_support
    {modes : Finset Wave} {u : Wave → Fin 3 → ℂ}
    (hsupp : ∀ k, k ∉ modes → u k = 0) (k : Wave) :
    nrm (u k) ≤ wienerL2 modes u := by
  by_cases hk : k ∈ modes
  · exact nrm_mode_le_wienerL2_of_mem hk
  · rw [hsupp k hk]
    have hnonneg : 0 ≤ wienerL2 modes u := wienerL2_nonneg modes u
    simpa [nrm, nsq] using hnonneg

/-- Every Galerkin mode at time t is bounded by the literal total L^2 norm at
that same time. -/
theorem galerkin_mode_le_energyNorm
    (G : GalerkinFlow) (t : ℝ) (k : Wave) :
    nrm (G.u t k) ≤ wienerL2 G.modes (G.u t) :=
  nrm_mode_le_wienerL2_of_support (G.support t) k

/-- The Galerkin L^2 norm is nonincreasing. -/
theorem wienerL2_le_initial
    (G : GalerkinFlow) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) :
    wienerL2 G.modes (G.u t₁)
      ≤ wienerL2 G.modes (G.u t₀) := by
  have hE := G.energy_le_initial ht
  have h0 := G.energy_nonneg t₀
  have h1 := G.energy_nonneg t₁
  have hs0 := G.energy_eq_wienerL2_sq t₀
  have hs1 := G.energy_eq_wienerL2_sq t₁
  have hn0 := wienerL2_nonneg G.modes (G.u t₀)
  have hn1 := wienerL2_nonneg G.modes (G.u t₁)
  nlinarith

/-- Uniform-in-time modal amplitude bound by the initial L^2 norm. -/
theorem galerkin_mode_le_initialEnergyNorm
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t) (k : Wave) :
    nrm (G.u t k) ≤ wienerL2 G.modes (G.u t₀) := by
  exact le_trans
    (galerkin_mode_le_energyNorm G t k)
    (wienerL2_le_initial G ht)

/-- Physical Hermitian scalar field attached to a literal Galerkin state and a
fixed spectator vector. -/
def hermitianScalarState
    (G : GalerkinFlow) (t : ℝ) (D : Fin 3 → ℂ) : Wave → ℝ :=
  fun k => hermitianStateScalar (G.u t k) D

/-- G1 for the actual Hermitian scalar state is paid by the ordinary Galerkin
energy reservoir and spectator norm. -/
theorem hermitianScalarState_amplitude_le_initialEnergy
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (D : Fin 3 → ℂ) (k : Wave) :
    |hermitianScalarState G t D k|
      ≤ wienerL2 G.modes (G.u t₀) * nrm D := by
  apply hermitian_g1_of_vectorAmplitude
  · exact wienerL2_nonneg G.modes (G.u t₀)
  · exact galerkin_mode_le_initialEnergyNorm G ht k

/-- The complete periodic R571 state envelope for the actual Galerkin
Hermitian scalarization.  No G2/gradient hypothesis remains: lattice
discreteness turns the energy-level G1 bound into G2 = 2 G1. -/
theorem galerkinHermitianOppositeShiftEnvelope
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (D : Fin 3 → ℂ) (center shift : Wave) :
    StateDerivativeEnvelope
      (wienerL2 G.modes (G.u t₀) * nrm D)
      (2 * (wienerL2 G.modes (G.u t₀) * nrm D))
      (hermitianScalarState G t D (center + shift))
      (hermitianScalarState G t D (center - shift))
      (wlen shift) := by
  apply periodicOppositeShiftStateEnvelope
  · exact mul_nonneg
      (wienerL2_nonneg G.modes (G.u t₀))
      (nrm_nonneg D)
  · intro mode
    exact hermitianScalarState_amplitude_le_initialEnergy G ht D mode

/-- Direct R571 second-moment payment with the complete state-side coefficient
paid by initial energy.  The state coefficient is 3 E0^{1/2} ||D||. -/
theorem r571_galerkinHermitian_of_initialEnergy
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (D : Fin 3 → ℂ)
    (s : DASHI.NS.Unforced.HelicitySign)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k y : E} {center shift : Wave} {w : ℝ}
    (hy : ‖y‖ = wlen shift)
    (hw : 0 ≤ w)
    (hk : 1 ≤ ‖k‖) :
    w *
        (|radialSymbol s (k + y) - radialSymbol s k|
            * |hermitianScalarState G t D (center + shift)
                - hermitianScalarState G t D (center - shift)|
          + |centeredRadialDefect s k y|
            * |hermitianScalarState G t D (center - shift)|)
      ≤ w * (‖y‖ * ‖y‖)
          * (3 * (wienerL2 G.modes (G.u t₀) * nrm D)) := by
  have hstate := galerkinHermitianOppositeShiftEnvelope
    G ht D center shift
  rw [← hy] at hstate
  have h := r571_pairedSecondMoment_of_stateEnvelope s hw hk hstate
  convert h using 1 <;> ring

/-- If the spectator is itself a Galerkin mode, the Hermitian scalar amplitude
is bounded directly by the initial energy, with no square root remaining. -/
theorem hermitianModePair_le_initialEnergy
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (k d : Wave) :
    |hermitianStateScalar (G.u t k) (G.u t d)|
      ≤ G.energy t₀ := by
  have hk := galerkin_mode_le_initialEnergyNorm G ht k
  have hd := galerkin_mode_le_initialEnergyNorm G ht d
  have hpair := abs_hermitianStateScalar_le (G.u t k) (G.u t d)
  have hL2 : 0 ≤ wienerL2 G.modes (G.u t₀) :=
    wienerL2_nonneg G.modes (G.u t₀)
  calc
    |hermitianStateScalar (G.u t k) (G.u t d)|
        ≤ nrm (G.u t k) * nrm (G.u t d) := hpair
    _ ≤ wienerL2 G.modes (G.u t₀)
          * wienerL2 G.modes (G.u t₀) :=
      mul_le_mul hk hd (nrm_nonneg _) hL2
    _ = (wienerL2 G.modes (G.u t₀)) ^ 2 := by ring
    _ = G.energy t₀ := G.energy_eq_wienerL2_sq t₀

/-- The actual scalar state used by the Hermitian pair with a physical
spectator mode. -/
def physicalHermitianScalarState
    (G : GalerkinFlow) (t : ℝ) (spectator : Wave) : Wave → ℝ :=
  fun k => hermitianStateScalar (G.u t k) (G.u t spectator)

/-- Complete periodic state envelope with the cutoff-independent radical-free
choice G1 = E0 and G2 = 2 E0. -/
theorem physicalHermitianOppositeShiftEnvelope
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (spectator center shift : Wave) :
    StateDerivativeEnvelope
      (G.energy t₀)
      (2 * G.energy t₀)
      (physicalHermitianScalarState G t spectator (center + shift))
      (physicalHermitianScalarState G t spectator (center - shift))
      (wlen shift) := by
  apply periodicOppositeShiftStateEnvelope
  · exact G.energy_nonneg t₀
  · intro mode
    exact hermitianModePair_le_initialEnergy G ht mode spectator

/-- R571 state-side payment with coefficient exactly 3 times the initial
Galerkin energy.  No independent G1, G2, frequency derivative, or path-gradient
authority remains. -/
theorem r571_physicalHermitian_of_initialEnergy
    (G : GalerkinFlow) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (spectator : Wave)
    (s : DASHI.NS.Unforced.HelicitySign)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k y : E} {center shift : Wave} {w : ℝ}
    (hy : ‖y‖ = wlen shift)
    (hw : 0 ≤ w)
    (hk : 1 ≤ ‖k‖) :
    w *
        (|radialSymbol s (k + y) - radialSymbol s k|
            * |physicalHermitianScalarState G t spectator (center + shift)
                - physicalHermitianScalarState G t spectator (center - shift)|
          + |centeredRadialDefect s k y|
            * |physicalHermitianScalarState G t spectator (center - shift)|)
      ≤ w * (‖y‖ * ‖y‖) * (3 * G.energy t₀) := by
  have hstate := physicalHermitianOppositeShiftEnvelope
    G ht spectator center shift
  rw [← hy] at hstate
  have h := r571_pairedSecondMoment_of_stateEnvelope s hw hk hstate
  convert h using 1 <;> ring

end RequestProject.NavierStokes.R571PeriodicHermitianEnergy
