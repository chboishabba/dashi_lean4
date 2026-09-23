/-
# Reducing the uniform gap to one two-slice decorrelation estimate

`Lattice/StrongCoupling.lean` proves coercivity of the literal Wilson energy form
from a *specific* decorrelation estimate, obtained by comparing the Wilson–Gibbs
measure with the product Haar measure through the global action bound
`|S| ≤ 32|β|(n+1)⁴`.  That comparison is what makes the resulting coupling
threshold shrink like `(n+1)^{-4}`: the estimate is volume dependent for a
reason internal to the *method*, not to the statement being proved.

This file separates the two.  What the coercivity of the literal transfer form
really needs is the single inequality

    ‖⟪P₀ψ, P₁ψ⟫‖ ≤ c ‖ψ‖²     for every ψ ⊥ Ω,

where `P₀, P₁` are the two literal slice embeddings of `Lattice/TransferForm.lean`
(i.e. `T = P₁* P₀` is the Euclidean transfer operator of the Wilson measure).
Any proof of that inequality — a cluster or character expansion, a Doeblin
argument, a reflection-positivity estimate — is enough, and the constant `c`
enters the gap linearly.

Main results:

* `energyForm_coercive_of_decorrelation` — decorrelation with constant `c` gives
  coercivity of the literal Wilson form with constant `1 - c`;
* `physEnergyForm_coercive_of_decorrelation` — the same on the gauge-invariant
  physical carrier, after the `a⁻¹` rescaling, with constant `a⁻¹(1-c)`;
* `phys_hasVacuumFormGap_of_decorrelation` — the resulting vacuum form gap of the
  literal physical Hamiltonian;
* `ym_uniform_gap_of_uniform_decorrelation` — **the reduction of `F1`**: a
  decorrelation constant `c < 1` that is uniform along a trajectory
  `k ↦ (n_k, β_k, a_k)`, together with `Δ ≤ a_k⁻¹(1-c)` for every `k`, produces
  exactly the uniform-gap hypothesis consumed by `Lattice/ContinuumWeld.lean`;
* `ym_continuum_massGap_of_uniform_decorrelation` — the composite: the continuum
  mass-gap conclusion from uniform decorrelation plus the continuum-limit data.

So the finite/RG side of the Clay problem is now reduced, on the literal
four-dimensional `SU(2)` Wilson theory, to a single inequality about the
Wilson–Gibbs slice measure, uniform in the volume and the spacing.  That
inequality is **not** proved here, and the strong-coupling estimate of
`Lattice/StrongCoupling.lean` does not imply it: see `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.ContinuumWeld

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.VaryingCarrierTransport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## Decorrelation implies coercivity -/

/-- **The two-slice decorrelation estimate is all the coercivity of the literal
Wilson form needs.**  If the two slice embeddings of a vacuum-orthogonal vector
have inner product bounded by `c‖ψ‖²`, the literal energy form
`q = 1 − ½(T + T*)` is `(1 − c)`-coercive at `ψ`. -/
theorem energyForm_coercive_of_decorrelation (hchi : Continuous chi) (beta : ℝ) {c : ℝ}
    (ψ : SliceL2 n G beta chi)
    (hdec : ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2) :
    (1 - c) * ‖ψ‖ ^ 2 ≤ ((energyForm hchi beta).form ψ ψ).re := by
  have hre : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hBA : ⟪embed1 hchi beta ψ, embed0 n G beta chi ψ⟫_ℂ
      = (starRingEnd ℂ) ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [energyForm_apply, hBA]
  have hhalf : (1 / 2 : ℂ) * (⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ
      + (starRingEnd ℂ) ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ)
      = ((⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ).re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  rw [hhalf, Complex.sub_re, Complex.ofReal_re, hre]
  nlinarith [Complex.re_le_norm ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ, hdec]

/-- The same on the gauge-invariant physical carrier, after the physical
rescaling: the coercivity constant of `q_a = a⁻¹(1 − ½(T+T*))` is `a⁻¹(1-c)`. -/
theorem physEnergyForm_coercive_of_decorrelation (hchi : Continuous chi)
    (hconj : ∀ g h : G, chi (g * h * g⁻¹) = chi h) (beta a : ℝ) (ha : 0 ≤ a) {c : ℝ}
    (ψ : PhysicalSlice n hchi hconj beta)
    (hdec : ‖⟪embed0 n G beta chi (ψ : SliceL2 n G beta chi),
        embed1 hchi beta (ψ : SliceL2 n G beta chi)⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2) :
    a⁻¹ * (1 - c) * ‖ψ‖ ^ 2 ≤ ((physEnergyForm n hchi hconj beta a ha).form ψ ψ).re := by
  have hnorm : ‖ψ‖ = ‖(ψ : SliceL2 n G beta chi)‖ := rfl
  have hq := energyForm_coercive_of_decorrelation hchi beta (ψ : SliceL2 n G beta chi)
    (by rw [hnorm] at hdec; exact hdec)
  rw [physEnergyForm, restrictForm_apply, scaleForm_apply, Complex.re_ofReal_mul, hnorm]
  have hnn : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.2 ha
  nlinarith [hq]

/-- **The vacuum form gap of the literal physical Hamiltonian from
decorrelation.**  This is the hypothesis shape consumed by the continuum weld. -/
theorem phys_hasVacuumFormGap_of_decorrelation (hchi : Continuous chi)
    (hconj : ∀ g h : G, chi (g * h * g⁻¹) = chi h) (beta a : ℝ) (ha : 0 ≤ a) {c Δ : ℝ}
    (hdec : ∀ ψ : PhysicalSlice n hchi hconj beta,
      ⟪physVacuum n hchi hconj beta, ψ⟫_ℂ = 0 →
        ‖⟪embed0 n G beta chi (ψ : SliceL2 n G beta chi),
          embed1 hchi beta (ψ : SliceL2 n G beta chi)⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2)
    (hΔ : Δ ≤ a⁻¹ * (1 - c)) :
    HasVacuumFormGap (physHamiltonian n hchi hconj beta a ha)
      (physVacuum n hchi hconj beta) Δ := by
  refine (physEnergyForm n hchi hconj beta a ha).hasVacuumFormGap_hamiltonian ?_
  intro ψ hψ
  have h := physEnergyForm_coercive_of_decorrelation hchi hconj beta a ha ψ (hdec ψ hψ)
  nlinarith [sq_nonneg ‖ψ‖, h]

/-! ## The reduction of `F1` along a trajectory -/

/-- **`F1` reduced to one uniform inequality.**  Let `k ↦ (vol k, beta k, a k)` be
a trajectory of the literal four-dimensional `SU(2)` Wilson theory.  If the
two-slice decorrelation constant `c < 1` is *uniform* in `k` — in particular
uniform in the lattice volume and the spacing — and `Δ ≤ a_k⁻¹(1-c)` for every
`k`, then the literal physical Hamiltonians have the uniform vacuum form gap `Δ`
required by `Lattice/ContinuumWeld.lean`.

This is the smallest explicit remaining finite-side payment: a single correlation
inequality for the Wilson–Gibbs slice measure, with no operator theory left in
it. -/
theorem ym_uniform_gap_of_uniform_decorrelation (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) {c Δ : ℝ}
    (hdec : ∀ k, ∀ ψ : ymPhysicalSlice (vol k) (beta k),
      ⟪ymPhysicalVacuum (vol k) (beta k), ψ⟫_ℂ = 0 →
        ‖⟪embed0 (vol k) SU2 (beta k) chiSU2 (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2),
          embed1 continuous_chiSU2 (beta k)
            (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2)⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2)
    (hΔ : ∀ k, Δ ≤ (a k)⁻¹ * (1 - c)) :
    ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a ha k)
      (ymTrajectoryVacuum vol beta k) Δ := fun k =>
  phys_hasVacuumFormGap_of_decorrelation (G := SU2) continuous_chiSU2 chiSU2_conj
    (beta k) (a k) (ha k) (hdec k) (hΔ k)

/-- **The composite statement of the remaining payment.**  Uniform two-slice
decorrelation along the trajectory, isometric embeddings of the literal physical
carriers into a common Hilbert space, and an embedded vacuum-sector graph limit
that is self-adjoint with a normalised zero-energy vacuum, give the full
continuum mass-gap conclusion at gap `Δ`.

Every object on the finite side is the literal Wilson object; the hypotheses
`hdec` (`F1`), `J` (`F2`), and `hlim`/`hsa`/`hmem`/`hunit`/`hground` (`F3`) are
the only inputs. -/
theorem ym_continuum_massGap_of_uniform_decorrelation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (J : ∀ k, ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] E)
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {c Δ : ℝ} (hΔpos : 0 < Δ)
    (hdec : ∀ k, ∀ ψ : ymPhysicalSlice (vol k) (beta k),
      ⟪ymPhysicalVacuum (vol k) (beta k), ψ⟫_ℂ = 0 →
        ‖⟪embed0 (vol k) SU2 (beta k) chiSU2 (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2),
          embed1 continuous_chiSU2 (beta k)
            (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2)⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2)
    (hgapbound : ∀ k, Δ ≤ (a k)⁻¹ * (1 - c))
    (hlim : IsEmbeddedVacuumGraphLimit J (ymTrajectoryHam vol beta a ha)
      (ymTrajectoryVacuum vol beta) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain) (hunit : ‖vac‖ = 1)
    (hground : Hinf ⟨vac, hmem⟩ = 0) :
    Clay.MassGapConclusion Hinf vac Δ :=
  ym_continuum_massGap_of_uniform_gap_and_graphLimit vol beta a ha J hΔpos
    (ym_uniform_gap_of_uniform_decorrelation vol beta a ha hdec hgapbound) hlim hsa hmem
    hunit hground

/-! ## Non-vacuity of the reduced hypothesis, uniformly in the volume -/

/-- **At zero coupling the two-slice decorrelation holds with `c = 0`, uniformly
in the lattice volume.**  The two slices of the Wilson–Gibbs measure are then
independent, so a vacuum-orthogonal wavefunction decorrelates exactly.  This
shows that the reduced hypothesis of `ym_uniform_gap_of_uniform_decorrelation`
is not vacuous, and in particular that the *volume* is not what obstructs it:
the obstruction is the coupling flow `β → ∞`. -/
theorem ym_uniform_decorrelation_zero_coupling (vol : ℕ → ℕ) (hvol : ∀ k, 1 ≤ vol k) :
    ∀ k, ∀ ψ : ymPhysicalSlice (vol k) 0,
      ⟪ymPhysicalVacuum (vol k) 0, ψ⟫_ℂ = 0 →
        ‖⟪embed0 (vol k) SU2 0 chiSU2 (ψ : SliceL2 (vol k) SU2 0 chiSU2),
          embed1 continuous_chiSU2 (0 : ℝ)
            (ψ : SliceL2 (vol k) SU2 0 chiSU2)⟫_ℂ‖ ≤ 0 * ‖ψ‖ ^ 2 := by
  intro k ψ hψ
  rw [inner_embed_eq_zero (zero_ne_one_zmod (hvol k)) continuous_chiSU2 _ hψ]
  simp

/-- **A uniform gap along a zero-coupling trajectory.**  For the literal Wilson
theory at `β = 0`, with spacings bounded above by `A > 0` and arbitrary volumes,
the literal physical Hamiltonians have the *uniform* vacuum form gap `A⁻¹`.  The
free theory is of course not the continuum limit of Yang–Mills; the point of the
statement is that the uniform-gap hypothesis of the weld is inhabited by the
literal objects at unbounded volume. -/
theorem ym_uniform_gap_zero_coupling (vol : ℕ → ℕ) (hvol : ∀ k, 1 ≤ vol k) (a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {A : ℝ} (haA : ∀ k, a k ≤ A) :
    ∀ k, HasVacuumFormGap (ymTrajectoryHam vol (fun _ => 0) a (fun k => (hapos k).le) k)
      (ymTrajectoryVacuum vol (fun _ => 0) k) A⁻¹ :=
  ym_uniform_gap_of_uniform_decorrelation vol (fun _ => 0) a (fun k => (hapos k).le)
    (ym_uniform_decorrelation_zero_coupling vol hvol)
    (fun k => by
      have h : (a k)⁻¹ * (1 - 0) = (a k)⁻¹ := by ring
      rw [h]
      exact inv_anti₀ (hapos k) (haA k))

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms energyForm_coercive_of_decorrelation
#print axioms physEnergyForm_coercive_of_decorrelation
#print axioms phys_hasVacuumFormGap_of_decorrelation
#print axioms ym_uniform_gap_of_uniform_decorrelation
#print axioms ym_continuum_massGap_of_uniform_decorrelation
#print axioms ym_uniform_decorrelation_zero_coupling
#print axioms ym_uniform_gap_zero_coupling

end Audit
