/-
# The recut frontier: `F1`, `F3`, `F4` — and what is left of `F2`

Earlier statements of the remaining Yang–Mills obligations carried four items:

* `F1` a uniform positive gap along the physical trajectory;
* `F2` a common Hilbert carrier for the cutoff spaces, together with Hamiltonian
  and vacuum compatibility conditions;
* `F3` the continuum limit of the literal family;
* `F4` the Yang–Mills / Osterwalder–Schrader identification.

`F2` is no longer a separate payment, and this file says precisely what survives
of it and what does not.

* `VaryingCarrierTransport.lean` proved that the consumer needs nothing about
  the embeddings except that they are linear isometries — no intertwining, no
  vacuum compatibility, no domain preservation — because the gap hypothesis is
  formulated on each cutoff Hilbert space in its own inner product.  So the
  *compatibility* half of `F2` is gone.
* `CommonCarrier.lean` proved that a carrier with isometric embeddings always
  exists (`exists_isometric_embeddings`), so the *existence* half of `F2` is a
  construction, not a physical theorem.
* The same file proves that the canonical `ℓ²` embeddings can approximate
  nothing (`eq_zero_of_tendsto_carrierEmbedding`).  Hence the *particular*
  embeddings along which the literal Wilson family converges are genuine data of
  the continuum problem: they belong to `F3`, and no generic construction
  supplies them.  `ymCanonicalCarrier_graphLimit_degenerate` states this for the
  literal Yang–Mills family.

Contents:

* `UniformLiteralWilsonGap` — the `F1` predicate, on the literal Wilson
  Hamiltonians, and `uniformLiteralWilsonGap_zero_coupling`, which inhabits it
  at zero coupling and unbounded volume;
* `EmbeddedContinuumLimit` — the `F3` data: the embeddings, a limit operator,
  its normalised zero-energy vacuum, self-adjointness, and the embedded
  vacuum-sector graph-limit property;
* `clay_massGap_of_F1_F3` — `F1 + F3 ⇒ Clay.MassGapConclusion`;
* `clay_massGap_os_of_F1_F3_F4` — with `F4`, the same conclusion for the
  Osterwalder–Schrader Hamiltonian;
* `clay_massGap_of_transfer_defect_F3` — `F1` in its sharpest finite form (the
  per-step transfer-operator spectral defect of
  `Lattice/TransferOperatorGap.lean`) composed with `F3`;
* `clay_massGap_of_uniform_mixing_F3` — the same endpoint with `F1` in purely
  measure-theoretic form: a uniform mixing (joint density) estimate for the
  literal Wilson–Gibbs measure, from `Lattice/CorrelationCriterion.lean`.

None of `F1`, `F3`, `F4` is proved here or anywhere in this repository; they are
displayed hypotheses.  What this file settles is that they are the only three.
-/
import Mathlib
import RequestProject.YangMills.CommonCarrier
import RequestProject.YangMills.Lattice.CorrelationCriterion

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.VaryingCarrierTransport
open RequestProject.YangMills.UnboundedHamiltonianDomain
open RequestProject.YangMills.CommonCarrier

/-! ## `F1` -/

/-- **`F1`**: the literal finite-spacing Yang–Mills Hamiltonians have a vacuum
form gap `Δ`, uniformly along the trajectory `k ↦ (vol k, beta k, a k)`. -/
def UniformLiteralWilsonGap (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (Δ : ℝ) : Prop :=
  ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a ha k) (ymTrajectoryVacuum vol beta k) Δ

/-- `F1` is inhabited by the literal objects at zero coupling and unbounded
volume, with gap `A⁻¹` for any upper bound `A` on the spacings.  The free theory
is not the continuum limit of Yang–Mills; the point is that the predicate is not
vacuous and that the volume is not what obstructs it. -/
theorem uniformLiteralWilsonGap_zero_coupling (vol : ℕ → ℕ) (hvol : ∀ k, 1 ≤ vol k)
    (a : ℕ → ℝ) (hapos : ∀ k, 0 < a k) {A : ℝ} (haA : ∀ k, a k ≤ A) :
    UniformLiteralWilsonGap vol (fun _ => 0) a (fun k => (hapos k).le) A⁻¹ :=
  ym_uniform_gap_zero_coupling vol hvol a hapos haA

/-! ## `F3` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **`F3`**: the continuum limit of the literal Wilson family in a carrier `E` —
the isometric embeddings of the literal physical Hilbert spaces, a limit
operator, its normalised zero-energy vacuum, self-adjointness, and the embedded
vacuum-sector graph-limit property.

The embeddings are a *field* of this structure, not a separate obligation: by
`CommonCarrier.exists_isometric_embeddings` embeddings always exist, but by
`CommonCarrier.eq_zero_of_tendsto_carrierEmbedding` the canonical ones cannot
satisfy the graph-limit field, so choosing them is part of the continuum
problem. -/
structure EmbeddedContinuumLimit (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- The isometric embeddings of the literal cutoff Hilbert spaces. -/
  emb : ∀ k, ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] E
  /-- The continuum Hamiltonian. -/
  ham : E →ₗ.[ℂ] E
  /-- The continuum vacuum. -/
  vac : E
  /-- Self-adjointness of the continuum Hamiltonian. -/
  isSelfAdjoint : IsSelfAdjoint ham
  /-- The vacuum is in the domain. -/
  mem_domain : vac ∈ ham.domain
  /-- The vacuum is a unit vector. -/
  norm_vac : ‖vac‖ = 1
  /-- The vacuum has zero energy. -/
  ham_vac : ham ⟨vac, mem_domain⟩ = 0
  /-- The limit is the embedded vacuum-sector graph limit of the literal family. -/
  isLimit : IsEmbeddedVacuumGraphLimit emb (ymTrajectoryHam vol beta a ha)
    (ymTrajectoryVacuum vol beta) ham vac

/-! ## The endpoint on `F1 + F3` (and `F4`) -/

/-- **`F1 + F3 ⇒ the continuum mass-gap conclusion.**  No compatibility
hypothesis of any kind occurs.  The conclusion is the full
`Clay.MassGapConclusion`: the form gap on the vacuum complement, no eigenvalue in
`(0, Δ)`, unique solvability of `Hψ − λψ = y` on the vacuum sector for every real
`λ < Δ`, and the resolvent bound `(Δ − λ)⁻¹`. -/
theorem clay_massGap_of_F1_F3 (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    {Δ : ℝ} (hΔ : 0 < Δ) (hF1 : UniformLiteralWilsonGap vol beta a ha Δ)
    (L : EmbeddedContinuumLimit vol beta a ha E) :
    Clay.MassGapConclusion L.ham L.vac Δ :=
  ym_continuum_massGap_of_uniform_gap_and_graphLimit vol beta a ha L.emb hΔ hF1
    L.isLimit L.isSelfAdjoint L.mem_domain L.norm_vac L.ham_vac

/-- **`F1 + F3 + F4 ⇒ the continuum mass-gap conclusion for the
Osterwalder–Schrader Hamiltonian.**  `F4` is the identity `U = V` of the two
evolutions together with a common core on which each generates its own. -/
theorem clay_massGap_os_of_F1_F3_F4 (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    {Δ : ℝ} (hΔ : 0 < Δ) (hF1 : UniformLiteralWilsonGap vol beta a ha Δ)
    (L : EmbeddedContinuumLimit vol beta a ha E)
    {Hos : E →ₗ.[ℂ] E} {U V : ℝ → E → E} {S : Submodule ℂ E} (hUV : U = V)
    (hcYM : L.ham.HasCore S) (hcOS : Hos.HasCore S)
    (hgYM : IsPMapEvolutionGenerator U S L.ham)
    (hgOS : IsPMapEvolutionGenerator V S Hos) :
    Clay.MassGapConclusion Hos L.vac Δ :=
  ym_continuum_massGap_os_of_same_evolution vol beta a ha L.emb hΔ hF1 L.isLimit
    L.isSelfAdjoint L.mem_domain L.norm_vac L.ham_vac hUV hcYM hcOS hgYM hgOS

/-- **The endpoint on the sharpest available form of `F1`.**  The finite-side
input is the per-step transfer-operator estimate on the vacuum complement of the
literal Wilson theory, with spectral defect at least `Δ a_k`; the continuum side
is `F3`.  Nothing else is assumed. -/
theorem clay_massGap_of_transfer_defect_F3 (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {c : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hT : ∀ k, ∀ ψ : ymPhysicalSlice (vol k) (beta k),
      ⟪ymPhysicalVacuum (vol k) (beta k), ψ⟫_ℂ = 0 →
        ‖transferOp continuous_chiSU2 (beta k)
            (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2)‖ ≤ c k * ‖ψ‖)
    (hdefect : ∀ k, Δ * a k ≤ 1 - c k)
    (L : EmbeddedContinuumLimit vol beta a (fun k => (hapos k).le) E) :
    Clay.MassGapConclusion L.ham L.vac Δ :=
  clay_massGap_of_F1_F3 vol beta a (fun k => (hapos k).le) hΔ
    (ym_uniform_gap_of_trajectory_decorrelation vol beta a (fun k => (hapos k).le)
      (fun k ψ hψ =>
        decorrelation_of_transferOp_norm_le continuous_chiSU2 (beta k)
          (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2) (hT k ψ hψ))
      (trajectory_gap_bound_of_defect hapos hdefect))
    L


/-- **The endpoint on the measure-theoretic form of `F1`.**  If along the
trajectory the joint law of the two time slices of the literal Wilson measure has
density `1 + h_k` relative to the product of its marginals with `‖h_k‖ ≤ eps k`,
and `Δ·a_k ≤ 1 − eps k`, then together with `F3` the continuum Hamiltonian has
the full mass-gap conclusion.  No operator-theoretic hypothesis is left on the
finite side: the remaining input is a mixing estimate for the Wilson–Gibbs
measure. -/
theorem clay_massGap_of_uniform_mixing_F3 (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {eps : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hfun : ∀ k, (SliceIdx (vol k) → SU2) × (SliceIdx (vol k) → SU2) → ℂ)
    (hmeas : ∀ k, AEStronglyMeasurable (hfun k)
      ((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
        (sliceMeasure (vol k) SU2 (beta k) chiSU2)))
    (hbound : ∀ k, ∀ᵐ z ∂((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
        (sliceMeasure (vol k) SU2 (beta k) chiSU2)), ‖hfun k z‖ ≤ eps k)
    (hdensity : ∀ k, ∀ F : (SliceIdx (vol k) → SU2) × (SliceIdx (vol k) → SU2) → ℂ,
      Integrable F ((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
          (sliceMeasure (vol k) SU2 (beta k) chiSU2)) →
        ∫ U, F (slice0 U, slice1 U) ∂(gibbs (vol k) SU2 (beta k) chiSU2)
          = ∫ z, F z * (1 + hfun k z)
              ∂((sliceMeasure (vol k) SU2 (beta k) chiSU2).prod
                (sliceMeasure (vol k) SU2 (beta k) chiSU2)))
    (hdefect : ∀ k, Δ * a k ≤ 1 - eps k)
    (L : EmbeddedContinuumLimit vol beta a (fun k => (hapos k).le) E) :
    Clay.MassGapConclusion L.ham L.vac Δ :=
  clay_massGap_of_F1_F3 vol beta a (fun k => (hapos k).le) hΔ
    (ym_uniform_gap_of_uniform_mixing vol beta a hapos hfun hmeas hbound hdensity hdefect) L

/-! ## What the generic carrier construction does *not* give -/

/-- **The canonical common carrier of a Wilson trajectory**: the Hilbert-space
direct sum of the gauge-invariant physical Hilbert spaces along
`k ↦ (vol k, beta k)`.  It exists for every trajectory, with canonical isometric
embeddings — see `ymCanonicalEmbedding`. -/
noncomputable abbrev ymCanonicalCarrier (vol : ℕ → ℕ) (beta : ℕ → ℝ) : Type :=
  lp (fun k => ymPhysicalSlice (vol k) (beta k)) 2

/-- The canonical isometric embeddings of the literal physical Hilbert spaces
into the canonical carrier.  Their existence is all that remains of `F2`. -/
noncomputable def ymCanonicalEmbedding (vol : ℕ → ℕ) (beta : ℕ → ℝ) (k : ℕ) :
    ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] ymCanonicalCarrier vol beta :=
  carrierEmbedding (E := fun k => ymPhysicalSlice (vol k) (beta k)) k

/-- **But the canonical embeddings cannot carry a nontrivial continuum limit.**
If the literal family has an embedded vacuum-sector graph limit *along the
canonical `ℓ²` embeddings*, then the vacuum complement of the limit domain is
zero: the limit theory is empty.  So the embeddings along which the physical
family converges are genuine data of `F3`, and the generic carrier construction
cannot be mistaken for a solution of the continuum problem. -/
theorem ymCanonicalCarrier_graphLimit_degenerate (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) {Hinf : ymCanonicalCarrier vol beta →ₗ.[ℂ] ymCanonicalCarrier vol beta}
    {vac : ymCanonicalCarrier vol beta}
    (hlim : IsEmbeddedVacuumGraphLimit (ymCanonicalEmbedding vol beta)
      (ymTrajectoryHam vol beta a ha) (ymTrajectoryVacuum vol beta) Hinf vac)
    (ψ : Hinf.domain) (hψ : ⟪vac, (ψ : ymCanonicalCarrier vol beta)⟫_ℂ = 0) :
    (ψ : ymCanonicalCarrier vol beta) = 0 := by
  obtain ⟨u, hu, -, hconv, -⟩ := hlim ψ hψ
  exact eq_zero_of_tendsto_carrierEmbedding
    (E := fun k => ymPhysicalSlice (vol k) (beta k)) hconv

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms uniformLiteralWilsonGap_zero_coupling
#print axioms clay_massGap_of_F1_F3
#print axioms clay_massGap_os_of_F1_F3_F4
#print axioms clay_massGap_of_transfer_defect_F3
#print axioms clay_massGap_of_uniform_mixing_F3
#print axioms ymCanonicalEmbedding
#print axioms ymCanonicalCarrier_graphLimit_degenerate

end Audit
