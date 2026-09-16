/-
# Yang--Mills vacuum-gap backward bounds

The imported YM final lane proves the physically correct spectral theorem on the
vacuum complement.  This weld exposes the quantitative part in the direction
needed by consumer-first/BIDI proof search:

* a `VacuumGapDatum` with gap `Δ` gives the zero-shift inverse estimate
  `‖ψ‖ ≤ Δ⁻¹ ‖Hψ‖` on `Ω^⊥`;
* any independently proved positive lower bound `δ ≤ Δ` can replace `Δ`, giving
  the weaker but source-friendly budget `‖ψ‖ ≤ δ⁻¹ ‖Hψ‖`;
* a uniform cutoff gap transported by `ContinuumGapTransport` gives the same
  zero-shift estimate for the continuum operator;
* a genuine same-evolution/common-core operator equality transports the same
  quantitative budget to the welded Hamiltonian.

No Yang--Mills Hamiltonian, continuum carrier, or gap is manufactured here.  The
point is to turn a genuine physical gap lower bound into an explicit terminal
operator budget that the existing Balaban/RG source lane can work backwards
against.
-/
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.ContinuumGapTransport
import RequestProject.YangMills.SameObjectGapTransfer

namespace Welds.YMVacuumGapBackwardBounds

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A physical vacuum-sector gap immediately gives the zero-shift inverse
estimate on the vacuum complement. -/
theorem zeroShiftResolventBound (D : VacuumGapDatum E) {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (hψ : D.op ψ = y) :
    ‖(ψ : E)‖ ≤ D.gap⁻¹ * ‖y‖ := by
  simpa using
    (D.resolvent_bound_vacuumSector (lam := 0) D.gap_pos hψorth (by simpa using hψ))

/-- Lowering a proved gap constant preserves the vacuum-gap datum.  This is the
monotone interface needed by upstream analytic producers: they may prove any
positive `δ` below the physical gap without changing the Hamiltonian. -/
def weakenGapDatum (D : VacuumGapDatum E) {δ : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D.gap) : VacuumGapDatum E where
  op := D.op
  vac := D.vac
  gap := δ
  vac_mem := D.vac_mem
  vac_unit := D.vac_unit
  vac_ground := D.vac_ground
  selfAdjoint := D.selfAdjoint
  gap_pos := hδ
  form_gap := by
    intro ψ hψorth
    have hgap := D.form_gap ψ hψorth
    have hsq : 0 ≤ ‖(ψ : E)‖ ^ 2 := sq_nonneg _
    nlinarith

@[simp] theorem weakenGapDatum_op (D : VacuumGapDatum E) {δ : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D.gap) : (weakenGapDatum D hδ hδD).op = D.op := rfl

@[simp] theorem weakenGapDatum_vac (D : VacuumGapDatum E) {δ : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D.gap) : (weakenGapDatum D hδ hδD).vac = D.vac := rfl

@[simp] theorem weakenGapDatum_gap (D : VacuumGapDatum E) {δ : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D.gap) : (weakenGapDatum D hδ hδD).gap = δ := rfl

/-- **Backward target bound.**  If upstream physics can prove a positive scalar
`δ` lies below the genuine vacuum-sector gap, then every vacuum-orthogonal
zero-shift solution obeys the explicit budget `δ⁻¹`.

This is intentionally one-way: a scalar source estimate does not create the
Hamiltonian or prove `δ ≤ gap`; those remain the physical weld. -/
theorem zeroShiftResolventBoundOfGapLowerBound (D : VacuumGapDatum E) {δ : ℝ}
    (hδ : 0 < δ) (hδD : δ ≤ D.gap) {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (hψ : D.op ψ = y) :
    ‖(ψ : E)‖ ≤ δ⁻¹ * ‖y‖ := by
  simpa [weakenGapDatum] using
    (zeroShiftResolventBound (D := weakenGapDatum D hδ hδD) hψorth hψ)

/-- The same zero-shift quantitative budget after uniform cutoff-to-continuum
gap transport.  Every physical input is exactly the hypothesis required by the
existing continuum theorem. -/
theorem continuumZeroShiftResolventBound
    {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E}
    {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : RequestProject.YangMills.ContinuumGapTransport.IsVacuumGraphLimit
      H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {ψ : Hinf.domain} (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ Δ⁻¹ * ‖Hinf ψ‖ := by
  simpa using
    (RequestProject.YangMills.ContinuumGapTransport.continuum_resolvent_bound
      hgap hlim hsa hmem hunit hground hΔ (lam := 0) hΔ hψorth)

/-- **Same-object quantitative weld.**  If two self-adjoint Hamiltonians are
proved equal by differentiating the same evolution on a common core, the
zero-shift vacuum-sector inverse budget transfers with the same gap constant.

The equality is theorem-producing machinery from `SameObjectGapTransfer`; a
shared name, scalar or receipt is not accepted as a replacement. -/
theorem sameObjectZeroShiftResolventBound
    {U V : ℝ → E → E} {S : Submodule ℂ E} {H₁ H₂ : E →ₗ.[ℂ] E}
    (hUV : U = V) (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁)
    (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁)
    {ψ : H₂.domain} (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ D.gap⁻¹ * ‖H₂ ψ‖ := by
  let D₂ :=
    RequestProject.YangMills.SameObjectGapTransfer.vacuumGapDatum_of_same_evolution
      hUV hc₁ hc₂ hg₁ hg₂ D hD
  have hbound : ‖(ψ : E)‖ ≤ D₂.gap⁻¹ * ‖D₂.op ψ‖ := by
    apply zeroShiftResolventBound D₂
    · exact hψorth
    · rfl
  exact hbound

/-- **Assembled backward bound.**  A uniform cutoff vacuum gap, graph-limit
transport, and genuine same-object OS/YM weld give an explicit zero-shift
resolvent budget for the welded Hamiltonian.  This is the terminal numeric
constraint that an upstream source construction may target. -/
theorem chainZeroShiftResolventBound
    {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E} {Hinf Hos : E →ₗ.[ℂ] E}
    {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : RequestProject.YangMills.ContinuumGapTransport.IsVacuumGraphLimit
      H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {U V : ℝ → E → E} {S : Submodule ℂ E} (hUV : U = V)
    (hc₁ : Hinf.HasCore S) (hc₂ : Hos.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S Hinf)
    (hg₂ : IsPMapEvolutionGenerator V S Hos)
    {ψ : Hos.domain} (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ Δ⁻¹ * ‖Hos ψ‖ := by
  let D := RequestProject.YangMills.ContinuumGapTransport.continuumDatum
    hgap hlim hsa hmem hunit hground hΔ
  exact sameObjectZeroShiftResolventBound hUV hc₁ hc₂ hg₁ hg₂ D rfl hψorth

#print axioms zeroShiftResolventBound
#print axioms weakenGapDatum
#print axioms zeroShiftResolventBoundOfGapLowerBound
#print axioms continuumZeroShiftResolventBound
#print axioms sameObjectZeroShiftResolventBound
#print axioms chainZeroShiftResolventBound

end Welds.YMVacuumGapBackwardBounds
