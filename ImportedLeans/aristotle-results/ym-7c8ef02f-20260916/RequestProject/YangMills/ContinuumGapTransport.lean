/-
# Cutoff → continuum transport of the vacuum mass gap

`VacuumSectorSpectralGap` turns a form gap above a zero-energy vacuum into a
genuine resolvent statement.  This module supplies the step *before* it: a
cutoff family of Hamiltonians with a **uniform** gap above their (moving) vacua
hands its gap to the limit operator, with no spectral pollution.

The transport hypothesis is the physically meaningful one — *graph* convergence
along vacuum-orthogonal approximants:

> for `ψ` in the limit domain with `ψ ⊥ Ω`, there are `ψₙ ∈ D(Hₙ)` with
> `ψₙ ⊥ Ωₙ`, `ψₙ → ψ` and `Hₙψₙ → Hψ`.

Main results:

* `formGap_le_of_graphLimit` — the pointwise transport: a uniform gap `Δ` for
  the family gives `Δ‖ψ‖² ≤ re⟪ψ, Hψ⟫` at every limit point reached this way.
  No self-adjointness, no boundedness, and no completeness is used.
* `formGap_le_of_graphLimit_tendsto` — the same with cutoff-dependent gaps
  `Δₙ → Δ`, so the gap constant may drift as long as it converges.
* `hasVacuumFormGap_of_graphLimit` — the whole vacuum form gap of the limit,
  when every vacuum-orthogonal limit vector is reachable.
* `continuumDatum` — assembles the limit `VacuumGapDatum` from the cutoff
  family, given that the limit operator is self-adjoint with the limit vacuum as
  a normalised zero mode.
* `continuum_no_spectrum_below_gap` and `continuum_resolvent_bound` — the
  endpoint of this lane: *the continuum Hamiltonian has no spectrum in `[0, Δ)`
  on the vacuum complement*, obtained by composing the transport with the
  carrier's resolvent theorem.  This is exactly "the uniform lattice gap
  survives the continuum limit, and the limit acquires no spectrum below it".
* `graphLimit_of_eventually_eq` — non-vacuity: a constant family transports its
  own gap, so the hypotheses are satisfiable.

Honest scope: the cutoff Hamiltonians, their uniform gap, the limit operator,
its self-adjointness and the graph convergence are all *inputs*.  Nothing here
constructs the Yang–Mills lattice family or proves that it converges.  What is
removed is every generic operator-theoretic step between "uniform gap along the
cutoffs" and "spectral gap in the continuum".
-/
import Mathlib
import RequestProject.YangMills.UnboundedFormGapResolvent
import RequestProject.YangMills.VacuumSectorSpectralGap

namespace RequestProject.YangMills.ContinuumGapTransport

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Pointwise transport along graph limits -/

/-- **Transport of the form gap along a graph limit.**  If every cutoff
Hamiltonian `H n` has form gap `Δ` above its own vacuum `vacn n`, and the limit
vector `ψ` is reached by vacuum-orthogonal approximants converging in the graph
sense, then the limit quadratic form obeys the same lower bound at `ψ`. -/
theorem formGap_le_of_graphLimit {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    {a : ℕ → E} (ha : ∀ n, a n ∈ (H n).domain)
    (haorth : ∀ n, ⟪vacn n, a n⟫_ℂ = 0)
    {x y : E} (hconv : Tendsto a atTop (𝓝 x))
    (hopconv : Tendsto (fun n => (H n) ⟨a n, ha n⟩) atTop (𝓝 y)) :
    Δ * ‖x‖ ^ 2 ≤ (⟪x, y⟫_ℂ).re := by
  have hstep : ∀ n, Δ * ‖a n‖ ^ 2 ≤ (⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ).re := by
    intro n
    simpa using hgap n ⟨a n, ha n⟩ (haorth n)
  have hL : Tendsto (fun n => Δ * ‖a n‖ ^ 2) atTop (𝓝 (Δ * ‖x‖ ^ 2)) := by
    exact ((hconv.norm).pow 2).const_mul Δ
  have hR : Tendsto (fun n => (⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ).re) atTop
      (𝓝 ((⟪x, y⟫_ℂ).re)) := by
    have hinner : Tendsto (fun n => ⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ) atTop (𝓝 (⟪x, y⟫_ℂ)) :=
      (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp (hconv.prodMk_nhds hopconv)
    exact Complex.continuous_re.tendsto _ |>.comp hinner
  exact le_of_tendsto_of_tendsto' hL hR hstep

/-- **Transport with drifting gap constants.**  The gap of the cutoff at scale
`n` may be `Δ n`; if `Δ n → Δ` the limit still obeys the bound with `Δ`. -/
theorem formGap_le_of_graphLimit_tendsto {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {gapn : ℕ → ℝ} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) (gapn n))
    (hgaplim : Tendsto gapn atTop (𝓝 Δ))
    {a : ℕ → E} (ha : ∀ n, a n ∈ (H n).domain)
    (haorth : ∀ n, ⟪vacn n, a n⟫_ℂ = 0)
    {x y : E} (hconv : Tendsto a atTop (𝓝 x))
    (hopconv : Tendsto (fun n => (H n) ⟨a n, ha n⟩) atTop (𝓝 y)) :
    Δ * ‖x‖ ^ 2 ≤ (⟪x, y⟫_ℂ).re := by
  have hstep : ∀ n, gapn n * ‖a n‖ ^ 2 ≤ (⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ).re := by
    intro n
    simpa using hgap n ⟨a n, ha n⟩ (haorth n)
  have hL : Tendsto (fun n => gapn n * ‖a n‖ ^ 2) atTop (𝓝 (Δ * ‖x‖ ^ 2)) :=
    hgaplim.mul ((hconv.norm).pow 2)
  have hR : Tendsto (fun n => (⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ).re) atTop
      (𝓝 ((⟪x, y⟫_ℂ).re)) := by
    have hinner : Tendsto (fun n => ⟪a n, (H n) ⟨a n, ha n⟩⟫_ℂ) atTop (𝓝 (⟪x, y⟫_ℂ)) :=
      (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp (hconv.prodMk_nhds hopconv)
    exact Complex.continuous_re.tendsto _ |>.comp hinner
  exact le_of_tendsto_of_tendsto' hL hR hstep

/-! ## The transport hypothesis, as a predicate -/

/-- `Hinf` is a **vacuum-sector graph limit** of the cutoff family `H` with
vacua `vacn` and limit vacuum `vac`: every domain vector of `Hinf` orthogonal to
`vac` is the limit of vacuum-orthogonal domain vectors of the cutoffs, in the
graph sense. -/
def IsVacuumGraphLimit (H : ℕ → E →ₗ.[ℂ] E) (vacn : ℕ → E)
    (Hinf : E →ₗ.[ℂ] E) (vac : E) : Prop :=
  ∀ ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
    ∃ (a : ℕ → E) (ha : ∀ n, a n ∈ (H n).domain),
      (∀ n, ⟪vacn n, a n⟫_ℂ = 0) ∧ Tendsto a atTop (𝓝 (ψ : E)) ∧
        Tendsto (fun n => (H n) ⟨a n, ha n⟩) atTop (𝓝 (Hinf ψ))

/-- **The limit Hamiltonian inherits the uniform gap.** -/
theorem hasVacuumFormGap_of_graphLimit {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac Δ := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact formGap_le_of_graphLimit hgap ha haorth hconv hopconv

/-- The drifting-constant version of the previous theorem. -/
theorem hasVacuumFormGap_of_graphLimit_tendsto {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {gapn : ℕ → ℝ} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) (gapn n))
    (hgaplim : Tendsto gapn atTop (𝓝 Δ))
    (hlim : IsVacuumGraphLimit H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac Δ := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact formGap_le_of_graphLimit_tendsto hgap hgaplim ha haorth hconv hopconv

/-! ## The continuum datum and its spectral gap -/

section Continuum

variable [CompleteSpace E]

/-- **The continuum carrier from the cutoff family.**  Given a uniform gap `Δ`
along the cutoffs, a vacuum-sector graph limit, and the limit operator's
self-adjointness together with a normalised zero-energy limit vacuum, the limit
is a `VacuumGapDatum` with gap `Δ`. -/
def continuumDatum {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0)
    (hΔ : 0 < Δ) : VacuumGapDatum E where
  op := Hinf
  vac := vac
  gap := Δ
  vac_mem := hmem
  vac_unit := hunit
  vac_ground := hground
  selfAdjoint := hsa
  gap_pos := hΔ
  form_gap := hasVacuumFormGap_of_graphLimit hgap hlim

@[simp] theorem continuumDatum_gap {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    (continuumDatum hgap hlim hsa hmem hunit hground hΔ).gap = Δ := rfl

@[simp] theorem continuumDatum_op {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    (continuumDatum hgap hlim hsa hmem hunit hground hΔ).op = Hinf := rfl

/-- **No spectral pollution in the continuum limit.**  Under the hypotheses
above, the limit Hamiltonian has no spectrum in `[0, Δ)` on the vacuum
complement: for every real `lam < Δ` and every `y ⊥ vac` the equation
`Hψ - lam ψ = y` has a unique vacuum-orthogonal solution in the domain.

Note the direction of the statement: the gap is *uniform along the cutoffs* and
the conclusion is about the *limit*, so no eigenvalue may appear in the gap as
the cutoff is removed. -/
theorem continuum_no_spectrum_below_gap {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} (hlt : lam < Δ) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      Hinf ψ - (lam : ℂ) • (ψ : E) = y :=
  (continuumDatum hgap hlim hsa hmem hunit hground hΔ).exists_unique_solution_vacuumSector
    hlt hy

/-- The quantitative continuum resolvent bound. -/
theorem continuum_resolvent_bound {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} (hlt : lam < Δ) {ψ : Hinf.domain}
    (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ (Δ - lam)⁻¹ * ‖Hinf ψ - (lam : ℂ) • (ψ : E)‖ :=
  (continuumDatum hgap hlim hsa hmem hunit hground hΔ).resolvent_bound_vacuumSector
    hlt hψorth rfl

/-- **The continuum mass gap in eigenvalue form.**  Any excited state of the
limit Hamiltonian orthogonal to the vacuum has energy at least `Δ`. -/
theorem continuum_no_eigenvalue_below_gap {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} {ψ : Hinf.domain} (hne : (ψ : E) ≠ 0)
    (heig : Hinf ψ = (lam : ℂ) • (ψ : E)) (hlt : lam < Δ) :
    lam = 0 :=
  (continuumDatum hgap hlim hsa hmem hunit hground hΔ).eigenvalue_eq_zero_of_lt_gap
    hne heig hlt

end Continuum

/-! ## Non-vacuity of the transport hypothesis -/

/-- A constant cutoff family is its own vacuum-sector graph limit, so
`IsVacuumGraphLimit` is satisfiable and the transport theorems are not vacuous. -/
theorem isVacuumGraphLimit_const (Hinf : E →ₗ.[ℂ] E) (vac : E) :
    IsVacuumGraphLimit (fun _ => Hinf) (fun _ => vac) Hinf vac := by
  intro ψ hψ
  exact ⟨fun _ => (ψ : E), fun _ => ψ.2, fun _ => hψ, tendsto_const_nhds,
    tendsto_const_nhds⟩

/-- The constant family transports its own gap: a sanity check that
`hasVacuumFormGap_of_graphLimit` does not lose information. -/
theorem hasVacuumFormGap_const {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : HasVacuumFormGap Hinf vac Δ) : HasVacuumFormGap Hinf vac Δ :=
  hasVacuumFormGap_of_graphLimit (H := fun _ => Hinf) (vacn := fun _ => vac)
    (fun _ => hgap) (isVacuumGraphLimit_const Hinf vac)

/-- The drifting gap constants `Δₙ = Δ + 1/(n+1)` converge to `Δ`. -/
theorem gap_drift_tendsto (Δ : ℝ) :
    Tendsto (fun n : ℕ => Δ + 1 / (n + 1 : ℝ)) atTop (𝓝 Δ) := by
  have h : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.add h

section DriftWitness

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- **A genuinely non-constant cutoff family.**  The projection Hamiltonians
`Δₙ · P` with common vacuum `vac` and strictly decreasing gaps
`Δₙ = Δ + 1/(n+1)` form a vacuum-sector graph limit of `Δ · P`: the operators
really change with the cutoff and still converge on the vacuum complement. -/
theorem isVacuumGraphLimit_projHam (vac : E) (Δ : ℝ) :
    IsVacuumGraphLimit (fun n : ℕ => projHam vac (Δ + 1 / (n + 1 : ℝ)))
      (fun _ => vac) (projHam vac Δ) vac := by
  intro ψ hψ
  refine ⟨fun _ => (ψ : E), fun _ => Submodule.mem_top, fun _ => hψ,
    tendsto_const_nhds, ?_⟩
  have happ : ∀ n : ℕ,
      (projHam vac (Δ + 1 / (n + 1 : ℝ))) ⟨(ψ : E), Submodule.mem_top⟩
        = ((Δ + 1 / (n + 1 : ℝ) : ℝ) : ℂ) • (ψ : E) := fun n =>
    projHam_apply_of_orthogonal _ hψ
  have hlim : Tendsto (fun n : ℕ => ((Δ + 1 / (n + 1 : ℝ) : ℝ) : ℂ) • (ψ : E)) atTop
      (𝓝 (((Δ : ℝ) : ℂ) • (ψ : E))) := by
    refine Tendsto.smul ?_ tendsto_const_nhds
    exact (Complex.continuous_ofReal.tendsto _).comp (gap_drift_tendsto Δ)
  rw [projHam_apply_of_orthogonal ψ hψ]
  exact (hlim.congr (fun n => (happ n).symm))

omit [CompleteSpace E] in
/-- The drifting family transports its gap to the limit: the limit projection
Hamiltonian has vacuum form gap `Δ`, obtained purely from the cutoff gaps
`Δ + 1/(n+1)`. -/
theorem hasVacuumFormGap_projHam_of_drift (vac : E) (Δ : ℝ) :
    HasVacuumFormGap (projHam vac Δ) vac Δ :=
  hasVacuumFormGap_of_graphLimit_tendsto
    (H := fun n : ℕ => projHam vac (Δ + 1 / (n + 1 : ℝ))) (vacn := fun _ => vac)
    (fun n => hasVacuumFormGap_projHam vac (Δ + 1 / (n + 1 : ℝ)))
    (gap_drift_tendsto Δ) (isVacuumGraphLimit_projHam vac Δ)

/-- **The end of this lane, on a witness.**  For a unit vacuum and `Δ > 0`, the
limit of the drifting cutoff family has no spectrum in `[0, Δ)` on the vacuum
complement.  Every hypothesis of `continuum_no_spectrum_below_gap` is discharged
here, so the continuum statement is inhabited rather than conditional. -/
theorem drift_continuum_no_spectrum_below_gap (vac : E) (hvac : ‖vac‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) {lam : ℝ} (hlt : lam < Δ) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : (projHam vac Δ).domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      projHam vac Δ ψ - (lam : ℂ) • (ψ : E) = y :=
  continuum_no_spectrum_below_gap
    (H := fun n : ℕ => projHam vac (Δ + 1 / (n + 1 : ℝ))) (vacn := fun _ => vac)
    (fun n ψ hψ => le_trans (by
      have hnn : (0 : ℝ) ≤ ‖(ψ : E)‖ ^ 2 := sq_nonneg _
      have hpos : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := by positivity
      nlinarith)
      (hasVacuumFormGap_projHam vac (Δ + 1 / (n + 1 : ℝ)) ψ hψ))
    (isVacuumGraphLimit_projHam vac Δ) (isSelfAdjoint_projHam vac Δ)
    Submodule.mem_top hvac (projHam_vac vac Δ) hΔ hlt hy

end DriftWitness

/-! ## Axiom audit -/

section Audit

#print axioms formGap_le_of_graphLimit
#print axioms formGap_le_of_graphLimit_tendsto
#print axioms hasVacuumFormGap_of_graphLimit
#print axioms hasVacuumFormGap_of_graphLimit_tendsto
#print axioms continuum_no_spectrum_below_gap
#print axioms continuum_resolvent_bound
#print axioms continuum_no_eigenvalue_below_gap
#print axioms isVacuumGraphLimit_const
#print axioms gap_drift_tendsto
#print axioms isVacuumGraphLimit_projHam
#print axioms hasVacuumFormGap_projHam_of_drift
#print axioms drift_continuum_no_spectrum_below_gap

end Audit

end RequestProject.YangMills.ContinuumGapTransport
