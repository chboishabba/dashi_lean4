/-
# Varying-carrier transport of the vacuum mass gap

`ContinuumGapTransport` transports a uniform vacuum form gap from a cutoff
family to its graph limit, but it assumes that **all** cutoff Hamiltonians act
on one and the same Hilbert space `E`.  The literal lattice construction of
`RequestProject/YangMills/Lattice/` does not have that shape: the physical
carrier at volume parameter `n` and coupling `β` is `L²_gauge(μ_{n,β})`, a
different Hilbert space for every cutoff.  That mismatch is a structural gap
between the literal lattice lane and the continuum consumer, and this file
closes it.

The setting here is a genuinely varying family of complex inner-product spaces
`F : ℕ → Type*`, each with its own Hamiltonian `H n : F n →ₗ.[ℂ] F n` and its
own vacuum `vacn n : F n`, together with linear **isometric embeddings**
`J n : F n →ₗᵢ[ℂ] E` into a common carrier.  Nothing else is required of the
embeddings: no compatibility between different `n`, no intertwining relation
with a second family of operators on `E`, and no identification of the vacua.
The reason is that the gap hypothesis and the convergence hypothesis are stated
where they physically live — the gap on each `F n` in its own inner product, the
convergence in `E` after embedding.

Main results:

* `formGap_le_of_embeddedGraphLimit` — pointwise transport of the form bound
  through the embeddings (uniform gap constant);
* `formGap_le_of_embeddedGraphLimit_tendsto` — the same with drifting constants
  `Δₙ → Δ`;
* `IsEmbeddedVacuumGraphLimit` — the varying-carrier convergence predicate;
* `hasVacuumFormGap_of_embeddedGraphLimit` (and its drifting version) — the
  limit operator on `E` inherits the uniform gap;
* `embeddedContinuumDatum` — the limit `VacuumGapDatum` on `E`;
* `embedded_no_spectrum_below_gap`, `embedded_resolvent_bound`,
  `embedded_no_eigenvalue_below_gap` — the resulting continuum spectral
  statements;
* `isEmbeddedVacuumGraphLimit_of_isVacuumGraphLimit` and
  `hasVacuumFormGap_of_graphLimit_of_embedded` — the fixed-carrier theory of
  `ContinuumGapTransport` is recovered as the special case `J n = id`, so the
  two convergence frameworks are connected rather than parallel;
* `isEmbeddedVacuumGraphLimit_subtype` and `embeddedContinuumDatum_subtype` —
  the subspace-carrier instance: cutoff Hilbert spaces given as closed subspaces
  of `E`, embedded by inclusion.  This is a carrier family whose type genuinely
  depends on the cutoff.

Honest scope: the cutoff Hamiltonians, the embeddings, the uniform gap, the
limit operator, its self-adjointness and the graph convergence are all *inputs*.
Nothing here constructs the Yang–Mills family, its embeddings, or its limit.
What is removed is the requirement that the cutoff carriers be literally equal
to the continuum carrier.
-/
import Mathlib
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.ContinuumGapTransport

namespace RequestProject.YangMills.VaryingCarrierTransport

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]

/-! ## Pointwise transport through the embeddings -/

/-- **Transport of the form gap through isometric embeddings.**  Each cutoff
Hamiltonian `H n` lives on its own space `F n` and has form gap `Δ` above its own
vacuum `vacn n`.  If a limit vector `x ∈ E` is reached by the embedded images of
vacuum-orthogonal domain vectors, in the graph sense, the limit quadratic form
obeys the same lower bound at `x`.

The only property of the embeddings used is that they preserve norms and inner
products; in particular the vacua of the cutoffs need not be related to each
other or to any vector of `E`. -/
theorem formGap_le_of_embeddedGraphLimit {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    {a : ∀ n, F n} (ha : ∀ n, a n ∈ (H n).domain)
    (haorth : ∀ n, ⟪vacn n, a n⟫_ℂ = 0)
    {x y : E} (hconv : Tendsto (fun n => J n (a n)) atTop (𝓝 x))
    (hopconv : Tendsto (fun n => J n ((H n) ⟨a n, ha n⟩)) atTop (𝓝 y)) :
    Δ * ‖x‖ ^ 2 ≤ (⟪x, y⟫_ℂ).re := by
  have hstep : ∀ n,
      Δ * ‖J n (a n)‖ ^ 2 ≤ (⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ).re := by
    intro n
    have h := hgap n ⟨a n, ha n⟩ (haorth n)
    rw [(J n).norm_map, (J n).inner_map_map]
    simpa using h
  have hL : Tendsto (fun n => Δ * ‖J n (a n)‖ ^ 2) atTop (𝓝 (Δ * ‖x‖ ^ 2)) :=
    ((hconv.norm).pow 2).const_mul Δ
  have hR : Tendsto (fun n => (⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ).re) atTop
      (𝓝 ((⟪x, y⟫_ℂ).re)) := by
    have hinner : Tendsto (fun n => ⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ) atTop
        (𝓝 (⟪x, y⟫_ℂ)) :=
      (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp (hconv.prodMk_nhds hopconv)
    exact Complex.continuous_re.tendsto _ |>.comp hinner
  exact le_of_tendsto_of_tendsto' hL hR hstep

/-- The drifting-constant version: the gap of the cutoff at scale `n` may be
`gapn n`, and only `gapn n → Δ` is required. -/
theorem formGap_le_of_embeddedGraphLimit_tendsto {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {gapn : ℕ → ℝ} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) (gapn n))
    (hgaplim : Tendsto gapn atTop (𝓝 Δ))
    {a : ∀ n, F n} (ha : ∀ n, a n ∈ (H n).domain)
    (haorth : ∀ n, ⟪vacn n, a n⟫_ℂ = 0)
    {x y : E} (hconv : Tendsto (fun n => J n (a n)) atTop (𝓝 x))
    (hopconv : Tendsto (fun n => J n ((H n) ⟨a n, ha n⟩)) atTop (𝓝 y)) :
    Δ * ‖x‖ ^ 2 ≤ (⟪x, y⟫_ℂ).re := by
  have hstep : ∀ n,
      gapn n * ‖J n (a n)‖ ^ 2 ≤ (⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ).re := by
    intro n
    have h := hgap n ⟨a n, ha n⟩ (haorth n)
    rw [(J n).norm_map, (J n).inner_map_map]
    simpa using h
  have hL : Tendsto (fun n => gapn n * ‖J n (a n)‖ ^ 2) atTop (𝓝 (Δ * ‖x‖ ^ 2)) :=
    hgaplim.mul ((hconv.norm).pow 2)
  have hR : Tendsto (fun n => (⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ).re) atTop
      (𝓝 ((⟪x, y⟫_ℂ).re)) := by
    have hinner : Tendsto (fun n => ⟪J n (a n), J n ((H n) ⟨a n, ha n⟩)⟫_ℂ) atTop
        (𝓝 (⟪x, y⟫_ℂ)) :=
      (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp (hconv.prodMk_nhds hopconv)
    exact Complex.continuous_re.tendsto _ |>.comp hinner
  exact le_of_tendsto_of_tendsto' hL hR hstep

/-! ## The varying-carrier convergence predicate -/

/-- `Hinf` on `E` is an **embedded vacuum-sector graph limit** of the varying
family `H n` on `F n` along the isometric embeddings `J n`: every domain vector
of `Hinf` orthogonal to the limit vacuum is the limit of the embedded images of
vacuum-orthogonal domain vectors of the cutoffs, together with their energies. -/
def IsEmbeddedVacuumGraphLimit (J : ∀ n, F n →ₗᵢ[ℂ] E) (H : ∀ n, F n →ₗ.[ℂ] F n)
    (vacn : ∀ n, F n) (Hinf : E →ₗ.[ℂ] E) (vac : E) : Prop :=
  ∀ ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
    ∃ (a : ∀ n, F n) (ha : ∀ n, a n ∈ (H n).domain),
      (∀ n, ⟪vacn n, a n⟫_ℂ = 0) ∧
        Tendsto (fun n => J n (a n)) atTop (𝓝 (ψ : E)) ∧
        Tendsto (fun n => J n ((H n) ⟨a n, ha n⟩)) atTop (𝓝 (Hinf ψ))

/-- **The limit Hamiltonian on the common carrier inherits the uniform gap.** -/
theorem hasVacuumFormGap_of_embeddedGraphLimit {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac Δ := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact formGap_le_of_embeddedGraphLimit hgap ha haorth hconv hopconv

/-- The drifting-constant version. -/
theorem hasVacuumFormGap_of_embeddedGraphLimit_tendsto {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E}
    {gapn : ℕ → ℝ} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) (gapn n))
    (hgaplim : Tendsto gapn atTop (𝓝 Δ))
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac Δ := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact formGap_le_of_embeddedGraphLimit_tendsto hgap hgaplim ha haorth hconv hopconv

/-! ## The continuum datum on the common carrier -/

section Continuum

variable [CompleteSpace E]

/-- **The continuum carrier from a varying-carrier cutoff family.**  Given a
uniform gap `Δ` on the cutoff spaces, isometric embeddings into `E`, an embedded
vacuum-sector graph limit, and self-adjointness of the limit operator with a
normalised zero-energy vacuum, the limit is a `VacuumGapDatum E` with gap `Δ`. -/
def embeddedContinuumDatum {J : ∀ n, F n →ₗᵢ[ℂ] E} {H : ∀ n, F n →ₗ.[ℂ] F n}
    {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
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
  form_gap := hasVacuumFormGap_of_embeddedGraphLimit hgap hlim

@[simp] theorem embeddedContinuumDatum_op {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).op = Hinf := rfl

@[simp] theorem embeddedContinuumDatum_vac {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).vac = vac := rfl

@[simp] theorem embeddedContinuumDatum_gap {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).gap = Δ := rfl

/-- **No spectral pollution in the varying-carrier continuum limit.**  For every
real `lam < Δ` and every `y ⊥ vac`, the equation `Hψ - lam ψ = y` has a unique
vacuum-orthogonal solution in the domain of the limit Hamiltonian. -/
theorem embedded_no_spectrum_below_gap {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} (hlt : lam < Δ) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      Hinf ψ - (lam : ℂ) • (ψ : E) = y :=
  (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).exists_unique_solution_vacuumSector
    hlt hy

/-- The quantitative resolvent bound in the varying-carrier limit. -/
theorem embedded_resolvent_bound {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} (hlt : lam < Δ) {ψ : Hinf.domain} (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ (Δ - lam)⁻¹ * ‖Hinf ψ - (lam : ℂ) • (ψ : E)‖ :=
  (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).resolvent_bound_vacuumSector
    hlt hψorth rfl

/-- Any excited state of the limit Hamiltonian orthogonal to the vacuum has
energy at least `Δ`. -/
theorem embedded_no_eigenvalue_below_gap {J : ∀ n, F n →ₗᵢ[ℂ] E}
    {H : ∀ n, F n →ₗ.[ℂ] F n} {vacn : ∀ n, F n} {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {lam : ℝ} {ψ : Hinf.domain} (hne : (ψ : E) ≠ 0)
    (heig : Hinf ψ = (lam : ℂ) • (ψ : E)) (hlt : lam < Δ) :
    lam = 0 :=
  (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ).eigenvalue_eq_zero_of_lt_gap
    hne heig hlt

end Continuum

/-! ## The fixed-carrier theory as a special case -/

/-- With `F n = E` and `J n` the identity isometry, the varying-carrier
predicate is exactly the fixed-carrier predicate of `ContinuumGapTransport`. -/
theorem isEmbeddedVacuumGraphLimit_of_isVacuumGraphLimit {H : ℕ → E →ₗ.[ℂ] E}
    {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E} {vac : E}
    (hlim : ContinuumGapTransport.IsVacuumGraphLimit H vacn Hinf vac) :
    IsEmbeddedVacuumGraphLimit (F := fun _ => E) (fun _ => LinearIsometry.id) H vacn
      Hinf vac := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact ⟨a, ha, haorth, by simpa using hconv, by simpa using hopconv⟩

/-- Conversely, an embedded graph limit along the identity embeddings is a
fixed-carrier graph limit, so the two predicates agree in that case. -/
theorem isVacuumGraphLimit_of_isEmbeddedVacuumGraphLimit {H : ℕ → E →ₗ.[ℂ] E}
    {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E} {vac : E}
    (hlim : IsEmbeddedVacuumGraphLimit (F := fun _ => E) (fun _ => LinearIsometry.id) H vacn
      Hinf vac) :
    ContinuumGapTransport.IsVacuumGraphLimit H vacn Hinf vac := by
  intro ψ hψ
  obtain ⟨a, ha, haorth, hconv, hopconv⟩ := hlim ψ hψ
  exact ⟨a, ha, haorth, by simpa using hconv, by simpa using hopconv⟩

/-- **The fixed-carrier transport theorem is the special case `J = id`.**  This
is the compatibility statement between the two convergence frameworks: the
varying-carrier theorem re-proves the theorem that `ContinuumGapTransport`
states, so nothing is lost in passing to the general setting. -/
theorem hasVacuumFormGap_of_graphLimit_of_embedded {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : ContinuumGapTransport.IsVacuumGraphLimit H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac Δ :=
  hasVacuumFormGap_of_embeddedGraphLimit (J := fun _ => LinearIsometry.id) hgap
    (isEmbeddedVacuumGraphLimit_of_isVacuumGraphLimit hlim)

/-! ## Carriers that genuinely depend on the cutoff: closed subspaces -/

section Subspace

/-- Cutoff carriers presented as closed subspaces `K n ⊆ E`, embedded by
inclusion.  The carrier type `↥(K n)` depends on `n`, so this is a genuine
instance of the varying-carrier framework, not the fixed-carrier one in
disguise. -/
noncomputable def subtypeEmbedding (K : ℕ → Submodule ℂ E) (n : ℕ) : ↥(K n) →ₗᵢ[ℂ] E :=
  (K n).subtypeₗᵢ

@[simp] theorem subtypeEmbedding_apply (K : ℕ → Submodule ℂ E) (n : ℕ) (x : ↥(K n)) :
    subtypeEmbedding K n x = (x : E) := rfl

/-- The subspace-carrier convergence hypothesis, written out: approximants
`a n ∈ D(H n) ⊆ K n`, orthogonal to the cutoff vacua, whose inclusions into `E`
converge together with their energies. -/
theorem isEmbeddedVacuumGraphLimit_subtype {K : ℕ → Submodule ℂ E}
    {H : ∀ n, ↥(K n) →ₗ.[ℂ] ↥(K n)} {vacn : ∀ n, ↥(K n)} {Hinf : E →ₗ.[ℂ] E} {vac : E}
    (h : ∀ ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
      ∃ (a : ∀ n, ↥(K n)) (ha : ∀ n, a n ∈ (H n).domain),
        (∀ n, ⟪vacn n, a n⟫_ℂ = 0) ∧
          Tendsto (fun n => ((a n : E))) atTop (𝓝 (ψ : E)) ∧
          Tendsto (fun n => (((H n) ⟨a n, ha n⟩ : ↥(K n)) : E)) atTop (𝓝 (Hinf ψ))) :
    IsEmbeddedVacuumGraphLimit (subtypeEmbedding K) H vacn Hinf vac := h

/-- **The subspace-carrier continuum datum.**  A uniform gap on a family of
closed-subspace carriers, plus convergence of the inclusions in the graph sense,
gives the full vacuum gap datum on `E`. -/
noncomputable def embeddedContinuumDatum_subtype [CompleteSpace E] {K : ℕ → Submodule ℂ E}
    {H : ∀ n, ↥(K n) →ₗ.[ℂ] ↥(K n)} {vacn : ∀ n, ↥(K n)} {Hinf : E →ₗ.[ℂ] E} {vac : E}
    {Δ : ℝ} (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit (subtypeEmbedding K) H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ) :
    VacuumGapDatum E :=
  embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ

end Subspace

/-! ## Non-vacuity with carriers of a genuinely different type -/

section VaryingWitness

/-- The cutoff carrier used by the witness: the subtype of the top submodule of
`E`.  It is isometrically isomorphic to `E` but is a *different type*, so the
following statements genuinely exercise the varying-carrier machinery rather
than the fixed-carrier one. -/
abbrev TopCarrier (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Type _ :=
  ↥(⊤ : Submodule ℂ E)

/-- The vacuum of the witness family, living on the cutoff carrier. -/
def topVacuum (vac : E) : TopCarrier E := ⟨vac, Submodule.mem_top⟩

@[simp] theorem topVacuum_coe (vac : E) : ((topVacuum vac : TopCarrier E) : E) = vac := rfl

/-- **The witness is an embedded vacuum-sector graph limit.**  The projection
Hamiltonians on the cutoff carriers, embedded by inclusion, converge in the
vacuum-sector graph sense to the projection Hamiltonian on `E`. -/
theorem isEmbeddedVacuumGraphLimit_topCarrier (vac : E) (Δ : ℝ) :
    IsEmbeddedVacuumGraphLimit (F := fun _ : ℕ => TopCarrier E)
      (fun _ => (⊤ : Submodule ℂ E).subtypeₗᵢ)
      (fun _ => projHam (topVacuum vac) Δ) (fun _ => topVacuum vac)
      (projHam vac Δ) vac := by
  intro ψ hψ
  refine ⟨fun _ => ⟨(ψ : E), Submodule.mem_top⟩, fun _ => Submodule.mem_top,
    fun _ => ?_, tendsto_const_nhds, ?_⟩
  · show ⟪topVacuum vac, (⟨(ψ : E), Submodule.mem_top⟩ : TopCarrier E)⟫_ℂ = 0
    simpa using hψ
  · have hcut : ∀ _ : ℕ, ((projHam (topVacuum vac) Δ)
        ⟨(⟨(ψ : E), Submodule.mem_top⟩ : TopCarrier E), Submodule.mem_top⟩ : TopCarrier E)
        = (Δ : ℂ) • (⟨(ψ : E), Submodule.mem_top⟩ : TopCarrier E) := by
      intro _
      refine projHam_apply_of_orthogonal _ ?_
      simpa using hψ
    rw [projHam_apply_of_orthogonal ψ hψ]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [hcut n]
    rfl

/-- **The varying-carrier transport is inhabited.**  Running the uniform gap of
the cutoff carriers through `hasVacuumFormGap_of_embeddedGraphLimit` returns the
gap of the limit operator, so the hypotheses of the transport theorems are
simultaneously satisfiable with carriers whose type depends on the cutoff. -/
theorem hasVacuumFormGap_of_topCarrier_limit (vac : E) (Δ : ℝ) :
    HasVacuumFormGap (projHam vac Δ) vac Δ :=
  hasVacuumFormGap_of_embeddedGraphLimit (F := fun _ : ℕ => TopCarrier E)
    (J := fun _ => (⊤ : Submodule ℂ E).subtypeₗᵢ)
    (fun _ => hasVacuumFormGap_projHam (topVacuum vac) Δ)
    (isEmbeddedVacuumGraphLimit_topCarrier vac Δ)

end VaryingWitness

/-! ## Axiom audit -/

section Audit

#print axioms formGap_le_of_embeddedGraphLimit
#print axioms formGap_le_of_embeddedGraphLimit_tendsto
#print axioms hasVacuumFormGap_of_embeddedGraphLimit
#print axioms hasVacuumFormGap_of_embeddedGraphLimit_tendsto
#print axioms embedded_no_spectrum_below_gap
#print axioms embedded_resolvent_bound
#print axioms embedded_no_eigenvalue_below_gap
#print axioms isEmbeddedVacuumGraphLimit_of_isVacuumGraphLimit
#print axioms isVacuumGraphLimit_of_isEmbeddedVacuumGraphLimit
#print axioms hasVacuumFormGap_of_graphLimit_of_embedded
#print axioms isEmbeddedVacuumGraphLimit_subtype
#print axioms isEmbeddedVacuumGraphLimit_topCarrier
#print axioms hasVacuumFormGap_of_topCarrier_limit

end Audit

end RequestProject.YangMills.VaryingCarrierTransport
