/-
# The vacuum sector: spectral gap above a zero-energy ground state

This module supplies the shared carrier that the Yang–Mills operator lane was
missing, and routes the existing unbounded-operator files through it.

The machinery already in this library (`UnboundedFormGapResolvent`,
`FormGapSpectralExclusion`) upgrades a quadratic-form lower bound
`Δ‖ψ‖² ≤ re ⟪ψ, Hψ⟫` to a spectral statement.  That hypothesis is **never
satisfied by a physical Hamiltonian with `Δ > 0`**: a physical Hamiltonian has a
vacuum `Ω` with `HΩ = 0`, so the form bound on the whole domain forces `Δ ≤ 0`.
The mass gap is a statement about the *orthogonal complement of the vacuum*.

This file closes that mismatch.  The carrier is `VacuumGapDatum`:

* a densely defined self-adjoint `H : D(H) ⊆ E → E`;
* a unit vacuum `Ω ∈ D(H)` with `HΩ = 0`;
* a gap `Δ > 0` with `Δ‖ψ‖² ≤ re ⟪ψ, Hψ⟫` **only** for `ψ ∈ D(H)` with `ψ ⊥ Ω`.

From that data the following are theorems here:

* `vacuumComplement_invariant` — `H` maps `D(H) ∩ Ω^⊥` into `Ω^⊥`
  (the vacuum sector is a reducing subspace), from symmetry and `HΩ = 0`;
* `domain_decomposition` — `D(H)` splits as `ℂΩ ⊕ (D(H) ∩ Ω^⊥)`;
* `eigenvalue_eq_zero_of_lt_gap` — an eigenvalue `< Δ` is forced to be `0`,
  with eigenvector proportional to the vacuum: **no excited state below the
  gap**;
* `hasFormLowerBound_zero` — `H ≥ 0` on all of `D(H)`;
* `exists_unique_solution_vacuumSector` — for real `lam < Δ` and any
  `y ⊥ Ω` there is a *unique* `ψ ∈ D(H)` with `ψ ⊥ Ω` and `Hψ - lam ψ = y`,
  i.e. `lam` is in the resolvent set of the reduced operator: **there is no
  spectrum in `[0, Δ)` on the vacuum complement**;
* `resolvent_bound_vacuumSector` — the quantitative bound
  `‖ψ‖ ≤ (Δ - lam)⁻¹‖y‖`.

`VacuumGapDatum.projectionWitness` inhabits the carrier in every Hilbert space
with a unit vector, so none of the above is vacuous.

Honest scope: `H`, its self-adjointness, the vacuum and the gap are *inputs*.
Nothing here constructs the Yang–Mills Hamiltonian.  What is removed is the gap
between "a physical Hamiltonian with a zero-energy vacuum and a form gap on the
vacuum complement" and "a genuine spectral gap", which was previously available
only in the physically unattainable whole-domain form.
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain
import RequestProject.YangMills.UnboundedFormGapResolvent

namespace RequestProject.YangMills.VacuumSectorSpectralGap

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.UnboundedFormGapResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## The form gap above a vacuum -/

/-- `H` has form gap `Δ` above `Ω`: the quadratic-form lower bound is imposed
only on the vectors of the domain orthogonal to `Ω`.  This is the physically
correct hypothesis; the whole-domain version is incompatible with `HΩ = 0`. -/
def HasVacuumFormGap (H : E →ₗ.[ℂ] E) (vac : E) (Δ : ℝ) : Prop :=
  ∀ ψ : H.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 → Δ * ‖(ψ : E)‖ ^ 2 ≤ (⟪(ψ : E), H ψ⟫_ℂ).re

/-- **The shared carrier.**  A self-adjoint Hamiltonian with a normalised
zero-energy vacuum and a positive form gap on the vacuum complement. -/
structure VacuumGapDatum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  /-- The Hamiltonian, as a densely defined unbounded operator. -/
  op : E →ₗ.[ℂ] E
  /-- The vacuum vector. -/
  vac : E
  /-- The mass gap. -/
  gap : ℝ
  /-- The vacuum lies in the domain of the Hamiltonian. -/
  vac_mem : vac ∈ op.domain
  /-- The vacuum is normalised. -/
  vac_unit : ‖vac‖ = 1
  /-- The vacuum has zero energy. -/
  vac_ground : op ⟨vac, vac_mem⟩ = 0
  /-- The Hamiltonian is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint op
  /-- The gap is positive. -/
  gap_pos : 0 < gap
  /-- The form gap holds on the vacuum complement. -/
  form_gap : HasVacuumFormGap op vac gap

namespace VacuumGapDatum

variable [CompleteSpace E] (D : VacuumGapDatum E)

/-! ### Symmetry -/

/-- A self-adjoint unbounded operator is symmetric on its domain. -/
theorem isSymmetric_of_isSelfAdjoint {H : E →ₗ.[ℂ] E} (hsa : IsSelfAdjoint H) :
    UnboundedHamiltonianDomain.IsSymmetric H := by
  intro x y
  have hdense : Dense (H.domain : Set E) := hsa.dense_domain
  have hHH : LinearPMap.adjoint H = H := LinearPMap.isSelfAdjoint_def.mp hsa
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := H) hdense
  have hxmem : (x : E) ∈ (LinearPMap.adjoint H).domain := by rw [hHH]; exact x.2
  have h := hfa ⟨(x : E), hxmem⟩ y
  have hcongr := (LinearPMap.ext_iff.mp hHH).2 (x := (x : E)) (hf := hxmem) (hg := x.2)
  rw [hcongr] at h
  simpa using h

/-- Symmetry of the carrier's Hamiltonian. -/
theorem inner_op_left (x y : D.op.domain) :
    ⟪D.op x, (y : E)⟫_ℂ = ⟪(x : E), D.op y⟫_ℂ :=
  isSymmetric_of_isSelfAdjoint D.selfAdjoint x y

/-! ### The vacuum sector is reducing -/

/-- **The vacuum complement is invariant.**  The image of the whole domain under
`H` is orthogonal to the vacuum: `⟪Ω, Hψ⟫ = ⟪HΩ, ψ⟫ = 0`.  In particular `H`
maps `D(H) ∩ Ω^⊥` into `Ω^⊥`, which is what makes "the Hamiltonian restricted to
the vacuum sector" meaningful.  This is pure symmetry plus `HΩ = 0`. -/
theorem vacuumComplement_invariant (ψ : D.op.domain) : ⟪D.vac, D.op ψ⟫_ℂ = 0 := by
  have h := D.inner_op_left ⟨D.vac, D.vac_mem⟩ ψ
  rw [D.vac_ground] at h
  simpa using h.symm

/-- The vacuum projection of a domain vector stays in the domain, and the
remainder is a domain vector orthogonal to the vacuum. -/
theorem domain_decomposition (ψ : D.op.domain) :
    ((ψ : E) - ⟪D.vac, (ψ : E)⟫_ℂ • D.vac) ∈ D.op.domain ∧
      ⟪D.vac, (ψ : E) - ⟪D.vac, (ψ : E)⟫_ℂ • D.vac⟫_ℂ = 0 := by
  refine ⟨D.op.domain.sub_mem ψ.2 (D.op.domain.smul_mem _ D.vac_mem), ?_⟩
  have hvv : ⟪D.vac, D.vac⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), D.vac_unit]
    norm_num
  rw [inner_sub_right, inner_smul_right, hvv, mul_one, sub_self]

/-- The image of the decomposition: `H` kills the vacuum component, so
`H ψ = H (ψ - ⟪Ω,ψ⟫ Ω)`. -/
theorem op_eq_op_vacuumPart (ψ : D.op.domain) :
    D.op ψ = D.op ⟨(ψ : E) - ⟪D.vac, (ψ : E)⟫_ℂ • D.vac,
      (D.domain_decomposition ψ).1⟩ := by
  have hsub : (⟨(ψ : E) - ⟪D.vac, (ψ : E)⟫_ℂ • D.vac, (D.domain_decomposition ψ).1⟩
      : D.op.domain)
      = ψ - ⟪D.vac, (ψ : E)⟫_ℂ • (⟨D.vac, D.vac_mem⟩ : D.op.domain) := by
    ext; simp
  rw [hsub, LinearPMap.map_sub, LinearPMap.map_smul, D.vac_ground, smul_zero, sub_zero]

/-! ### Positivity on the whole domain -/

/-- **`H ≥ 0`.**  The gap on the vacuum complement plus `HΩ = 0` gives
nonnegativity of the quadratic form on the entire domain. -/
theorem hasFormLowerBound_zero : HasFormLowerBound D.op 0 := by
  intro ψ
  set c : ℂ := ⟪D.vac, (ψ : E)⟫_ℂ with hc
  set ψ₀ : D.op.domain := ⟨(ψ : E) - c • D.vac, (D.domain_decomposition ψ).1⟩ with hψ₀
  have horth : ⟪D.vac, (ψ₀ : E)⟫_ℂ = 0 := (D.domain_decomposition ψ).2
  have hop : D.op ψ = D.op ψ₀ := D.op_eq_op_vacuumPart ψ
  have hinner : ⟪(ψ : E), D.op ψ⟫_ℂ = ⟪(ψ₀ : E), D.op ψ₀⟫_ℂ := by
    have hsplit : (ψ : E) = (ψ₀ : E) + c • D.vac := by simp [hψ₀]
    rw [hop, hsplit, inner_add_left, inner_smul_left]
    have hzero : ⟪D.vac, D.op ψ₀⟫_ℂ = 0 := D.vacuumComplement_invariant ψ₀
    rw [hzero, mul_zero, add_zero]
  rw [hinner]
  have := D.form_gap ψ₀ horth
  nlinarith [sq_nonneg ‖(ψ₀ : E)‖, D.gap_pos.le, norm_nonneg ((ψ₀ : E))]

/-! ### No excited state below the gap -/

/-- **No eigenvalue strictly between `0` and the gap.**  If `Hψ = lam ψ` with
`ψ ≠ 0` and `lam < Δ` real, then `lam = 0`.  Equivalently: every excited state
has energy at least `Δ`. -/
theorem eigenvalue_eq_zero_of_lt_gap {lam : ℝ} {ψ : D.op.domain}
    (hne : (ψ : E) ≠ 0) (heig : D.op ψ = (lam : ℂ) • (ψ : E)) (hlt : lam < D.gap) :
    lam = 0 := by
  by_contra hlam
  -- `ψ` is orthogonal to the vacuum, since the vacuum has eigenvalue `0 ≠ lam`.
  have horth : ⟪D.vac, (ψ : E)⟫_ℂ = 0 := by
    have h := D.inner_op_left ⟨D.vac, D.vac_mem⟩ ψ
    rw [D.vac_ground, heig, inner_smul_right] at h
    have h0 : (0 : ℂ) = (lam : ℂ) * ⟪D.vac, (ψ : E)⟫_ℂ := by simpa using h
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact absurd (by exact_mod_cast h1) hlam
    · exact h1
  have hform := D.form_gap ψ horth
  rw [heig, re_inner_smul_self] at hform
  have hpos : 0 < ‖(ψ : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  nlinarith

/-- **The eigenvector at the bottom is the vacuum.**  Together with
`eigenvalue_eq_zero_of_lt_gap`, an eigenvector with eigenvalue below the gap and
orthogonal to the vacuum must vanish. -/
theorem eq_zero_of_eigen_orthogonal_below_gap {lam : ℝ} {ψ : D.op.domain}
    (horth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) (heig : D.op ψ = (lam : ℂ) • (ψ : E))
    (hlt : lam < D.gap) : (ψ : E) = 0 := by
  by_contra hne
  have hform := D.form_gap ψ horth
  rw [heig, re_inner_smul_self] at hform
  have hpos : 0 < ‖(ψ : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  nlinarith

/-! ### Solvability in the vacuum sector -/

/-- Coercivity of `H - lam` on the vacuum complement. -/
theorem norm_sub_smul_lower_bound_vacuumSector (lam : ℝ) (ψ : D.op.domain)
    (horth : ⟪D.vac, (ψ : E)⟫_ℂ = 0) :
    (D.gap - lam) * ‖(ψ : E)‖ ≤ ‖D.op ψ - (lam : ℂ) • (ψ : E)‖ := by
  have hlow : (D.gap - lam) * ‖(ψ : E)‖ ^ 2
      ≤ (⟪(ψ : E), D.op ψ - (lam : ℂ) • (ψ : E)⟫_ℂ).re := by
    rw [re_inner_sub_smul]
    nlinarith [D.form_gap ψ horth]
  have hcs : (⟪(ψ : E), D.op ψ - (lam : ℂ) • (ψ : E)⟫_ℂ).re
      ≤ ‖(ψ : E)‖ * ‖D.op ψ - (lam : ℂ) • (ψ : E)‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (ψ : E)) with hn | hn
  · rw [← hn]; simp
  · have h2 : (D.gap - lam) * ‖(ψ : E)‖ * ‖(ψ : E)‖
        ≤ ‖D.op ψ - (lam : ℂ) • (ψ : E)‖ * ‖(ψ : E)‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hn

/-- The image of the vacuum sector under `H - lam`, as a submodule of `E`. -/
def sectorRange (D : VacuumGapDatum E) (lam : ℝ) : Submodule ℂ E where
  carrier := {z | ∃ ψ : D.op.domain, ⟪D.vac, (ψ : E)⟫_ℂ = 0 ∧
    D.op ψ - (lam : ℂ) • (ψ : E) = z}
  add_mem' := by
    rintro z w ⟨ψ, hψ, rfl⟩ ⟨φ, hφ, rfl⟩
    refine ⟨ψ + φ, ?_, ?_⟩
    · rw [show ((ψ + φ : D.op.domain) : E) = (ψ : E) + (φ : E) from rfl,
        inner_add_right, hψ, hφ, add_zero]
    · rw [LinearPMap.map_add,
        show ((ψ + φ : D.op.domain) : E) = (ψ : E) + (φ : E) from rfl]
      module
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c z ⟨ψ, hψ, rfl⟩
    refine ⟨c • ψ, ?_, ?_⟩
    · rw [show ((c • ψ : D.op.domain) : E) = c • (ψ : E) from rfl,
        inner_smul_right, hψ, mul_zero]
    · rw [LinearPMap.map_smul,
        show ((c • ψ : D.op.domain) : E) = c • (ψ : E) from rfl]
      module

theorem mem_sectorRange_iff {lam : ℝ} {z : E} :
    z ∈ D.sectorRange lam ↔ ∃ ψ : D.op.domain, ⟪D.vac, (ψ : E)⟫_ℂ = 0 ∧
      D.op ψ - (lam : ℂ) • (ψ : E) = z := Iff.rfl

/-- The sector range lies in the vacuum complement. -/
theorem sectorRange_orthogonal_vac {lam : ℝ} {z : E} (hz : z ∈ D.sectorRange lam) :
    ⟪D.vac, z⟫_ℂ = 0 := by
  obtain ⟨ψ, hψ, rfl⟩ := hz
  rw [inner_sub_right, inner_smul_right, hψ, mul_zero, sub_zero,
    D.vacuumComplement_invariant ψ]

/-- **The sector range is closed.**  This uses closedness of the graph of the
self-adjoint operator together with the coercivity bound. -/
theorem isClosed_sectorRange {lam : ℝ} (hlt : lam < D.gap) :
    IsClosed ((D.sectorRange lam : Submodule ℂ E) : Set E) := by
  have hcpos : 0 < D.gap - lam := by linarith
  rw [← isSeqClosed_iff_isClosed]
  intro zn z hzn hlim
  choose ψ hψorth hψeq using fun n => (D.mem_sectorRange_iff).mp (hzn n)
  -- the preimages form a Cauchy sequence
  have hCauchy : CauchySeq (fun n => ((ψ n : E))) := by
    have hconv : CauchySeq zn := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hconv ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hconv ((D.gap - lam) * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := hN m hm n hn
    have hsubmem : ⟪D.vac, ((ψ m - ψ n : D.op.domain) : E)⟫_ℂ = 0 := by
      rw [show ((ψ m - ψ n : D.op.domain) : E) = (ψ m : E) - (ψ n : E) from rfl,
        inner_sub_right, hψorth, hψorth, sub_zero]
    have hlb := D.norm_sub_smul_lower_bound_vacuumSector lam (ψ m - ψ n) hsubmem
    have hval : D.op (ψ m - ψ n) - (lam : ℂ) • ((ψ m - ψ n : D.op.domain) : E)
        = zn m - zn n := by
      rw [LinearPMap.map_sub,
        show ((ψ m - ψ n : D.op.domain) : E) = (ψ m : E) - (ψ n : E) from rfl,
        ← hψeq m, ← hψeq n]
      module
    rw [hval] at hlb
    have hnormsub : ‖((ψ m - ψ n : D.op.domain) : E)‖ = ‖(ψ m : E) - (ψ n : E)‖ := rfl
    rw [hnormsub] at hlb
    have hdd : ‖zn m - zn n‖ < (D.gap - lam) * ε := by
      rwa [← dist_eq_norm]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((ψ m : E) - (ψ n : E))]
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hCauchy
  -- the images converge as well
  have hopconv : Tendsto (fun n => D.op (ψ n)) atTop (𝓝 (z + (lam : ℂ) • u)) := by
    have h1 : Tendsto (fun n => (lam : ℂ) • ((ψ n : E))) atTop (𝓝 ((lam : ℂ) • u)) :=
      hu.const_smul _
    have h2 : Tendsto (fun n => zn n + (lam : ℂ) • ((ψ n : E))) atTop
        (𝓝 (z + (lam : ℂ) • u)) := hlim.add h1
    refine h2.congr (fun n => ?_)
    rw [← hψeq n]; module
  -- closedness of the graph of a self-adjoint operator
  have hclosed : D.op.IsClosed := D.selfAdjoint.isClosed
  have hgc : IsClosed ((D.op.graph : Submodule ℂ (E × E)) : Set (E × E)) := hclosed
  have hmem : (u, z + (lam : ℂ) • u) ∈ D.op.graph :=
    hgc.mem_of_tendsto (hu.prodMk_nhds hopconv)
      (Eventually.of_forall (fun n => D.op.mem_graph (ψ n)))
  obtain ⟨w, hw1, hw2⟩ := (D.op.mem_graph_iff).mp hmem
  simp only at hw1 hw2
  have umem : u ∈ D.op.domain := hw1 ▸ w.2
  have hueq : D.op ⟨u, umem⟩ = z + (lam : ℂ) • u := by
    rw [show (⟨u, umem⟩ : D.op.domain) = w from Subtype.ext hw1.symm]; exact hw2
  · refine (D.mem_sectorRange_iff).mpr ⟨⟨u, umem⟩, ?_, ?_⟩
    · have : Tendsto (fun n => ⟪D.vac, ((ψ n : E))⟫_ℂ) atTop (𝓝 (⟪D.vac, u⟫_ℂ)) :=
        (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
          (Tendsto.prodMk_nhds tendsto_const_nhds hu)
      have hzero : Tendsto (fun n => ⟪D.vac, ((ψ n : E))⟫_ℂ) atTop (𝓝 (0 : ℂ)) := by
        simp [hψorth]
      have := tendsto_nhds_unique this hzero
      exact this
    · rw [hueq]; module

/-- **Solvability in the vacuum sector.**  For real `lam < Δ` and any `y`
orthogonal to the vacuum there is a unique `ψ ∈ D(H)` orthogonal to the vacuum
with `Hψ - lam ψ = y`.  This is exactly "no spectrum below the gap on the
vacuum complement" — the mass-gap statement for a Hamiltonian with a
zero-energy ground state. -/
theorem exists_unique_solution_vacuumSector {lam : ℝ} (hlt : lam < D.gap)
    {y : E} (hy : ⟪D.vac, y⟫_ℂ = 0) :
    ∃! ψ : D.op.domain, ⟪D.vac, (ψ : E)⟫_ℂ = 0 ∧
      D.op ψ - (lam : ℂ) • (ψ : E) = y := by
  have hcpos : 0 < D.gap - lam := by linarith
  have hclosed := D.isClosed_sectorRange hlt
  -- The range is a complete, hence orthogonally complemented, submodule.
  haveI : CompleteSpace (D.sectorRange lam) := hclosed.completeSpace_coe
  -- the orthogonal remainder of `y`
  set p : E := (D.sectorRange lam).starProjection y with hp
  have hpmem : p ∈ D.sectorRange lam := (D.sectorRange lam).starProjection_apply_mem y
  set r : E := y - p with hr
  have hrperp : r ∈ (D.sectorRange lam)ᗮ := by
    exact (D.sectorRange lam).sub_starProjection_mem_orthogonal y
  -- `r` is orthogonal to the vacuum
  have hrvac : ⟪D.vac, r⟫_ℂ = 0 := by
    rw [hr, inner_sub_right, hy, D.sectorRange_orthogonal_vac hpmem, sub_zero]
  -- `r` is orthogonal to the range of `H - lam` on the *whole* domain
  have hfull : ∀ ψ : D.op.domain, ⟪D.op ψ - (lam : ℂ) • (ψ : E), r⟫_ℂ = 0 := by
    intro ψ
    set c : ℂ := ⟪D.vac, (ψ : E)⟫_ℂ with hc
    set ψ₀ : D.op.domain := ⟨(ψ : E) - c • D.vac, (D.domain_decomposition ψ).1⟩ with hψ₀
    have horth0 : ⟪D.vac, (ψ₀ : E)⟫_ℂ = 0 := (D.domain_decomposition ψ).2
    have hop : D.op ψ = D.op ψ₀ := D.op_eq_op_vacuumPart ψ
    have hdec : D.op ψ - (lam : ℂ) • (ψ : E)
        = (D.op ψ₀ - (lam : ℂ) • (ψ₀ : E)) - ((lam : ℂ) * c) • D.vac := by
      rw [hop]
      have : (ψ : E) = (ψ₀ : E) + c • D.vac := by simp [hψ₀]
      rw [this]; module
    rw [hdec, inner_sub_left]
    have h1 : ⟪D.op ψ₀ - (lam : ℂ) • (ψ₀ : E), r⟫_ℂ = 0 := by
      have hmem : D.op ψ₀ - (lam : ℂ) • (ψ₀ : E) ∈ D.sectorRange lam :=
        ⟨ψ₀, horth0, rfl⟩
      exact (Submodule.mem_orthogonal _ _).mp hrperp _ hmem
    have h2 : ⟪((lam : ℂ) * c) • D.vac, r⟫_ℂ = 0 := by
      rw [inner_smul_left]
      have : ⟪D.vac, r⟫_ℂ = 0 := hrvac
      simp [this]
    rw [h1, h2, sub_zero]
  -- hence `r` is in the domain and is an eigenvector below the gap: `r = 0`
  obtain ⟨hrd, hreig⟩ := mem_domain_of_orthogonal_range D.selfAdjoint hfull
  have hrzero : r = 0 :=
    D.eq_zero_of_eigen_orthogonal_below_gap (ψ := ⟨r, hrd⟩) hrvac hreig hlt
  have hyp : y ∈ D.sectorRange lam := by
    have : y = p := by rw [← sub_eq_zero]; exact hrzero
    rw [this]; exact hpmem
  obtain ⟨ψ, hψorth, hψeq⟩ := hyp
  refine ⟨ψ, ⟨hψorth, hψeq⟩, ?_⟩
  rintro φ ⟨hφorth, hφeq⟩
  -- uniqueness from coercivity
  have hsubmem : ⟪D.vac, ((φ - ψ : D.op.domain) : E)⟫_ℂ = 0 := by
    rw [show ((φ - ψ : D.op.domain) : E) = (φ : E) - (ψ : E) from rfl,
      inner_sub_right, hφorth, hψorth, sub_zero]
  have hlb := D.norm_sub_smul_lower_bound_vacuumSector lam (φ - ψ) hsubmem
  have hval : D.op (φ - ψ) - (lam : ℂ) • ((φ - ψ : D.op.domain) : E) = 0 := by
    rw [LinearPMap.map_sub, show ((φ - ψ : D.op.domain) : E) = (φ : E) - (ψ : E) from rfl]
    rw [show D.op φ - D.op ψ - (lam : ℂ) • ((φ : E) - (ψ : E))
        = (D.op φ - (lam : ℂ) • (φ : E)) - (D.op ψ - (lam : ℂ) • (ψ : E)) by module,
      hφeq, hψeq, sub_self]
  rw [hval, norm_zero] at hlb
  have hnz : ‖((φ - ψ : D.op.domain) : E)‖ = 0 := by
    have := norm_nonneg (((φ - ψ : D.op.domain) : E))
    nlinarith
  have : (φ : E) - (ψ : E) = 0 := by
    have h := norm_eq_zero.mp hnz
    simpa using h
  exact Subtype.ext (by linear_combination (norm := module) this)

/-- **The resolvent bound in the vacuum sector.** -/
theorem resolvent_bound_vacuumSector {lam : ℝ} (hlt : lam < D.gap)
    {y : E} {ψ : D.op.domain}
    (hψorth : ⟪D.vac, (ψ : E)⟫_ℂ = 0)
    (hψ : D.op ψ - (lam : ℂ) • (ψ : E) = y) :
    ‖(ψ : E)‖ ≤ (D.gap - lam)⁻¹ * ‖y‖ := by
  have hcpos : 0 < D.gap - lam := by linarith
  have hlb := D.norm_sub_smul_lower_bound_vacuumSector lam ψ hψorth
  rw [hψ] at hlb
  rw [inv_mul_eq_div, le_div_iff₀ hcpos]
  linarith [hlb]

end VacuumGapDatum

/-! ## Non-vacuity: the carrier is inhabited -/

section Witness

variable [CompleteSpace E]

/-- The **projection Hamiltonian** `c · P`, with `P` the orthogonal projection
onto the orthogonal complement of `ℂ·vac`, presented as an everywhere-defined
unbounded operator.  It is the canonical inhabitant of `VacuumGapDatum`: it
annihilates `vac` and multiplies the vacuum complement by `c`. -/
noncomputable def projHam (vac : E) (c : ℝ) : E →ₗ.[ℂ] E :=
  (((c : ℂ) • (ContinuousLinearMap.id ℂ E
    - (ℂ ∙ vac).starProjection)) : E →L[ℂ] E).toPMap ⊤

omit [CompleteSpace E] in
@[simp] theorem projHam_domain (vac : E) (c : ℝ) : (projHam vac c).domain = ⊤ := rfl

omit [CompleteSpace E] in
theorem projHam_apply (vac : E) (c : ℝ) (ψ : (projHam vac c).domain) :
    projHam vac c ψ = (c : ℂ) • ((ψ : E) - (ℂ ∙ vac).starProjection (ψ : E)) := by
  simp [projHam, LinearMap.toPMap_apply]

omit [CompleteSpace E] in
/-- On the vacuum complement the projection Hamiltonian is multiplication by `c`. -/
theorem projHam_apply_of_orthogonal {vac : E} {c : ℝ} (ψ : (projHam vac c).domain)
    (hψ : ⟪vac, (ψ : E)⟫_ℂ = 0) : projHam vac c ψ = (c : ℂ) • (ψ : E) := by
  have hψmem : (ψ : E) ∈ (ℂ ∙ vac)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, ← inner_conj_symm]
    simp [hψ]
  have hzero : (ℂ ∙ vac).starProjection (ψ : E) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]; exact hψmem
  rw [projHam_apply, hzero, sub_zero]

omit [CompleteSpace E] in
theorem projHam_vac (vac : E) (c : ℝ) :
    projHam vac c ⟨vac, Submodule.mem_top⟩ = 0 := by
  have hmem : vac ∈ (ℂ ∙ vac) := Submodule.mem_span_singleton_self vac
  rw [projHam_apply, Submodule.starProjection_eq_self_iff.mpr hmem, sub_self, smul_zero]

theorem isSelfAdjoint_projHam (vac : E) (c : ℝ) : IsSelfAdjoint (projHam vac c) := by
  have hproj : IsSelfAdjoint ((ℂ ∙ vac).starProjection) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hd : IsSelfAdjoint (ContinuousLinearMap.id ℂ E - (ℂ ∙ vac).starProjection) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.one (R := E →L[ℂ] E)) hproj
  have hsa : IsSelfAdjoint (((c : ℂ) • (ContinuousLinearMap.id ℂ E
      - (ℂ ∙ vac).starProjection)) : E →L[ℂ] E) := by
    refine IsSelfAdjoint.smul ?_ hd
    simp [isSelfAdjoint_iff, Complex.conj_ofReal]
  exact UnboundedFormGapResolvent.isSelfAdjoint_toPMap_top hsa

omit [CompleteSpace E] in
/-- The projection Hamiltonian has form gap exactly `c` above its vacuum. -/
theorem hasVacuumFormGap_projHam (vac : E) (c : ℝ) :
    HasVacuumFormGap (projHam vac c) vac c := by
  intro ψ hψ
  rw [projHam_apply_of_orthogonal ψ hψ, UnboundedFormGapResolvent.re_inner_smul_self]

/-- **A witness for the carrier.**  In any complex Hilbert space, a unit vector
`Ω` and a positive number `Δ` give a self-adjoint Hamiltonian `Δ · P`, with `P`
the orthogonal projection onto `Ω^⊥`, which has `Ω` as a zero-energy vacuum and
form gap exactly `Δ` on the vacuum complement.  So `VacuumGapDatum` is not
vacuous, and the gap value is not forced. -/
noncomputable def projectionWitness (vac : E) (hvac : ‖vac‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) :
    VacuumGapDatum E where
  op := projHam vac Δ
  vac := vac
  gap := Δ
  vac_mem := Submodule.mem_top
  vac_unit := hvac
  vac_ground := projHam_vac vac Δ
  selfAdjoint := isSelfAdjoint_projHam vac Δ
  gap_pos := hΔ
  form_gap := hasVacuumFormGap_projHam vac Δ

/-- The witness really does have the prescribed gap and vacuum. -/
theorem projectionWitness_gap (vac : E) (hvac : ‖vac‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) :
    (projectionWitness vac hvac hΔ).gap = Δ ∧
      (projectionWitness vac hvac hΔ).vac = vac := ⟨rfl, rfl⟩

end Witness

end RequestProject.YangMills.VacuumSectorSpectralGap

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.VacuumSectorSpectralGap

#print axioms VacuumGapDatum.isSymmetric_of_isSelfAdjoint
#print axioms VacuumGapDatum.vacuumComplement_invariant
#print axioms VacuumGapDatum.domain_decomposition
#print axioms VacuumGapDatum.op_eq_op_vacuumPart
#print axioms VacuumGapDatum.hasFormLowerBound_zero
#print axioms VacuumGapDatum.eigenvalue_eq_zero_of_lt_gap
#print axioms VacuumGapDatum.eq_zero_of_eigen_orthogonal_below_gap
#print axioms VacuumGapDatum.norm_sub_smul_lower_bound_vacuumSector
#print axioms VacuumGapDatum.sectorRange_orthogonal_vac
#print axioms VacuumGapDatum.isClosed_sectorRange
#print axioms VacuumGapDatum.exists_unique_solution_vacuumSector
#print axioms VacuumGapDatum.resolvent_bound_vacuumSector
#print axioms projHam_vac
#print axioms isSelfAdjoint_projHam
#print axioms hasVacuumFormGap_projHam
#print axioms projectionWitness_gap

end Audit
