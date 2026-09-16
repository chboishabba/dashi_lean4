/-
# No spectrum below the gap, for an *unbounded* self-adjoint Hamiltonian

`FormGapSpectralExclusion` upgrades a quadratic-form lower bound to a spectral
statement for **bounded** operators.  This module does the same for a genuinely
unbounded operator `H : D(H) ⊆ E → E`, which is the situation of a physical
Hamiltonian:

if `H` is self-adjoint (Mathlib's `IsSelfAdjoint` for `LinearPMap`, i.e.
`H† = H`) and its quadratic form obeys `Δ‖ψ‖² ≤ re ⟪ψ, Hψ⟫` on its domain, then
for every real `lam < Δ` the operator `H - lam` maps `D(H)` **bijectively** onto
`E`, with the resolvent bound `‖ψ‖ ≤ (Δ - lam)⁻¹‖y‖`.  That is exactly the
statement that `lam` lies in the resolvent set: there is no spectrum below the
form gap, and in particular no eigenvalue below it.

Main results:

* `norm_sub_smul_lower_bound` — `(Δ - lam)‖ψ‖ ≤ ‖Hψ - lam ψ‖` on the domain;
* `mem_domain_of_orthogonal_range` — a vector orthogonal to the range of
  `H - lam` lies in the domain and is an eigenvector, by self-adjointness;
* `exists_unique_solution_of_formGap` — solvability and uniqueness;
* `resolvent_bound_of_formGap` — the quantitative resolvent bound;
* `no_eigenvalue_below_gap` — no eigenvalue strictly below `Δ` (this one needs
  no self-adjointness).

Nothing here constructs a physical Hamiltonian: `H`, its self-adjointness and
the form bound are hypotheses.  What is removed is the need for any further
generic operator theory between "self-adjoint `H` with a uniform form gap" and
"no spectrum below the gap".
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain

namespace RequestProject.YangMills.UnboundedFormGapResolvent

open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Two computations with the real shift -/

theorem re_inner_smul_self (lam : ℝ) (x : E) :
    (⟪x, (lam : ℂ) • x⟫_ℂ).re = lam * ‖x‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem re_inner_sub_smul (lam : ℝ) (x y : E) :
    (⟪x, y - (lam : ℂ) • x⟫_ℂ).re = (⟪x, y⟫_ℂ).re - lam * ‖x‖ ^ 2 := by
  rw [inner_sub_right, Complex.sub_re, re_inner_smul_self]

/-- The form gap of an unbounded operator, as used here. -/
def HasFormLowerBound (H : E →ₗ.[ℂ] E) (Δ : ℝ) : Prop :=
  ∀ ψ : H.domain, Δ * ‖(ψ : E)‖ ^ 2 ≤ (⟪(ψ : E), H ψ⟫_ℂ).re

/-- **Coercivity below the gap.**  For real `lam < Δ`, the shifted operator is
bounded below on the domain. -/
theorem norm_sub_smul_lower_bound {H : E →ₗ.[ℂ] E} {Δ : ℝ}
    (hgap : HasFormLowerBound H Δ) {lam : ℝ} (ψ : H.domain) :
    (Δ - lam) * ‖(ψ : E)‖ ≤ ‖H ψ - (lam : ℂ) • (ψ : E)‖ := by
  have hlow : (Δ - lam) * ‖(ψ : E)‖ ^ 2
      ≤ (⟪(ψ : E), H ψ - (lam : ℂ) • (ψ : E)⟫_ℂ).re := by
    rw [re_inner_sub_smul]
    nlinarith [hgap ψ]
  have hcs : (⟪(ψ : E), H ψ - (lam : ℂ) • (ψ : E)⟫_ℂ).re
      ≤ ‖(ψ : E)‖ * ‖H ψ - (lam : ℂ) • (ψ : E)‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (ψ : E)) with hn | hn
  · rw [← hn]
    simp
  · have h2 : (Δ - lam) * ‖(ψ : E)‖ * ‖(ψ : E)‖
        ≤ ‖H ψ - (lam : ℂ) • (ψ : E)‖ * ‖(ψ : E)‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hn

/-- **No eigenvalue below the gap.**  A form lower bound `Δ` forbids
eigenvalues `lam < Δ`; no self-adjointness is needed. -/
theorem no_eigenvalue_below_gap {H : E →ₗ.[ℂ] E} {Δ : ℝ}
    (hgap : HasFormLowerBound H Δ) {lam : ℝ} {ψ : H.domain} (hne : (ψ : E) ≠ 0)
    (heig : H ψ = (lam : ℂ) • (ψ : E)) : Δ ≤ lam := by
  have hform := hgap ψ
  rw [heig, re_inner_smul_self] at hform
  have hpos : 0 < ‖(ψ : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  nlinarith

section SelfAdjoint

variable [CompleteSpace E]

/-- A vector orthogonal to the range of `H - lam` is, by self-adjointness, an
element of the domain with `Hx = lam x`. -/
theorem mem_domain_of_orthogonal_range {H : E →ₗ.[ℂ] E} (hsa : IsSelfAdjoint H)
    {lam : ℝ} {x : E}
    (hx : ∀ ψ : H.domain, ⟪H ψ - (lam : ℂ) • (ψ : E), x⟫_ℂ = 0) :
    ∃ hxd : x ∈ H.domain, H ⟨x, hxd⟩ = (lam : ℂ) • x := by
  have hdense : Dense (H.domain : Set E) := hsa.dense_domain
  have hforall : ∀ ψ : H.domain, ⟪(lam : ℂ) • x, (ψ : E)⟫_ℂ = ⟪x, H ψ⟫_ℂ := by
    intro ψ
    have h0 := hx ψ
    rw [inner_sub_left, sub_eq_zero] at h0
    have h2 : ⟪x, H ψ⟫_ℂ = ⟪x, (lam : ℂ) • (ψ : E)⟫_ℂ := by
      rw [← inner_conj_symm, h0, inner_conj_symm]
    rw [h2, inner_smul_right, inner_smul_left]
    simp
  have hmem : x ∈ (LinearPMap.adjoint H).domain :=
    LinearPMap.mem_adjoint_domain_of_exists x ⟨(lam : ℂ) • x, hforall⟩
  have hHH : LinearPMap.adjoint H = H := LinearPMap.isSelfAdjoint_def.mp hsa
  have hxd : x ∈ H.domain := by rw [← hHH]; exact hmem
  refine ⟨hxd, ?_⟩
  have hadj : LinearPMap.adjoint H ⟨x, hmem⟩ = (lam : ℂ) • x :=
    LinearPMap.adjoint_apply_eq hdense ⟨x, hmem⟩ hforall
  have hcongr := (LinearPMap.ext_iff.mp hHH).2 (x := x) (hf := hmem) (hg := hxd)
  rw [← hcongr, hadj]

/-- **Solvability below the gap.**  For real `lam < Δ`, every `y` is
`H ψ - lam ψ` for a unique `ψ` in the domain: `lam` is in the resolvent set. -/
theorem exists_unique_solution_of_formGap {H : E →ₗ.[ℂ] E} (hsa : IsSelfAdjoint H)
    {Δ : ℝ} (hgap : HasFormLowerBound H Δ) {lam : ℝ} (hlt : lam < Δ) (y : E) :
    ∃! ψ : H.domain, H ψ - (lam : ℂ) • (ψ : E) = y := by
  classical
  have hcpos : 0 < Δ - lam := by linarith
  -- the shifted operator as a genuine linear map on the domain
  set A : H.domain →ₗ[ℂ] E := H.toFun - (lam : ℂ) • H.domain.subtype with hA
  have hAapp : ∀ ψ : H.domain, A ψ = H ψ - (lam : ℂ) • (ψ : E) := fun ψ => rfl
  have hAlb : ∀ ψ : H.domain, (Δ - lam) * ‖(ψ : E)‖ ≤ ‖A ψ‖ := by
    intro ψ; rw [hAapp]; exact norm_sub_smul_lower_bound hgap ψ
  set R : Submodule ℂ E := LinearMap.range A with hR
  -- the range is closed
  have hclosed : IsClosed (R : Set E) := by
    rw [← isSeqClosed_iff_isClosed]
    intro zn z hzn hlim
    choose ψ hψ using fun n => LinearMap.mem_range.mp (hzn n)
    have hCauchy : CauchySeq (fun n => ((ψ n : E))) := by
      have hconv : CauchySeq zn := hlim.cauchySeq
      rw [Metric.cauchySeq_iff] at hconv ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hconv ((Δ - lam) * ε) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hd := hN m hm n hn
      have hsub : A (ψ m - ψ n) = zn m - zn n := by
        rw [map_sub, hψ m, hψ n]
      have hlb := hAlb (ψ m - ψ n)
      rw [hsub] at hlb
      have hnormsub : ‖((ψ m - ψ n : H.domain) : E)‖ = dist ((ψ m : E)) ((ψ n : E)) := by
        rw [dist_eq_norm]
        rfl
      rw [hnormsub, ← dist_eq_norm] at hlb
      have hchain : (Δ - lam) * dist ((ψ m : E)) ((ψ n : E)) < (Δ - lam) * ε :=
        lt_of_le_of_lt hlb hd
      exact lt_of_mul_lt_mul_left hchain (le_of_lt hcpos)
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hHconv : Tendsto (fun n => H (ψ n)) atTop (𝓝 (z + (lam : ℂ) • w)) := by
      have hrew : ∀ n, H (ψ n) = zn n + (lam : ℂ) • ((ψ n : E)) := by
        intro n
        have := hψ n
        rw [hAapp] at this
        rw [← this]
        abel
      simp only [hrew]
      exact hlim.add (((continuous_const_smul ((lam : ℂ))).tendsto w).comp hw)
    have hgraph : (w, z + (lam : ℂ) • w) ∈ (H.graph : Set (E × E)) := by
      refine (hsa.isClosed : IsClosed (H.graph : Set (E × E))).mem_of_tendsto
        (f := fun n => (((ψ n : E)), H (ψ n))) (Tendsto.prodMk_nhds hw hHconv) ?_
      exact Filter.Eventually.of_forall (fun n => H.mem_graph (ψ n))
    obtain ⟨φ, hφ1, hφ2⟩ := (H.mem_graph_iff).mp hgraph
    refine LinearMap.mem_range.mpr ⟨φ, ?_⟩
    rw [hAapp, hφ2, hφ1]
    module
  -- the range is dense
  have hperp : (Rᗮ : Submodule ℂ E) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxperp : ∀ ψ : H.domain, ⟪H ψ - (lam : ℂ) • (ψ : E), x⟫_ℂ = 0 := by
      intro ψ
      exact hx _ (LinearMap.mem_range.mpr ⟨ψ, (hAapp ψ)⟩)
    obtain ⟨hxd, hxeq⟩ := mem_domain_of_orthogonal_range hsa hxperp
    have hform := hgap ⟨x, hxd⟩
    rw [hxeq, re_inner_smul_self] at hform
    have hn2 : ‖x‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hn2)
  have hRtop : R = ⊤ := by
    haveI := hclosed.completeSpace_coe
    rw [← R.orthogonal_orthogonal, hperp]
    simp
  -- existence and uniqueness
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp (by rw [hRtop]; trivial : y ∈ R)
  have hψ' : H ψ - (lam : ℂ) • (ψ : E) = y := by rw [← hAapp]; exact hψ
  refine ⟨ψ, hψ', ?_⟩
  intro φ hφ
  have hφ' : A φ = y := by rw [hAapp]; exact hφ
  have hzero : A (φ - ψ) = 0 := by rw [map_sub, hφ', hψ, sub_self]
  have hlb := hAlb (φ - ψ)
  rw [hzero] at hlb
  have hnorm : ‖((φ - ψ : H.domain) : E)‖ = 0 := by
    simp only [norm_zero] at hlb
    nlinarith [norm_nonneg (((φ - ψ : H.domain) : E))]
  have hsub : ((φ : E)) - ((ψ : E)) = 0 := by
    have : ((φ - ψ : H.domain) : E) = ((φ : E)) - ((ψ : E)) := rfl
    rw [← this]
    exact norm_eq_zero.mp hnorm
  exact Subtype.ext (sub_eq_zero.mp hsub)

/-! ### Non-vacuity: the hypotheses are simultaneously satisfiable -/

/-- A bounded self-adjoint operator, viewed as a partially defined operator on
the whole space, is self-adjoint in the `LinearPMap` sense. -/
theorem isSelfAdjoint_toPMap_top {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (LinearMap.toPMap (A : E →ₗ[ℂ] E) ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have h := ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (A := A) (p := (⊤ : Submodule ℂ E)) (by simp [dense_iff_closure_eq])
  rw [h, hA.adjoint_eq]

omit [CompleteSpace E] in
/-- The hypotheses of `exists_unique_solution_of_formGap` are not vacuous: the
operator `Δ • id`, viewed as a partially defined operator, is self-adjoint and
has form lower bound `Δ`. -/
theorem hasFormLowerBound_smul_id (Δ : ℝ) :
    HasFormLowerBound
      (LinearMap.toPMap (((Δ : ℂ) • ContinuousLinearMap.id ℂ E : E →L[ℂ] E) :
        E →ₗ[ℂ] E) ⊤) Δ := by
  intro ψ
  have hval : (LinearMap.toPMap (((Δ : ℂ) • ContinuousLinearMap.id ℂ E : E →L[ℂ] E) :
      E →ₗ[ℂ] E) ⊤) ψ = (Δ : ℂ) • (ψ : E) := rfl
  rw [hval, re_inner_smul_self]

theorem isSelfAdjoint_smul_id (Δ : ℝ) :
    IsSelfAdjoint (LinearMap.toPMap (((Δ : ℂ) • ContinuousLinearMap.id ℂ E : E →L[ℂ] E) :
      E →ₗ[ℂ] E) ⊤) := by
  refine isSelfAdjoint_toPMap_top ?_
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪(Δ : ℂ) • x, y⟫_ℂ = ⟪x, (Δ : ℂ) • y⟫_ℂ
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

end SelfAdjoint

/-- **The resolvent bound.**  The solution of `Hψ - lam ψ = y` obeys
`‖ψ‖ ≤ (Δ - lam)⁻¹‖y‖`. -/
theorem resolvent_bound_of_formGap {H : E →ₗ.[ℂ] E} {Δ : ℝ}
    (hgap : HasFormLowerBound H Δ) {lam : ℝ} (hlt : lam < Δ) {y : E} {ψ : H.domain}
    (hψ : H ψ - (lam : ℂ) • (ψ : E) = y) : ‖(ψ : E)‖ ≤ (Δ - lam)⁻¹ * ‖y‖ := by
  have hlb := norm_sub_smul_lower_bound (lam := lam) hgap ψ
  rw [hψ] at hlb
  have hpos : 0 < Δ - lam := by linarith
  exact (le_inv_mul_iff₀ hpos).mpr hlb

end RequestProject.YangMills.UnboundedFormGapResolvent

#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.norm_sub_smul_lower_bound
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.no_eigenvalue_below_gap
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.mem_domain_of_orthogonal_range
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.exists_unique_solution_of_formGap
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.resolvent_bound_of_formGap
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.isSelfAdjoint_smul_id
#print axioms RequestProject.YangMills.UnboundedFormGapResolvent.hasFormLowerBound_smul_id
