/-
# A genuinely unbounded Hamiltonian witnessing the domain machinery

`UnboundedHamiltonianDomain` and `UnboundedFormGapTransport` state properties of
partially defined operators `H : D(H) ⊆ E → E`.  This module shows those
properties are *not vacuous* by exhibiting an operator that has all of them and
is genuinely unbounded — the number operator

  `N (Σ xᵢ eᵢ) = Σ i xᵢ eᵢ`

on the Hilbert space `ℓ²(ℕ)`, with domain the (dense) span of the standard unit
vectors:

* `dense_coreDomain` — the domain is dense, so the operator is densely defined;
* `numberPMap_isSymmetric` — it is symmetric on its domain;
* `numberPMap_not_bounded` — it is **not** bounded on its domain, so this is a
  real unbounded operator and not a bounded one in disguise;
* `numberPMap_isClosable`, `numberPMap_closure_isSymmetric` — hence closable,
  with a symmetric closure;
* `numberPMap_hasFormGap` — it has quadratic-form gap `1` above the "vacuum"
  `e₀`, so the unbounded gap notion of `UnboundedFormGapTransport` is inhabited
  by an operator with a *positive* gap.

This is a witness, nothing more: it is not a Yang–Mills Hamiltonian, and no
physical conclusion is drawn from it.  Its only role is to certify that the
domain-theoretic statements have models with the intended properties.
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain
import RequestProject.YangMills.UnboundedFormGapTransport

namespace RequestProject.YangMills.UnboundedHamiltonianWitness

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.UnboundedHamiltonianDomain
open RequestProject.YangMills.UnboundedFormGapTransport

/-! ### Two arithmetic helpers -/

theorem conj_mul_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  have h : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem conj_mul_natCast_re (n : ℕ) (z : ℂ) :
    ((starRingEnd ℂ) z * ((n : ℂ) * z)).re = (n : ℝ) * ‖z‖ ^ 2 := by
  have h : (starRingEnd ℂ) z * ((n : ℂ) * z) = (n : ℂ) * ((starRingEnd ℂ) z * z) := by
    ring
  rw [h, Complex.mul_re, conj_mul_re]
  simp

/-! ### The carrier and its finitely supported vectors -/

/-- The carrier: the Hilbert space `ℓ²(ℕ)` of square-summable complex
sequences. -/
abbrev Carrier := lp (fun _ : ℕ => ℂ) 2

/-- The standard unit vectors. -/
noncomputable def basisVec (i : ℕ) : Carrier := lp.single 2 i (1 : ℂ)

/-- Finitely supported sequences, viewed inside `ℓ²`. -/
noncomputable def iota : (ℕ →₀ ℂ) →ₗ[ℂ] Carrier := Finsupp.linearCombination ℂ basisVec

theorem iota_apply (x : ℕ →₀ ℂ) (i : ℕ) : (iota x) i = x i := by
  classical
  rw [iota, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum]
  simp only [Finset.sum_apply, basisVec]
  by_cases h : i ∈ x.support
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hni; exact absurd h hni
  · rw [Finset.sum_eq_zero]
    · simpa using (Finsupp.notMem_support_iff.mp h).symm
    · intro b hb
      have hbi : b ≠ i := fun hbi => h (hbi ▸ hb)
      simp [Ne.symm hbi]

theorem iota_injective : Function.Injective iota := by
  intro x y hxy
  ext i
  have := congrArg (fun f : Carrier => f i) hxy
  simpa [iota_apply] using this

theorem iota_single (i : ℕ) (c : ℂ) : iota (Finsupp.single i c) = c • basisVec i := by
  simp [iota, Finsupp.linearCombination_single]

/-- The domain of the number operator: the span of the unit vectors. -/
noncomputable def coreDomain : Submodule ℂ Carrier := LinearMap.range iota

theorem single_mem_coreDomain (i : ℕ) (c : ℂ) : lp.single 2 i c ∈ coreDomain := by
  refine ⟨Finsupp.single i c, ?_⟩
  rw [iota_single]
  ext j
  simp [basisVec, lp.single_apply, Pi.single_apply]

/-- **The domain is dense**: the operator below is densely defined. -/
theorem dense_coreDomain : Dense (coreDomain : Set Carrier) := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall (fun f => ?_)
  have hsum : HasSum (fun i : ℕ => lp.single 2 i (f i)) f :=
    lp.hasSum_single (by norm_num) f
  refine mem_closure_of_tendsto hsum ?_
  filter_upwards with s
  exact Submodule.sum_mem _ (fun i _ => single_mem_coreDomain i (f i))

/-! ### The number operator -/

/-- Multiplication of the `i`-th coefficient by `i`, on finitely supported
sequences. -/
noncomputable def numberFinsupp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ (fun i => (i : ℂ) • Finsupp.lsingle i)

theorem numberFinsupp_apply (x : ℕ →₀ ℂ) (j : ℕ) :
    (numberFinsupp x) j = (j : ℂ) * x j := by
  classical
  rw [numberFinsupp, Finsupp.lsum_apply]
  simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  by_cases h : j ∈ x.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro hni; exact absurd h hni
  · rw [Finset.sum_eq_zero]
    · simp [Finsupp.notMem_support_iff.mp h]
    · intro b hb
      have hbj : b ≠ j := fun hbj => h (hbj ▸ hb)
      simp [hbj]

/-- The number operator as a partially defined operator on `ℓ²(ℕ)`. -/
noncomputable def numberPMap : Carrier →ₗ.[ℂ] Carrier where
  domain := coreDomain
  toFun := (iota.comp numberFinsupp).comp
    ((LinearEquiv.ofInjective iota iota_injective).symm.toLinearMap)

@[simp] theorem numberPMap_domain : numberPMap.domain = coreDomain := rfl

theorem ofInjective_symm_iota (x : ℕ →₀ ℂ) (h : iota x ∈ LinearMap.range iota) :
    (LinearEquiv.ofInjective iota iota_injective).symm ⟨iota x, h⟩ = x := by
  apply (LinearEquiv.ofInjective iota iota_injective).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem numberPMap_apply (x : ℕ →₀ ℂ) (h : iota x ∈ numberPMap.domain) :
    numberPMap ⟨iota x, h⟩ = iota (numberFinsupp x) := by
  show iota (numberFinsupp ((LinearEquiv.ofInjective iota iota_injective).symm _)) = _
  rw [ofInjective_symm_iota x h]

/-! ### Inner products on the domain -/

theorem inner_iota (x y : ℕ →₀ ℂ) :
    ⟪iota x, iota y⟫_ℂ = ∑ i ∈ x.support, (starRingEnd ℂ) (x i) * y i := by
  classical
  rw [lp.inner_eq_tsum]
  have hterm : ∀ i : ℕ, ⟪(iota x) i, (iota y) i⟫_ℂ = (starRingEnd ℂ) (x i) * y i := by
    intro i; simp [iota_apply, RCLike.inner_apply, mul_comm]
  rw [tsum_congr hterm]
  refine tsum_eq_sum (fun i hi => ?_)
  simp [Finsupp.notMem_support_iff.mp hi]

theorem norm_sq_iota (x : ℕ →₀ ℂ) :
    ‖iota x‖ ^ 2 = ∑ i ∈ x.support, ‖x i‖ ^ 2 := by
  have h := inner_iota x x
  have hself : ⟪iota x, iota x⟫_ℂ = ((‖iota x‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K _
  have hre : ((‖iota x‖ : ℝ)) ^ 2 = (∑ i ∈ x.support, (starRingEnd ℂ) (x i) * x i).re := by
    rw [← h, hself]
    norm_cast
  rw [hre, Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => conj_mul_re (x i))

/-! ### The witness properties -/

/-- The number operator is symmetric on its domain. -/
theorem numberPMap_isSymmetric : IsSymmetric numberPMap := by
  classical
  rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩
  rw [numberPMap_apply x ⟨x, rfl⟩, numberPMap_apply y ⟨y, rfl⟩, inner_iota, inner_iota]
  have hsupp : (numberFinsupp x).support ⊆ x.support := by
    intro i hi
    by_contra hni
    rw [Finsupp.mem_support_iff, numberFinsupp_apply,
      Finsupp.notMem_support_iff.mp hni] at hi
    simp at hi
  have hshrink : ∑ i ∈ (numberFinsupp x).support, (starRingEnd ℂ) ((numberFinsupp x) i) * y i
      = ∑ i ∈ x.support, (starRingEnd ℂ) ((numberFinsupp x) i) * y i := by
    refine Finset.sum_subset hsupp (fun i _ hi => ?_)
    rw [Finsupp.notMem_support_iff.mp hi]
    simp
  rw [hshrink]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [numberFinsupp_apply, numberFinsupp_apply, map_mul, Complex.conj_natCast]
  ring

/-- **The number operator is genuinely unbounded on its domain.** -/
theorem numberPMap_not_bounded :
    ¬ ∃ C : ℝ, ∀ ψ : numberPMap.domain, ‖numberPMap ψ‖ ≤ C * ‖(ψ : Carrier)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right C 1) hn
  have hnC : C < (n : ℝ) := lt_of_le_of_lt (le_max_left C 1) hn
  have hnne : (n : ℂ) ≠ 0 := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hn1
    exact_mod_cast hn0
  have hmem : iota (Finsupp.single n 1) ∈ numberPMap.domain := ⟨_, rfl⟩
  have hval := hC ⟨iota (Finsupp.single n 1), hmem⟩
  have hnorm1 : ‖iota (Finsupp.single n (1 : ℂ))‖ ^ 2 = 1 := by
    rw [norm_sq_iota, Finsupp.support_single_ne_zero _ (by norm_num : (1 : ℂ) ≠ 0)]
    simp
  have hnorm1' : ‖iota (Finsupp.single n (1 : ℂ))‖ = 1 := by
    nlinarith [norm_nonneg (iota (Finsupp.single n (1 : ℂ))), hnorm1]
  have hnum : numberFinsupp (Finsupp.single n (1 : ℂ)) = Finsupp.single n (n : ℂ) := by
    ext j
    rw [numberFinsupp_apply]
    by_cases h : j = n <;> simp [h]
  have hnormN : ‖(numberPMap ⟨iota (Finsupp.single n 1), hmem⟩ : Carrier)‖ ^ 2
      = (n : ℝ) ^ 2 := by
    rw [numberPMap_apply _ hmem, hnum, norm_sq_iota,
      Finsupp.support_single_ne_zero _ hnne]
    simp
  have hnormN' : ‖(numberPMap ⟨iota (Finsupp.single n 1), hmem⟩ : Carrier)‖ = (n : ℝ) := by
    nlinarith [norm_nonneg ((numberPMap ⟨iota (Finsupp.single n 1), hmem⟩ : Carrier)),
      hnormN, Nat.cast_nonneg (α := ℝ) n]
  rw [hnormN', hnorm1', mul_one] at hval
  linarith

/-- Hence the number operator is closable. -/
theorem numberPMap_isClosable : numberPMap.IsClosable :=
  IsSymmetric.isClosable (by simpa using dense_coreDomain) numberPMap_isSymmetric

/-- And its closure is symmetric. -/
theorem numberPMap_closure_isSymmetric : IsSymmetric numberPMap.closure :=
  IsSymmetric.closure numberPMap_isClosable numberPMap_isSymmetric

/-- **A positive form gap above the vacuum `e₀`.**  Every state of the domain
orthogonal to `e₀` has energy at least `‖ψ‖²`. -/
theorem numberPMap_hasFormGap : HasFormGapOn numberPMap (basisVec 0) 1 := by
  classical
  rintro ⟨-, x, rfl⟩ hperp
  have hx0 : x 0 = 0 := by
    have h : ⟪iota x, basisVec 0⟫_ℂ = (starRingEnd ℂ) (x 0) := by
      rw [basisVec, lp.inner_single_right]
      simp [iota_apply]
    rw [h] at hperp
    simpa using congrArg (starRingEnd ℂ) hperp
  have hsupp0 : (0 : ℕ) ∉ x.support := by simp [Finsupp.mem_support_iff, hx0]
  rw [numberPMap_apply x ⟨x, rfl⟩, inner_iota, norm_sq_iota]
  have hre : (∑ i ∈ x.support, (starRingEnd ℂ) (x i) * (numberFinsupp x) i).re
      = ∑ i ∈ x.support, (i : ℝ) * ‖x i‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [numberFinsupp_apply]
    exact conj_mul_natCast_re i (x i)
  rw [hre, one_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi1 : 1 ≤ (i : ℝ) := by
    have hine : i ≠ 0 := fun h => hsupp0 (h ▸ hi)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hine
  nlinarith [sq_nonneg ‖x i‖, norm_nonneg (x i)]

end RequestProject.YangMills.UnboundedHamiltonianWitness

#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.dense_coreDomain
#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.numberPMap_isSymmetric
#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.numberPMap_not_bounded
#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.numberPMap_isClosable
#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.numberPMap_closure_isSymmetric
#print axioms RequestProject.YangMills.UnboundedHamiltonianWitness.numberPMap_hasFormGap
