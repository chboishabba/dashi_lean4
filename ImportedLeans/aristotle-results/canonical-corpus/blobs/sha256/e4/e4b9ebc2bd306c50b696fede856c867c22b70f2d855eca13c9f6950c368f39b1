import Mathlib
import Integration.Variation.Pairing

/-!
# A proper, dense admitted perturbation fibre

`Integration.Variation.Pairing` proves two sharp statements about when the
stress pairing separates tensors on an admitted perturbation fibre `K`:

* `separates_iff_eq_top` — for an orthogonally complemented `K`, separation
  forces `K = ⊤`;
* `separates_iff_dense` — over a complete space, separation holds exactly when
  `K` is dense.

The physically interesting configuration is the gap between the two: an admitted
fibre that is **not everything** — as a fibre of compactly supported
perturbations never is — and yet **dense**, so that separation still holds.
This file shows that configuration is not vacuous, by exhibiting it.

The witness is the fibre of *finitely supported* perturbations in a separable
Hilbert space: the linear span of a Hilbert basis indexed by `ℕ`.  It is dense
(`span_basis_dense`), it is a proper subspace (`span_basis_ne_top`, witnessed by
a geometric ℓ² vector whose expansion has infinite support), and the pairing
separates tensors on it (`basis_span_separates`).

`proper_dense_admitted_fibre_exists` packages this unconditionally for
`ℓ²(ℕ, ℝ)`.
-/

namespace Integration.Variation.DenseFibre

open scoped InnerProductSpace RealInnerProductSpace
open Integration.Variation.Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The linear span of a Hilbert basis is dense. -/
theorem span_basis_dense (b : HilbertBasis ℕ ℝ H) :
    Dense (Submodule.span ℝ (Set.range (b : ℕ → H)) : Set H) := by
  classical
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hle : (⨆ J : Finset ℕ, Submodule.span ℝ ((Finset.image (b : ℕ → H) J : Finset H) : Set H))
      ≤ Submodule.span ℝ (Set.range (b : ℕ → H)) := by
    refine iSup_le (fun J => Submodule.span_le.mpr ?_)
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmono := Submodule.topologicalClosure_mono hle
  rw [b.finite_spans_dense] at hmono
  exact top_le_iff.mp hmono

/-- An element of the algebraic span of a Hilbert basis has finitely supported
expansion coefficients. -/
theorem repr_finitely_supported (b : HilbertBasis ℕ ℝ H) :
    ∀ y ∈ Submodule.span ℝ (Set.range (b : ℕ → H)),
      ∃ s : Finset ℕ, ∀ n ∉ s, b.repr y n = 0 := by
  classical
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨{i}, fun n hn => ?_⟩
      have hne : n ≠ i := Finset.mem_singleton.not.mp hn
      rw [b.repr_self]
      simp [lp.single_apply, hne]
  | zero => exact ⟨∅, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, fun n hn => ?_⟩
      simp only [Finset.mem_union, not_or] at hn
      simp [hs n hn.1, ht n hn.2]
  | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨s, fun n hn => by simp [hs n hn]⟩

/-- The geometric sequence is square summable. -/
theorem memℓp_geometric : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
  apply memℓp_gen
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
  have hpow : ∀ n : ℕ, |(1 / 2 : ℝ) ^ n| ^ (2 : ℝ) = ((1 / 4 : ℝ)) ^ n := by
    intro n
    rw [abs_of_pos (by positivity), ← Real.rpow_natCast (1 / 2 : ℝ) n,
      ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num)]
    norm_num
  simp_rw [hpow]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- **The span of a Hilbert basis indexed by `ℕ` is a proper subspace.**  The
vector whose expansion coefficients are `2⁻ⁿ` lies in the space but not in the
algebraic span, because its support is infinite. -/
theorem span_basis_ne_top (b : HilbertBasis ℕ ℝ H) :
    Submodule.span ℝ (Set.range (b : ℕ → H)) ≠ ⊤ := by
  classical
  intro htop
  set g : lp (fun _ : ℕ => ℝ) 2 := ⟨fun n => (1 / 2 : ℝ) ^ n, memℓp_geometric⟩ with hg
  set x : H := b.repr.symm g with hx
  have hmem : x ∈ Submodule.span ℝ (Set.range (b : ℕ → H)) := by rw [htop]; trivial
  obtain ⟨s, hs⟩ := repr_finitely_supported b x hmem
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset s
  have hrepr : b.repr x = g := by rw [hx, LinearIsometryEquiv.apply_symm_apply]
  have h0 : ((1 : ℝ) / 2) ^ n = 0 := by
    have := hs n hn
    rwa [hrepr] at this
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- **The pairing separates tensors on the finitely supported fibre.**  Density
is enough, so the admitted fibre need not be everything. -/
theorem basis_span_separates (b : HilbertBasis ℕ ℝ H) (A B : H)
    (hAB : ∀ v ∈ Submodule.span ℝ (Set.range (b : ℕ → H)), pair A v = pair B v) : A = B :=
  eq_of_pair_eq_on_dense_submodule A B _ (span_basis_dense b) hAB

/-- **A proper, dense, separating admitted fibre exists.**  In `ℓ²(ℕ, ℝ)` the
finitely supported perturbations form an admitted fibre that is a proper
subspace and still separates tensors — exactly the configuration the QFT/GR
frontier needs, and the reason `separates_iff_dense` rather than
`separates_iff_eq_top` is the usable form of the separation hypothesis. -/
theorem proper_dense_admitted_fibre_exists :
    ∃ K : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2),
      Dense (K : Set (lp (fun _ : ℕ => ℝ) 2)) ∧ K ≠ ⊤ ∧
        ∀ A B : lp (fun _ : ℕ => ℝ) 2, (∀ v ∈ K, pair A v = pair B v) → A = B := by
  classical
  let b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2) := default
  exact ⟨Submodule.span ℝ (Set.range (b : ℕ → lp (fun _ : ℕ => ℝ) 2)),
    span_basis_dense b, span_basis_ne_top b, fun A B h => basis_span_separates b A B h⟩

end Integration.Variation.DenseFibre
