/-
# The ternary phase core, done once

Part A is the exact `C₃` phase algebra over `ℂ`: `ζ³ = 1`, `ζ ≠ 1`,
`1 + ζ + ζ² = 0`, `ζ² = ζ⁻¹ = conj ζ`, the involution `ζ ↦ ζ²` fixing `1`, and
the character table of `C₃` as an actual matrix `F₃` satisfying the
orthogonality relation `F₃ · F₃ᴴ = 3 · I`.

Part B is the *realification*, which is the part that turns `3 = 1 + 2` from
arithmetic into representation theory.  On `EuclideanSpace ℝ (Fin 3)` with the
cyclic shift `σ` (the regular representation of `C₃`):

* a vector is fixed by `σ` exactly when it is constant — the fixed sector is the
  trivial character, one real dimension;
* the transverse sector is exactly the mean-zero vectors, and it is
  two-dimensional (`RealC3.finrank_transverse`);
* `σ` preserves it and has **no real eigenvector at all** inside it
  (`RealC3.no_real_eigenvector_transverse`), so the transverse sector is an
  irreducible real rotation plane, not two independent labelled lines.

Part C is the binary contrast.  On `ℝ[C₂]` the transverse sector is
one-dimensional and the generator acts on it by `-1`
(`RealC2.swap_eq_neg_on_transverse`): the nontrivial binary character is already
real, so there "label" and "real transverse dimension" coincide and can be
conflated.  In `C₃` they demonstrably come apart.  That is the precise content of
"the ternary case is the first one where the intuition is forced to become
precise".
-/
import Mathlib
import Spine.AnchoredGram

open Complex ComplexConjugate Matrix RealInnerProductSpace

namespace Spine

/-! ## Part A: the exact complex phase algebra -/

/-- A primitive cube root of unity, given explicitly. -/
noncomputable def zeta : ℂ := (-1 + Complex.I * (Real.sqrt 3)) / 2

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  norm_cast; rw [Real.sq_sqrt]; norm_num

theorem zeta_sq : zeta ^ 2 = (-1 - Complex.I * (Real.sqrt 3)) / 2 := by
  simp only [zeta]
  linear_combination (Complex.I ^ 2 / 4) * sqrt3_sq + (3 / 4) * Complex.I_sq

/-- `ζ³ = 1`. -/
theorem zeta_cube : zeta ^ 3 = 1 := by
  have h : zeta ^ 3 = zeta * zeta ^ 2 := by ring
  rw [h, zeta_sq]; simp only [zeta]
  linear_combination (-Complex.I ^ 2 / 4) * sqrt3_sq + (-3 / 4) * Complex.I_sq

/-- `ζ ≠ 1`: the root is primitive. -/
theorem zeta_ne_one : zeta ≠ 1 := by
  simp only [zeta, ne_eq, Complex.ext_iff]
  simp [Complex.add_re, Complex.add_im]

/-- `1 + ζ + ζ² = 0`: the three phases sum to zero.  This is the arithmetic
shadow of the splitting "constant mode ⊕ mean-zero modes". -/
theorem zeta_sum : 1 + zeta + zeta ^ 2 = 0 := by
  rw [zeta_sq]; simp only [zeta]; ring

theorem zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have h3 := zeta_cube
  rw [h] at h3; norm_num at h3

/-- `conj ζ = ζ²`. -/
theorem conj_zeta : conj zeta = zeta ^ 2 := by
  rw [zeta_sq]
  simp only [zeta, map_div₀, map_add, map_mul, map_neg, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

theorem zeta_pow_four : zeta ^ 4 = zeta := by
  calc zeta ^ 4 = zeta ^ 3 * zeta := by ring
  _ = zeta := by rw [zeta_cube]; ring

/-- `conj (ζ²) = ζ`: conjugation is the involution swapping the two nontrivial
phases, and it fixes the constant phase `1` (`map_one`). -/
theorem conj_zeta_sq : conj (zeta ^ 2) = zeta := by
  rw [map_pow, conj_zeta, ← pow_mul]
  calc zeta ^ (2 * 2) = zeta ^ 3 * zeta := by ring
  _ = zeta := by rw [zeta_cube]; ring

/-- `ζ⁻¹ = ζ²`, so inversion and conjugation are the same involution here. -/
theorem zeta_inv : zeta⁻¹ = zeta ^ 2 := by
  have h : zeta ^ 2 * zeta = 1 := by
    calc zeta ^ 2 * zeta = zeta ^ 3 := by ring
    _ = 1 := zeta_cube
  exact inv_eq_of_mul_eq_one_left h

/-- The involution fixes the constant phase. -/
theorem conj_one_eq_one : conj (1 : ℂ) = 1 := map_one _

/-- The character table of `C₃`, rows indexed by characters, columns by group
elements. -/
noncomputable def charMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, zeta, zeta ^ 2; 1, zeta ^ 2, zeta]

/-- **Character orthogonality for `C₃`**: `F₃ · F₃ᴴ = 3 · I`. -/
theorem charMatrix_orthogonality :
    charMatrix * charMatrixᴴ = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [charMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      conj_zeta, conj_zeta_sq] <;>
    ring_nf <;>
    first
      | exact zeta_sum
      | (rw [zeta_cube]; norm_num)
      | (rw [zeta_pow_four]; linear_combination zeta_sum)

/-- Consequently the finite Fourier transform on `C₃` is invertible. -/
theorem charMatrix_det_ne_zero : charMatrix.det ≠ 0 := by
  intro h
  have hcon := congrArg Matrix.det charMatrix_orthogonality
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one] at hcon
  norm_num at hcon

/-! ## Part B: realification, `ℝ[C₃] = ℝ_triv ⊕ ℝ²_rot` -/

namespace RealC3

/-- The carrier `ℝ[C₃]`, as a three-dimensional real inner product space. -/
abbrev V := EuclideanSpace ℝ (Fin 3)

/-- The regular action of the generator of `C₃`: cyclic shift of coordinates. -/
noncomputable def shift : V →ₗ[ℝ] V where
  toFun x := WithLp.toLp 2 (fun i => x (i + 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift_apply (x : V) (i : Fin 3) : shift x i = x (i + 1) := rfl

/-- The action has order three. -/
theorem shift_cube (x : V) : shift (shift (shift x)) = x := by
  ext i; fin_cases i <;> simp

/-- The shift is an isometry of the standard inner product, so the splitting
below is orthogonal. -/
theorem shift_inner (x y : V) : ⟪shift x, shift y⟫ = ⟪x, y⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- The linear functional whose kernel is the transverse sector. -/
def sumForm : V →ₗ[ℝ] ℝ where
  toFun x := x 0 + x 1 + x 2
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- The transverse sector: mean-zero vectors. -/
def transverse : Submodule ℝ V := LinearMap.ker sumForm

theorem mem_transverse_iff (x : V) : x ∈ transverse ↔ x 0 + x 1 + x 2 = 0 := Iff.rfl

/-- A vector is fixed by the shift exactly when it is constant: the fixed sector
is the trivial character. -/
theorem fixed_iff_constant (x : V) : shift x = x ↔ ∀ i j, x i = x j := by
  constructor
  · intro h i j
    have h0 : x 1 = x 0 := by simpa using congrArg (fun v : V => v 0) h
    have h1 : x 2 = x 1 := by simpa using congrArg (fun v : V => v 1) h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h; ext i; simpa using h (i + 1) i

/-- The shift preserves the transverse sector. -/
theorem shift_mem_transverse {x : V} (hx : x ∈ transverse) : shift x ∈ transverse := by
  rw [mem_transverse_iff] at hx ⊢
  have e0 : shift x 0 = x 1 := by simp
  have e1 : shift x 1 = x 2 := by simp
  have e2 : shift x 2 = x 0 := by simp
  rw [e0, e1, e2]; linarith

/-- **No invariant line.**  The shift has no real eigenvector inside the
transverse sector: for every nonzero mean-zero `x` and every real `c`,
`σ x ≠ c • x`.  Equivalently, the two nontrivial `C₃` characters realify to a
single irreducible two-dimensional rotation plane. -/
theorem no_real_eigenvector_transverse {x : V} (hx : x ∈ transverse) (hx0 : x ≠ 0) (c : ℝ) :
    shift x ≠ c • x := by
  intro h
  have e1 : shift (shift x) = c • (c • x) := by
    rw [show shift x = c • x from h, map_smul, h]
  have e2 : shift (shift (shift x)) = c • (c • (c • x)) := by
    rw [show shift (shift x) = c • (c • x) from e1, map_smul, map_smul, h]
  rw [shift_cube] at e2
  have hpow : c ^ 3 • x = c • c • c • x := by
    rw [smul_smul, smul_smul]; congr 1; ring
  have h3 : x = c ^ 3 • x := by rw [hpow]; exact e2
  have hc : c ^ 3 = 1 := by
    by_contra hne
    have hz : (c ^ 3 - 1) • x = 0 := by rw [sub_smul, one_smul, ← h3]; simp
    rcases smul_eq_zero.mp hz with h' | h'
    · exact hne (by linarith [sub_eq_zero.mp h'])
    · exact hx0 h'
  have hc1 : c = 1 := by nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg c]
  rw [hc1, one_smul] at h
  have hconst := (fixed_iff_constant x).mp h
  have hsum : x 0 + x 1 + x 2 = 0 := (mem_transverse_iff x).mp hx
  have hzero : x 0 = 0 := by
    have h1 : x 1 = x 0 := hconst 1 0
    have h2 : x 2 = x 0 := hconst 2 0
    rw [h1, h2] at hsum; linarith
  exact hx0 (by ext i; simpa [hzero] using hconst i 0)

/-- In particular the transverse sector contains no nonzero fixed vector: the
splitting `fixed ⊕ transverse` is a genuine direct sum. -/
theorem no_fixed_vector_transverse {x : V} (hx : x ∈ transverse) (hfix : shift x = x) :
    x = 0 := by
  by_contra hx0
  exact no_real_eigenvector_transverse hx hx0 1 (by simpa using hfix)

/-- The transverse sector is two-dimensional: this is the `2` of `3 = 1 + 2`. -/
theorem finrank_transverse : Module.finrank ℝ transverse = 2 := by
  have hsurj : Function.Surjective sumForm := by
    intro c
    exact ⟨WithLp.toLp 2 (fun i => if i = 0 then c else 0), by simp [sumForm]⟩
  have h := LinearMap.finrank_range_add_finrank_ker sumForm
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  simp at h
  simp only [transverse]
  omega

/-! ### The splitting as a literal internal direct sum -/

/-- The all-ones vector, spanning the trivial character. -/
noncomputable def onesV : V := WithLp.toLp 2 (fun _ => (1 : ℝ))

@[simp] theorem onesV_apply (i : Fin 3) : onesV i = 1 := rfl

/-- The fixed sector: the line of constant vectors. -/
noncomputable def fixedSub : Submodule ℝ V := Submodule.span ℝ {onesV}

theorem mem_fixedSub_iff (x : V) : x ∈ fixedSub ↔ ∀ i j, x i = x j := by
  rw [fixedSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩ i j; simp
  · intro h
    refine ⟨x 0, ?_⟩
    ext i; simpa using (h i 0).symm

/-- The fixed sector is exactly the set of `σ`-fixed vectors. -/
theorem mem_fixedSub_iff_shift (x : V) : x ∈ fixedSub ↔ shift x = x := by
  rw [mem_fixedSub_iff, fixed_iff_constant]

/-- The shift acts as the identity on the fixed sector. -/
theorem shift_on_fixedSub {x : V} (hx : x ∈ fixedSub) : shift x = x :=
  (mem_fixedSub_iff_shift x).mp hx

/-- The two sectors are orthogonal. -/
theorem inner_fixedSub_transverse {x y : V} (hx : x ∈ fixedSub) (hy : y ∈ transverse) :
    ⟪x, y⟫ = 0 := by
  have hc := (mem_fixedSub_iff x).mp hx
  have hs := (mem_transverse_iff y).mp hy
  have h1 : x 1 = x 0 := hc 1 0
  have h2 : x 2 = x 0 := hc 2 0
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  rw [h1, h2]
  linear_combination (x 0) * hs

/-- **`ℝ[C₃] = ℝ_triv ⊕ ℝ²`.**  The fixed line and the transverse plane are
complementary submodules of the carrier. -/
theorem isCompl_fixedSub_transverse : IsCompl fixedSub transverse := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hc := (mem_fixedSub_iff x).mp hx.1
    have hs := (mem_transverse_iff x).mp hx.2
    have h1 : x 1 = x 0 := hc 1 0
    have h2 : x 2 = x 0 := hc 2 0
    rw [h1, h2] at hs
    have hzero : x 0 = 0 := by linarith
    have hx0 : x = 0 := by ext i; simpa [hzero] using hc i 0
    simpa using hx0
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    set a : ℝ := (x 0 + x 1 + x 2) / 3 with ha
    refine Submodule.mem_sup.mpr ⟨a • onesV, ?_, x - a • onesV, ?_, by abel⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [mem_transverse_iff]
      have e : ∀ i : Fin 3, (x - a • onesV) i = x i - a := by intro i; simp
      rw [e 0, e 1, e 2, ha]; ring

/-- **The rotation relation.**  On the transverse sector the shift satisfies
`σ² + σ + 1 = 0`, the minimal polynomial of a rotation by `2π/3`: the plane is a
single real rotation plane, not a pair of labelled lines. -/
theorem shift_sq_add_shift_add_one {x : V} (hx : x ∈ transverse) :
    shift (shift x) + shift x + x = 0 := by
  have hs := (mem_transverse_iff x).mp hx
  ext i
  fin_cases i <;> simp <;> linarith

/-- **Irreducibility.**  The transverse plane has no proper nonzero
`σ`-invariant subspace, so it is an irreducible two-dimensional real
representation of `C₃`. -/
theorem transverse_irreducible (W : Submodule ℝ V) (hW : W ≤ transverse)
    (hinv : ∀ x ∈ W, shift x ∈ W) : W = ⊥ ∨ W = transverse := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hbot
  have hspan : Submodule.span ℝ ({x} : Set V) ≤ W := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxW
  have hrk1 : Module.finrank ℝ (Submodule.span ℝ ({x} : Set V)) = 1 :=
    finrank_span_singleton hx0
  have hW2 : 2 ≤ Module.finrank ℝ W := by
    by_contra hlt
    push_neg at hlt
    have hle : Module.finrank ℝ W ≤ Module.finrank ℝ (Submodule.span ℝ ({x} : Set V)) := by
      rw [hrk1]; omega
    have hEq : Submodule.span ℝ ({x} : Set V) = W := Submodule.eq_of_le_of_finrank_le hspan hle
    have hmem : shift x ∈ Submodule.span ℝ ({x} : Set V) := by rw [hEq]; exact hinv x hxW
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact no_real_eigenvector_transverse (hW hxW) hx0 c hc.symm
  refine Submodule.eq_of_le_of_finrank_le hW ?_
  rw [finrank_transverse]; exact hW2

end RealC3

/-! ## Part C: the binary contrast -/

namespace RealC2

abbrev V := EuclideanSpace ℝ (Fin 2)

/-- The regular action of the generator of `C₂`. -/
noncomputable def swap : V →ₗ[ℝ] V where
  toFun x := WithLp.toLp 2 (fun i => x (i + 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swap_apply (x : V) (i : Fin 2) : swap x i = x (i + 1) := rfl

def sumForm : V →ₗ[ℝ] ℝ where
  toFun x := x 0 + x 1
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- The transverse sector of `ℝ[C₂]`. -/
def transverse : Submodule ℝ V := LinearMap.ker sumForm

theorem mem_transverse_iff (x : V) : x ∈ transverse ↔ x 0 + x 1 = 0 := Iff.rfl

/-- **The binary collapse.**  On `ℝ[C₂]` the transverse sector *is* an
eigenline: the generator acts on it by `-1`.  So the single nontrivial binary
character is real, and "one nontrivial label" and "one real transverse
dimension" coincide — the conflation that the ternary case forbids. -/
theorem swap_eq_neg_on_transverse {x : V} (hx : x ∈ transverse) : swap x = -x := by
  rw [mem_transverse_iff] at hx
  ext i; fin_cases i <;> simp <;> linarith

/-- The binary transverse sector is one-dimensional. -/
theorem finrank_transverse : Module.finrank ℝ transverse = 1 := by
  have hsurj : Function.Surjective sumForm := by
    intro c
    exact ⟨WithLp.toLp 2 (fun i => if i = 0 then c else 0), by simp [sumForm]⟩
  have h := LinearMap.finrank_range_add_finrank_ker sumForm
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  simp at h
  simp only [transverse]
  omega

end RealC2

end Spine
