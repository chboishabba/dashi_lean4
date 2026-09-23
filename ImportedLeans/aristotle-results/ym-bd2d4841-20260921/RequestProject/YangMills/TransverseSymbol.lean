/-
# A closed-form constrained symbol: the rank-one (Landau-type) constraint

The abstract Schur formula `G = G̃ − G̃Qᵀ(QG̃Qᵀ)⁻¹QG̃` becomes fully explicit as
soon as the constraint at a fixed momentum is a single linear condition
`⟨u, B⟩ = 0`, which is the shape of a Landau/axial-type gauge constraint symbol.
This module computes that case exactly:

    G̃ = a·1,  Q = uᵀ  ⟹  G = a·(1 − uuᵀ/|u|²),

the transverse projector divided by the scalar part of the operator
(`constrainedPropagator_rankOne`), together with its Ward identity `G u = 0`
(`transverseProjector_mulVec_self`).

It is then instantiated at the lattice momentum of `LatticeMomentum`: with
`u_μ = p̂_μ = 2 sin(π p_μ)` and `a = 1/p̂²` one gets the lattice transverse
propagator

    G(p)_{μν} = ( δ_{μν} − p̂_μ p̂_ν / p̂² ) / p̂² ,

and `wilsonOperator_mul_transversePropagator` proves that it inverts the Wilson
quadratic operator `K_{μν} = δ_{μν} p̂² − p̂_μ p̂_ν` *on the transverse subspace*:

    K(p) · G(p) = 1 − p̂ p̂ᵀ / p̂² ,

which is the identity on the constraint kernel and zero on the longitudinal
direction.  The gauge zero mode of `K` is therefore exactly the direction the
constraint removes; the constrained problem is well posed and its propagator is
the explicit matrix above.

**Provenance.**  `p̂_μ = 2 sin(π p_μ)` and `K_{μν} = δ_{μν} p̂² − p̂_μ p̂_ν` are the
project's own conventions, fixed in `LatticeMomentum`; nothing in this file is
presented as a transcription of an external text, and no numerical value of a
beta coefficient is asserted anywhere.
-/
import RequestProject.YangMills.ConstrainedPropagator
import RequestProject.YangMills.LatticeMomentum

namespace YangMills

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The constraint symbol of a single linear condition, as a `1 × n` matrix. -/
def rowVec (u : n → ℝ) : Matrix (Fin 1) n ℝ := Matrix.replicateRow (Fin 1) u

/-- The squared length of the constraint direction. -/
def normSqVec (u : n → ℝ) : ℝ := ∑ i, u i * u i

/-- The transverse projector `1 − uuᵀ/|u|²`. -/
noncomputable def transverseProjector (u : n → ℝ) : Matrix n n ℝ :=
  1 - (normSqVec u)⁻¹ • Matrix.vecMulVec u u

omit [Fintype n] [DecidableEq n] in
theorem rowVec_transpose_mul (u : n → ℝ) :
    (rowVec u)ᵀ * rowVec u = Matrix.vecMulVec u u := by
  ext i j
  simp [rowVec, Matrix.mul_apply, Matrix.vecMulVec_apply]

theorem reducedBlock_rankOne (u : n → ℝ) (a : ℝ) :
    rowVec u * (a • (1 : Matrix n n ℝ)) * (rowVec u)ᵀ
      = (a * normSqVec u) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [rowVec, normSqVec, Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm]

theorem inv_smul_one {N : Type*} [Fintype N] [DecidableEq N] {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix N N ℝ))⁻¹ = c⁻¹ • (1 : Matrix N N ℝ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

/-- **The constrained propagator of a scalar operator with a rank-one
constraint is the transverse projector.**
`G̃ = a·1`, `Q = uᵀ` ⟹ `G = a·(1 − uuᵀ/|u|²)`. -/
theorem constrainedPropagator_rankOne (u : n → ℝ) (a : ℝ) (ha : a ≠ 0)
    (hu : normSqVec u ≠ 0) :
    constrainedPropagator (a • (1 : Matrix n n ℝ)) (rowVec u)
      = a • transverseProjector u := by
  have hK : rowVec u * (a • (1 : Matrix n n ℝ)) * (rowVec u)ᵀ
      = (a * normSqVec u) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := reducedBlock_rankOne u a
  have hKinv : (rowVec u * (a • (1 : Matrix n n ℝ)) * (rowVec u)ᵀ)⁻¹
      = (a * normSqVec u)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hK, inv_smul_one (mul_ne_zero ha hu)]
  rw [constrainedPropagator, hKinv, transverseProjector]
  have hprod : (a • (1 : Matrix n n ℝ)) * (rowVec u)ᵀ
      * ((a * normSqVec u)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      * (rowVec u * (a • (1 : Matrix n n ℝ)))
      = (a * a * (a * normSqVec u)⁻¹) • Matrix.vecMulVec u u := by
    rw [← rowVec_transpose_mul u]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
      Matrix.one_mul]
    congr 1
    field_simp
  rw [hprod, smul_sub, smul_smul]
  have hscal : a * a * (a * normSqVec u)⁻¹ = a * (normSqVec u)⁻¹ := by
    field_simp
  rw [hscal]

/-- **The Ward identity of the closed-form symbol.**  The transverse projector
annihilates the constraint direction: `(1 − uuᵀ/|u|²) u = 0`. -/
theorem transverseProjector_mulVec_self (u : n → ℝ) (hu : normSqVec u ≠ 0) :
    (transverseProjector u).mulVec u = 0 := by
  have hw : (Matrix.vecMulVec u u).mulVec u = normSqVec u • u := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, normSqVec]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [transverseProjector, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec, hw,
    smul_smul, inv_mul_cancel₀ hu, one_smul, sub_self]

section Lattice

open scoped Real

/-- The lattice momentum vector `p̂_μ = 2 sin(π p_μ)`. -/
noncomputable def phatVec (p : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ => phat (p μ)

theorem normSqVec_phatVec (p : Fin 4 → ℝ) : normSqVec (phatVec p) = phatSq p := by
  rw [normSqVec, phatSq]
  exact Finset.sum_congr rfl fun μ _ => by rw [phatVec]; ring

/-- The Wilson quadratic operator at momentum `p`, as a matrix:
`K_{μν} = δ_{μν} p̂² − p̂_μ p̂_ν`. -/
noncomputable def wilsonOperator (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => wilsonInversePropagator p μ ν

theorem wilsonOperator_eq (p : Fin 4 → ℝ) :
    wilsonOperator p
      = (phatSq p) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - Matrix.vecMulVec (phatVec p) (phatVec p) := by
  ext μ ν
  by_cases h : μ = ν <;>
    simp [wilsonOperator, wilsonInversePropagator, Matrix.vecMulVec_apply, phatVec,
      h]

/-- The lattice transverse propagator `G(p) = (1 − p̂p̂ᵀ/p̂²)/p̂²`, obtained from
the constrained Schur formula with the rank-one constraint `p̂ᵀ`. -/
theorem constrainedPropagator_lattice (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    constrainedPropagator ((phatSq p)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
        (rowVec (phatVec p))
      = (phatSq p)⁻¹ • transverseProjector (phatVec p) := by
  refine constrainedPropagator_rankOne (phatVec p) _ (inv_ne_zero hp) ?_
  rw [normSqVec_phatVec]
  exact hp

/-- **The closed-form symbol inverts the Wilson operator on the constraint
kernel.**  `K(p) · G(p) = 1 − p̂p̂ᵀ/p̂²`: the identity transversally, zero on the
longitudinal direction that the constraint removes. -/
theorem wilsonOperator_mul_transversePropagator (p : Fin 4 → ℝ) (hp : phatSq p ≠ 0) :
    wilsonOperator p * ((phatSq p)⁻¹ • transverseProjector (phatVec p))
      = transverseProjector (phatVec p) := by
  set c := phatSq p with hc
  set w := Matrix.vecMulVec (phatVec p) (phatVec p) with hw
  have hnorm : normSqVec (phatVec p) = c := normSqVec_phatVec p
  have hww : w * w = c • w := by
    ext i j
    simp only [hw, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [← hnorm, normSqVec, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hT : transverseProjector (phatVec p) = 1 - c⁻¹ • w := by
    rw [transverseProjector, hnorm, hw]
  have hK : wilsonOperator p = c • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w := by
    rw [wilsonOperator_eq, hc, hw]
  have e : (c • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w) * (1 - c⁻¹ • w)
      = c • (1 - c⁻¹ • w) := by
    calc (c • (1 : Matrix (Fin 4) (Fin 4) ℝ) - w) * (1 - c⁻¹ • w)
        = c • (1 * (1 - c⁻¹ • w)) - w * (1 - c⁻¹ • w) := by
          rw [Matrix.sub_mul, Matrix.smul_mul]
      _ = c • ((1 : Matrix (Fin 4) (Fin 4) ℝ) - c⁻¹ • w) - (w - c⁻¹ • (w * w)) := by
          rw [Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
      _ = c • ((1 : Matrix (Fin 4) (Fin 4) ℝ) - c⁻¹ • w) - (w - c⁻¹ • (c • w)) := by
          rw [hww]
      _ = c • ((1 : Matrix (Fin 4) (Fin 4) ℝ) - c⁻¹ • w) := by
          rw [smul_smul, inv_mul_cancel₀ hp, one_smul, sub_self, sub_zero]
  rw [hT, hK, Matrix.mul_smul, e, smul_smul, inv_mul_cancel₀ hp, one_smul]

end Lattice

end YangMills
