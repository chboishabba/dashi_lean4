import Mathlib

/-!
# QFT/GR frontier, lane 6 — the symmetric perturbation fibre

Lane 1 proves that a pairing separates tensors exactly when the admitted
perturbation fibre is everything (algebraically) or dense (topologically).  That
raises the obvious objection to the whole weld: a *physical* metric perturbation
is not an arbitrary element of the perturbation space, it is a **symmetric**
2-tensor.  Symmetric perturbations are a proper subspace, so by lane 1's
obstruction they cannot separate arbitrary tensors.

This lane settles the objection in the concrete matrix model, and it settles it
in favour of the weld — but only because the *stress* side is symmetric too:

* symmetric perturbations do **not** separate arbitrary tensors
  (`symmetric_perturbations_do_not_separate_general_tensors`): the antisymmetric
  part is invisible, exactly as lane 1's obstruction predicts;
* symmetric perturbations **do** separate *symmetric* tensors
  (`eq_of_trace_eq_on_symmetric`).

So the stress weld survives restriction to the physical fibre precisely when
both `G` and `T` are known to be symmetric, and the symmetry of the stress
tensor is not a cosmetic hypothesis: without it the weld is false on the
physical fibre.

## What is proved

* `trace_mul_single` — the elementary trace evaluation the argument runs on;
* `isSymm_singlePair` — the symmetric probe used to read off an entry;
* `eq_of_trace_eq_on_symmetric` — separation of symmetric tensors by symmetric
  perturbations;
* `symmetric_perturbations_do_not_separate_general_tensors` — and the failure
  without symmetry of the tensors;
* `symmetry_of_the_stress_is_load_bearing` — the two put together, as a single
  statement about the weld.
-/

namespace Integration.Variation.SymmetricFibre

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `tr(C · E_{ij}) = C_{ji}`, the evaluation that reads a single entry of `C`
off a trace pairing. -/
theorem trace_mul_single (C : Matrix n n ℝ) (i j : n) :
    (C * Matrix.single i j (1 : ℝ)).trace = C j i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- The symmetric probe `E_{ij} + E_{ji}`. -/
def singlePair (i j : n) : Matrix n n ℝ :=
  Matrix.single i j (1 : ℝ) + Matrix.single j i (1 : ℝ)

omit [Fintype n] in
theorem isSymm_singlePair (i j : n) : (singlePair i j).IsSymm := by
  ext k l
  simp only [Matrix.transpose_apply, singlePair, Matrix.add_apply, Matrix.single_apply,
    and_comm]
  ring

/-- **Symmetric perturbations separate symmetric tensors.**  If two symmetric
matrices have the same trace pairing against every symmetric perturbation, they
are equal. -/
theorem eq_of_trace_eq_on_symmetric (A B : Matrix n n ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hab : ∀ H : Matrix n n ℝ, H.IsSymm → (A * H).trace = (B * H).trace) : A = B := by
  have hC : ∀ H : Matrix n n ℝ, H.IsSymm → ((A - B) * H).trace = 0 := by
    intro H hH
    rw [Matrix.sub_mul, Matrix.trace_sub, hab H hH, sub_self]
  have hsymm : ∀ i j : n, (A - B) j i = (A - B) i j := by
    intro i j
    simp [Matrix.sub_apply, hA.apply j i, hB.apply j i]
  ext i j
  have h0 := hC (singlePair i j) (isSymm_singlePair i j)
  rw [singlePair, Matrix.mul_add, Matrix.trace_add, trace_mul_single, trace_mul_single,
    hsymm i j] at h0
  have hz : (A - B) i j = 0 := by linarith
  simpa [Matrix.sub_apply, sub_eq_zero] using hz

/-- **Symmetric perturbations do not separate arbitrary tensors.**  For two or
more indices there are distinct matrices with identical trace pairings against
every symmetric perturbation: the antisymmetric part is invisible. -/
theorem symmetric_perturbations_do_not_separate_general_tensors [Nontrivial n] :
    ∃ A B : Matrix n n ℝ, A ≠ B ∧
      ∀ H : Matrix n n ℝ, H.IsSymm → (A * H).trace = (B * H).trace := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  refine ⟨0, Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ), ?_, ?_⟩
  · intro hc
    have := congrFun (congrFun hc i) j
    simp [Matrix.sub_apply, hij, hij.symm] at this
  · intro H hH
    rw [Matrix.zero_mul, Matrix.trace_zero, Matrix.sub_mul, Matrix.trace_sub,
      Matrix.trace_mul_comm (Matrix.single i j (1 : ℝ)) H,
      Matrix.trace_mul_comm (Matrix.single j i (1 : ℝ)) H,
      trace_mul_single, trace_mul_single, hH.apply i j, sub_self]

/-- **The symmetry of the stress tensor is load-bearing for the weld.**  On the
physical (symmetric) perturbation fibre, agreement of the pairings forces `G = T`
when both are symmetric, and fails to force it in general. -/
theorem symmetry_of_the_stress_is_load_bearing [Nontrivial n] :
    (∀ G T : Matrix n n ℝ, G.IsSymm → T.IsSymm →
        (∀ H : Matrix n n ℝ, H.IsSymm → (G * H).trace = (T * H).trace) → G = T)
      ∧ ¬ (∀ G T : Matrix n n ℝ,
        (∀ H : Matrix n n ℝ, H.IsSymm → (G * H).trace = (T * H).trace) → G = T) := by
  refine ⟨eq_of_trace_eq_on_symmetric, ?_⟩
  intro hall
  obtain ⟨A, B, hne, hagree⟩ :=
    symmetric_perturbations_do_not_separate_general_tensors (n := n)
  exact hne (hall A B hagree)

end Integration.Variation.SymmetricFibre
