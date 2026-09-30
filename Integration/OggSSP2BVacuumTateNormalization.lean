import Mathlib

/-!
# Ordinary C2 Tate cohomology: vacuum normalization check

For the rank-one integral vacuum lattice Z, every VOA automorphism
fixes its generator. Therefore g=1, N=1+g=2, D=g-1=0.
The ordinary C2 Tate groups are Hhat0=Z/2 and Hhat1=0.

This does not claim that a Fourier half-shift is the coefficientwise
Tate decomposition; in fact the naive q^(n-1) parity assignment
places a q^(-1) pole in the difference branch and therefore
requires an explicit grading/normalization reconciliation against
Carnahan Corollary 3.25 before the two structures can be identified.
-/

namespace Integration.OggSSP2BVacuumTateNormalization

theorem vacuum_norm_is_double (n : ℤ) :
    n + n = 2 * n := by ring

theorem vacuum_coboundary_zero (n : ℤ) :
    n - n = 0 := by ring

theorem vacuum_norm_kernel_trivial
    (n : ℤ) (hn : n + n = 0) : n = 0 := by
  omega

theorem vacuum_unit_not_a_norm :
    ¬ ∃ n : ℤ, n + n = 1 := by
  rintro ⟨n, hn⟩
  omega

theorem vacuum_h0_nontrivial_mod_two :
    (1 : ZMod 2) ≠ 0 := by
  decide

theorem vacuum_h1_no_nonzero_cocycles :
    ∀ n : ℤ, n + n = 0 → n = 0 :=
  vacuum_norm_kernel_trivial

/-- Algebraic q^(-1) routing: the half-translation sign is -1.
This is a statement about the series index, NOT a Tate-isomorphism. -/
theorem negative_one_half_translation_sign :
    (1 + (-1 : ℤ)) = 0 ∧ (1 - (-1 : ℤ)) = 2 := by
  constructor <;> norm_num

/-- An unconditional identification of the difference/half-shift
coefficients with ordinary Hhat1 of the *fixed vacuum* would demand
both Hhat1=0 and a nonzero pole. It is mathematically incompatible.
This audits the naive indexing, not the correctness of Carnahan's
published theorem, whose exact conventions must be retained. -/
theorem naive_vacuum_coefficient_identification_inconsistent
    (naiveDifferencePole : ℤ)
    (hNaive : naiveDifferencePole = 1)
    (hTateH1 : naiveDifferencePole = 0) : False := by
  omega

end Integration.OggSSP2BVacuumTateNormalization
