import RequestProject.ArtinSchreier
import RequestProject.FrobeniusAutomorphismGroup
import RequestProject.GF27
import RequestProject.HilbertNinety

/-!
# Artin–Schreier, Hilbert 90 and the automorphism group for the concrete field `GF27`

The general theorems of `ArtinSchreier.lean`, `HilbertNinety.lean` and
`FrobeniusAutomorphismGroup.lean`, instantiated at the kernel-computable field
`GF27 = 𝔽₃[t]/(t³ - t - 1)`:

* `GF27.exists_cube_sub_self_iff` : `x³ - x = a` is solvable in `GF27` exactly when
  `a + a³ + a⁹ = 0`;
* `GF27.card_range_asHom` : the image of `x ↦ x³ - x` has `9` elements, and equals the kernel of
  the trace (`GF27.range_asHom_eq_ker_traceHom`);
* `GF27.pow_thirteen_eq_one_iff` : a nonzero element has norm `x¹³ = 1` exactly when it is a
  square;
* `GF27.card_ringAut_eq` : `GF27` has exactly `3` ring automorphisms, namely the Frobenius
  iterates `x ↦ x^(3^k)`, `k < 3` (`GF27.exists_pow_of_ringHom`).

The abstract solvability criterion is cross-checked against a direct kernel computation over the
27 elements of `GF27` (`GF27.exists_cube_sub_self_iff_kernel`, `GF27.card_cube_sub_self_image`).
-/

open FrobeniusPrimeSubfield

namespace GF27

/-- On `GF27` the Frobenius orbit sum is `a ↦ a + a³ + a⁹`. -/
theorem frobTrace_eq (a : GF27) : frobTrace 3 3 a = a + a ^ 3 + a ^ 9 := by
  simp [frobTrace, Finset.sum_range_succ]

/-- **Artin–Schreier for `GF27`**: the image of `x ↦ x³ - x` is the kernel of the trace. -/
theorem range_asHom_eq_ker_traceHom :
    (asHom GF27 3).range = (traceHom GF27 3 3).ker :=
  FrobeniusPrimeSubfield.range_asHom_eq_ker_traceHom card_eq (by norm_num)

/-- The image of `x ↦ x³ - x` on `GF27` has exactly `9` elements. -/
theorem card_range_asHom : Nat.card (asHom GF27 3).range = 9 := by
  rw [FrobeniusPrimeSubfield.card_range_asHom card_eq (by norm_num)]
  norm_num

/-- **The Artin–Schreier equation over `GF27`**: `x³ - x = a` is solvable iff `a + a³ + a⁹ = 0`. -/
theorem exists_cube_sub_self_iff (a : GF27) :
    (∃ x : GF27, x ^ 3 - x = a) ↔ a + a ^ 3 + a ^ 9 = 0 := by
  rw [← frobTrace_eq]
  exact FrobeniusPrimeSubfield.exists_pow_sub_self_eq_iff card_eq (by norm_num) a

/-! ### Cross-checks by kernel computation -/

/-- The same criterion, verified directly by the kernel over all `27` elements. -/
theorem exists_cube_sub_self_iff_kernel (a : GF27) :
    (∃ x : GF27, x * x * x - x = a) ↔ a + a * a * a + (a * a * a) * (a * a * a) * (a * a * a) = 0 := by
  revert a
  decide

/-- The image of `x ↦ x³ - x` really does consist of `9` elements (kernel computation). -/
theorem card_cube_sub_self_image :
    ((enum.map fun x => x * x * x - x).dedup).length = 9 := by decide

/-! ### The automorphism group of `GF27` -/

/-- Every ring endomorphism of `GF27` is a Frobenius iterate `x ↦ x^(3^k)` with `k < 3`. -/
theorem exists_pow_of_ringHom (σ : GF27 →+* GF27) : ∃ k < 3, ∀ x : GF27, σ x = x ^ 3 ^ k :=
  exists_pow_pow_char_eq_of_ringHom card_eq σ

/-- `GF27` has exactly three ring automorphisms. -/
theorem card_ringAut_eq : Nat.card (GF27 ≃+* GF27) = 3 :=
  card_ringAut card_eq (by norm_num)

/-! ### Hilbert 90 for `GF27` -/

/-- On `GF27` the Frobenius orbit product is `x ↦ x¹³`. -/
theorem frobNorm_eq (x : GF27) : frobNorm 3 3 x = x ^ 13 := by
  rw [frobNorm_eq_pow]
  norm_num [Finset.sum_range_succ]

/-- **Hilbert 90 for `GF27`**: a nonzero element has norm `1` exactly when it is a square. -/
theorem pow_thirteen_eq_one_iff {x : GF27} (hx : x ≠ 0) :
    x ^ 13 = 1 ↔ ∃ y : GF27, y ≠ 0 ∧ y ^ 2 = x := by
  rw [← frobNorm_eq]
  exact frobNorm_eq_one_iff card_eq hx

/-- The same statement, verified directly by the kernel over all `27` elements. -/
theorem pow_thirteen_eq_one_iff_kernel :
    ∀ x : GF27, x ≠ 0 → (x ^ 13 = 1 ↔ ∃ y : GF27, y ≠ 0 ∧ y * y = x) := by decide

end GF27
