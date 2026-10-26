import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Iterated Tate defect detects the missing characteristic-two extension data

For a square-zero endomorphism `N`, the degree-zero Tate quotient has underlying
dimension `finrank (ker N) - finrank (range N)`. Rank-nullity and
`range N ≤ ker N` give

`defect = finrank V - 2 * finrank (range N)`.

For an involution `g` in characteristic two, take `N = g - 1`.  Thus a
10-dimensional `J₂^5` action has defect zero.  This is precisely the kind of
2-singular invariant ordinary Brauer characters cannot see, and it is the
right target for an iterated-Tate/Klein-four computation on the actual 2B
Tate head.
-/

namespace Integration.OggSSP2BIteratedTateDefectDetector

open LinearMap

variable {K V : Type*}
variable [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Dimension proxy for `ker N / range N`.  For square-zero `N`, `range N ≤ ker N`. -/
def tateDefectFinrank (N : V →ₗ[K] V) : Nat :=
  Module.finrank K ↥N.ker - Module.finrank K ↥N.range

lemma range_le_ker_of_comp_self_eq_zero
    (N : V →ₗ[K] V) (hsq : N.comp N = 0) :
    N.range ≤ N.ker := by
  rintro x ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  have hxy : (N.comp N) y = 0 := by rw [hsq]; rfl
  simpa [LinearMap.comp_apply] using hxy

/-- Rank-nullity formula for the square-zero Tate defect. -/
theorem tateDefectFinrank_eq
    (N : V →ₗ[K] V) (hsq : N.comp N = 0) :
    tateDefectFinrank N =
      Module.finrank K V - 2 * Module.finrank K ↥N.range := by
  have hrk := LinearMap.finrank_range_add_finrank_ker N
  have hleSub : N.range ≤ N.ker := range_le_ker_of_comp_self_eq_zero N hsq
  have hle := Submodule.finrank_mono hleSub
  unfold tateDefectFinrank
  omega

/-- A rank-five square-zero operator on a ten-space has zero Tate defect. -/
theorem ten_rankFive_squareZero_defect_zero
    (N : V →ₗ[K] V) (hsq : N.comp N = 0)
    (hV : Module.finrank K V = 10)
    (hR : Module.finrank K ↥N.range = 5) :
    tateDefectFinrank N = 0 := by
  rw [tateDefectFinrank_eq N hsq, hV, hR]
  norm_num

/-- Conversely, on a ten-space a square-zero operator with zero Tate defect
    must have rank five. -/
theorem ten_defect_zero_forces_rankFive
    (N : V →ₗ[K] V) (hsq : N.comp N = 0)
    (hV : Module.finrank K V = 10)
    (hD : tateDefectFinrank N = 0) :
    Module.finrank K ↥N.range = 5 := by
  have hformula := tateDefectFinrank_eq N hsq
  rw [hV] at hformula
  have hrk := LinearMap.finrank_range_add_finrank_ker N
  have hleSub : N.range ≤ N.ker := range_le_ker_of_comp_self_eq_zero N hsq
  have hle := Submodule.finrank_mono hleSub
  unfold tateDefectFinrank at hD
  omega

end Integration.OggSSP2BIteratedTateDefectDetector
