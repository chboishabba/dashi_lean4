import Integration.EisensteinQuadraticAlgebraExact
import Integration.EisensteinLatticeCountingMaxCut
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round

namespace Dashi.EisensteinEuclideanDomainExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut
open Dashi.EisensteinQuadraticAlgebraExact

------------------------------------------------------------------------
-- Positive definite norm on the standard `QuadraticAlgebra ℤ (-1) (-1)`.
------------------------------------------------------------------------

theorem norm_eq_coordinate_norm (z : EisensteinQA) :
    QuadraticAlgebra.norm z = eisensteinNorm z.re z.im := by
  simp [QuadraticAlgebra.norm_def, eisensteinNorm]
  ring

theorem norm_nonneg (z : EisensteinQA) :
    0 ≤ QuadraticAlgebra.norm z := by
  rw [norm_eq_coordinate_norm]
  have h := eisensteinNorm_four_decomposition_a z.re z.im
  nlinarith [sq_nonneg (z.re - 2 * z.im)]

@[simp] theorem norm_eq_zero {z : EisensteinQA} :
    QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have ha_bound := eisensteinNorm_coercive_a z.re z.im
    have hb_bound := eisensteinNorm_coercive_b z.re z.im
    rw [← norm_eq_coordinate_norm, hz] at ha_bound hb_bound
    have ha_sq : z.re * z.re = 0 := by
      nlinarith [sq_nonneg z.re]
    have hb_sq : z.im * z.im = 0 := by
      nlinarith [sq_nonneg z.im]
    have ha : z.re = 0 := mul_self_eq_zero.mp ha_sq
    have hb : z.im = 0 := mul_self_eq_zero.mp hb_sq
    ext <;> simp [ha, hb]
  · rintro rfl
    simp [QuadraticAlgebra.norm_def]

theorem norm_pos {z : EisensteinQA} :
    0 < QuadraticAlgebra.norm z ↔ z ≠ 0 := by
  constructor
  · intro hz hzero
    subst z
    simp at hz
  · intro hzero
    have hnonneg := norm_nonneg z
    have hne : QuadraticAlgebra.norm z ≠ 0 :=
      fun hz => hzero (norm_eq_zero.mp hz)
    omega

------------------------------------------------------------------------
-- Exact quotient numerators.
--
-- For x = a+bω and y = c+dω,
--   x * star(y) = A + Bω
-- with A = ac-ad+bd and B = -ad+bc.
-- Dividing A and B by N(y), then independently rounding, gives the nearest
-- lattice quotient in the coefficient square.  The Eisenstein norm of the
-- coefficient error is at most 3/4, which is strictly below one.
------------------------------------------------------------------------

def quotientNumeratorRe (x y : EisensteinQA) : Int :=
  (x * star y).re

def quotientNumeratorIm (x y : EisensteinQA) : Int :=
  (x * star y).im

def quotientCoordinateRe (x y : EisensteinQA) : Rat :=
  (quotientNumeratorRe x y : Rat) / (QuadraticAlgebra.norm y : Rat)

def quotientCoordinateIm (x y : EisensteinQA) : Rat :=
  (quotientNumeratorIm x y : Rat) / (QuadraticAlgebra.norm y : Rat)

def eisensteinQuotient (x y : EisensteinQA) : EisensteinQA :=
  asQuadraticAlgebra
    (round (quotientCoordinateRe x y))
    (round (quotientCoordinateIm x y))

instance instDiv : Div EisensteinQA := ⟨eisensteinQuotient⟩

@[simp] theorem div_def (x y : EisensteinQA) :
    x / y =
      asQuadraticAlgebra
        (round (quotientCoordinateRe x y))
        (round (quotientCoordinateIm x y)) := rfl

def eisensteinRemainder (x y : EisensteinQA) : EisensteinQA :=
  x - y * (x / y)

instance instMod : Mod EisensteinQA := ⟨eisensteinRemainder⟩

@[simp] theorem mod_def (x y : EisensteinQA) :
    x % y = x - y * (x / y) := rfl

------------------------------------------------------------------------
-- The finite geometry behind the Euclidean contraction.
------------------------------------------------------------------------

theorem coefficient_error_norm_lt_one
    (u v : Rat)
    (hu : |u| ≤ (1 / 2 : Rat))
    (hv : |v| ≤ (1 / 2 : Rat)) :
    u ^ 2 - u * v + v ^ 2 < 1 := by
  have hu_sq : u ^ 2 ≤ (1 / 2 : Rat) ^ 2 :=
    sq_le_sq.mpr (by simpa using hu)
  have hv_sq : v ^ 2 ≤ (1 / 2 : Rat) ^ 2 :=
    sq_le_sq.mpr (by simpa using hv)
  have huv_abs : |u * v| ≤ (1 / 2 : Rat) * (1 / 2 : Rat) := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg v) (by norm_num)
  have hneg_uv : -(u * v) ≤ |u * v| := neg_le_abs (u * v)
  nlinarith

/-- Polynomial identity relating an arbitrary integral quotient `(m,n)` to the
exact quotient numerators.  It is the division algorithm without inequalities. -/
theorem scaled_remainder_norm_identity
    (x y : EisensteinQA) (m n : Int) :
    QuadraticAlgebra.norm y *
        QuadraticAlgebra.norm (x - y * asQuadraticAlgebra m n)
      =
    eisensteinNorm
      (quotientNumeratorRe x y - QuadraticAlgebra.norm y * m)
      (quotientNumeratorIm x y - QuadraticAlgebra.norm y * n) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [quotientNumeratorRe, quotientNumeratorIm, asQuadraticAlgebra,
    QuadraticAlgebra.norm_def, eisensteinNorm]
  ring

/-- Rounding the two exact quotient coordinates produces numerator errors whose
Eisenstein norm is strictly smaller than `N(y)^2`. -/
theorem rounded_numerator_error_norm_lt_square
    (x : EisensteinQA) {y : EisensteinQA} (hy : y ≠ 0) :
    eisensteinNorm
      (quotientNumeratorRe x y -
        QuadraticAlgebra.norm y * round (quotientCoordinateRe x y))
      (quotientNumeratorIm x y -
        QuadraticAlgebra.norm y * round (quotientCoordinateIm x y))
      < QuadraticAlgebra.norm y * QuadraticAlgebra.norm y := by
  let N : Int := QuadraticAlgebra.norm y
  let A : Int := quotientNumeratorRe x y
  let B : Int := quotientNumeratorIm x y
  let m : Int := round (quotientCoordinateRe x y)
  let n : Int := round (quotientCoordinateIm x y)
  let U : Int := A - N * m
  let V : Int := B - N * n
  let u : Rat := (U : Rat) / (N : Rat)
  let v : Rat := (V : Rat) / (N : Rat)

  have hN : 0 < N := by
    simpa [N] using (norm_pos (z := y)).2 hy
  have hNq : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  have hNne : (N : Rat) ≠ 0 := ne_of_gt hNq

  have hu_ident :
      u = quotientCoordinateRe x y - (m : Rat) := by
    simp [u, U, A, N, m, quotientCoordinateRe]
    field_simp [hNne]
    ring
  have hv_ident :
      v = quotientCoordinateIm x y - (n : Rat) := by
    simp [v, V, B, N, n, quotientCoordinateIm]
    field_simp [hNne]
    ring

  have hu : |u| ≤ (1 / 2 : Rat) := by
    rw [hu_ident]
    simpa [m] using abs_sub_round (quotientCoordinateRe x y)
  have hv : |v| ≤ (1 / 2 : Rat) := by
    rw [hv_ident]
    simpa [n] using abs_sub_round (quotientCoordinateIm x y)
  have herr : u ^ 2 - u * v + v ^ 2 < 1 :=
    coefficient_error_norm_lt_one u v hu hv

  have hU : (U : Rat) = (N : Rat) * u := by
    simp [u]
    field_simp [hNne]
  have hV : (V : Rat) = (N : Rat) * v := by
    simp [v]
    field_simp [hNne]

  have hcast :
      ((eisensteinNorm U V : Int) : Rat)
        = (N : Rat) ^ 2 * (u ^ 2 - u * v + v ^ 2) := by
    simp [eisensteinNorm, hU, hV]
    ring
  have hsqpos : (0 : Rat) < (N : Rat) ^ 2 := sq_pos_of_pos hNq
  have hrat :
      ((eisensteinNorm U V : Int) : Rat) < ((N * N : Int) : Rat) := by
    rw [hcast]
    norm_num [Int.cast_mul]
    nlinarith
  have hint : eisensteinNorm U V < N * N := by
    exact_mod_cast hrat
  simpa [U, V, A, B, N, m, n] using hint

------------------------------------------------------------------------
-- Euclidean remainder contraction and the actual domain instance.
------------------------------------------------------------------------

theorem norm_mod_lt (x : EisensteinQA) {y : EisensteinQA} (hy : y ≠ 0) :
    QuadraticAlgebra.norm (x % y) < QuadraticAlgebra.norm y := by
  let m := round (quotientCoordinateRe x y)
  let n := round (quotientCoordinateIm x y)
  have hscaled := scaled_remainder_norm_identity x y m n
  have herr := rounded_numerator_error_norm_lt_square x hy
  have hN : 0 < QuadraticAlgebra.norm y := (norm_pos (z := y)).2 hy
  rw [mod_def, div_def] at hscaled
  dsimp [m, n] at hscaled
  nlinarith

theorem natAbs_norm_mod_lt (x : EisensteinQA) {y : EisensteinQA} (hy : y ≠ 0) :
    (QuadraticAlgebra.norm (x % y)).natAbs <
      (QuadraticAlgebra.norm y).natAbs := by
  have hrem_nonneg := norm_nonneg (x % y)
  have hy_nonneg := norm_nonneg y
  rw [Int.natAbs_of_nonneg hrem_nonneg, Int.natAbs_of_nonneg hy_nonneg]
  exact_mod_cast norm_mod_lt x hy

theorem norm_le_norm_mul_left (x : EisensteinQA) {y : EisensteinQA} (hy : y ≠ 0) :
    (QuadraticAlgebra.norm x).natAbs ≤
      (QuadraticAlgebra.norm (x * y)).natAbs := by
  rw [map_mul, Int.natAbs_mul]
  have hy_one : 1 ≤ (QuadraticAlgebra.norm y).natAbs := by
    rw [Int.natAbs_of_nonneg (norm_nonneg y)]
    exact_mod_cast (Int.add_one_le_of_lt ((norm_pos (z := y)).2 hy))
  exact le_mul_of_one_le_right (Nat.zero_le _) hy_one

instance instEuclideanDomain : EuclideanDomain EisensteinQA :=
  { inferInstanceAs (CommRing EisensteinQA),
    inferInstanceAs (Nontrivial EisensteinQA) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro x
      ext <;> simp [div_def, quotientCoordinateRe, quotientCoordinateIm,
        quotientNumeratorRe, quotientNumeratorIm, asQuadraticAlgebra]
    quotient_mul_add_remainder_eq := by
      intro x y
      simp [mod_def]
      ring
    r := fun z => (QuadraticAlgebra.norm z).natAbs
    r_wellFounded := (measure (Int.natAbs ∘ QuadraticAlgebra.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 =>
      not_lt_of_ge (norm_le_norm_mul_left a hb0) }

structure EisensteinEuclideanBoundary where
  positiveDefiniteNormPaid : Bool := true
  roundedQuotientConstructed : Bool := true
  coefficientErrorThreeQuarterBoundPaid : Bool := true
  remainderNormContractionPaid : Bool := true
  euclideanDomainInstanceConstructed : Bool := true
  ufdAvailableByTypeclass : Bool := true
  splitPrimeRepresentationCountPaid : Bool := false
  universalRepresentationFormulaPaid : Bool := false

def canonicalBoundary : EisensteinEuclideanBoundary := {}

end Dashi.EisensteinEuclideanDomainExact
