import Mathlib.Tactic
import NSBControl.Rational345Round71PhysicalCarrier

/-!
# Round71 transversality of the literal radius-four field

For every nonzero output mode the Leray projector kills the longitudinal
component.  Hence the quadratic Galerkin nonlinearity is transverse for
*arbitrary* input state.  The divergence variable of the full field therefore
obeys the scalar linear law

  k · Q(u)_k = -|k|² (k · u_k).

This is the exact finite-dimensional invariant needed to transport the R830
trajectory into Agda's `LivePhysicalPacketStructure` divergence-free field.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345Round71TransverseField

open Rational345RealRadius4
open Rational345Round71PhysicalCarrier

/-- Explicit three-coordinate norm square. -/
theorem normSq_three (k : Mode) :
    normSq k =
      (kReal k 0)^2 + (kReal k 1)^2 + (kReal k 2)^2 := by
  simp [normSq, Fin.sum_univ_succ]

/-- A nonzero lattice mode has strictly positive Euclidean square norm. -/
theorem normSq_pos {k : Mode} (hk : ¬ isZeroMode k) : 0 < normSq k := by
  rw [normSq_three]
  have hc := nonzero_coordinate hk
  rcases hc with hx | hy | hz
  · have hxr : (kReal k 0) ≠ 0 := by
      exact_mod_cast hx
    nlinarith [sq_pos_of_ne_zero hxr, sq_nonneg (kReal k 1), sq_nonneg (kReal k 2)]
  · have hyr : (kReal k 1) ≠ 0 := by
      exact_mod_cast hy
    nlinarith [sq_nonneg (kReal k 0), sq_pos_of_ne_zero hyr, sq_nonneg (kReal k 2)]
  · have hzr : (kReal k 2) ≠ 0 := by
      exact_mod_cast hz
    nlinarith [sq_nonneg (kReal k 0), sq_nonneg (kReal k 1), sq_pos_of_ne_zero hzr]

 theorem normSq_ne_zero {k : Mode} (hk : ¬ isZeroMode k) : normSq k ≠ 0 :=
  ne_of_gt (normSq_pos hk)

/-- Dotting the real wave vector with itself produces the embedded norm square. -/
theorem bilinearDot_kComplex_self (k : Mode) :
    bilinearDot (kComplex k) (kComplex k) = (normSq k : ℂ) := by
  simp [bilinearDot, kComplex, normSq, kReal, Fin.sum_univ_succ]
  ring

theorem bilinearDot_add_right (w u v : Vec3) :
    bilinearDot w (u + v) = bilinearDot w u + bilinearDot w v := by
  simp [bilinearDot, Finset.mul_sum]
  ring

theorem bilinearDot_sub_right (w u v : Vec3) :
    bilinearDot w (u - v) = bilinearDot w u - bilinearDot w v := by
  simp [bilinearDot, Finset.mul_sum]
  ring

theorem bilinearDot_smul_right (w : Vec3) (c : ℂ) (v : Vec3) :
    bilinearDot w (c • v) = c * bilinearDot w v := by
  simp [bilinearDot, Finset.mul_sum]
  ring

theorem bilinearDot_sum_right
    {ι : Type*} [Fintype ι] (w : Vec3) (f : ι → Vec3) :
    bilinearDot w (∑ i, f i) = ∑ i, bilinearDot w (f i) := by
  simp [bilinearDot, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Component formula for Leray projection in scalar-multiple form. -/
theorem leray_eq_sub_smul {k : Mode} (hk : ¬ isZeroMode k) (v : Vec3) :
    leray k v =
      v - (bilinearDot (kComplex k) v / (normSq k : ℂ)) • kComplex k := by
  funext j
  simp [leray, hk, kComplex]
  ring

/-- Literal Leray projection is transverse on every nonzero output mode. -/
theorem leray_transverse {k : Mode} (hk : ¬ isZeroMode k) (v : Vec3) :
    bilinearDot (kComplex k) (leray k v) = 0 := by
  rw [leray_eq_sub_smul hk]
  rw [bilinearDot_sub_right, bilinearDot_smul_right,
      bilinearDot_kComplex_self]
  have hnormR : normSq k ≠ 0 := normSq_ne_zero hk
  have hnormC : (normSq k : ℂ) ≠ 0 := by exact_mod_cast hnormR
  field_simp

/-- Every resonant ordered cell is transverse at its output. -/
theorem projectedOrdered_transverse
    (left right : State) {k : Mode} (hk : ¬ isZeroMode k) (p q : Mode) :
    bilinearDot (kComplex k) (projectedOrderedBilinear left right p q k) = 0 := by
  by_cases hres : Resonates p q k
  · simp only [projectedOrderedBilinear, hres, if_true]
    rw [show (fun j => -Complex.I *
          leray k (fun a => bilinearDot (left p) (kComplex q) * right q a) j)
        = (-Complex.I) •
          leray k (fun a => bilinearDot (left p) (kComplex q) * right q a) by
      rfl]
    rw [bilinearDot_smul_right, leray_transverse hk]
    simp
  · simp [projectedOrderedBilinear, hres, bilinearDot]

/-- The complete projected quadratic nonlinearity is transverse for arbitrary
input state. -/
theorem projectedNonlinearity_transverse (u : State) (k : Mode) :
    bilinearDot (kComplex k) (projectedNonlinearity u k) = 0 := by
  by_cases hk : isZeroMode k
  · simp [projectedNonlinearity, projectedBilinear, hk, bilinearDot]
  · unfold projectedNonlinearity projectedBilinear
    simp only [hk, if_false]
    rw [bilinearDot_sum_right]
    apply Finset.sum_eq_zero
    intro p hp
    rw [bilinearDot_sum_right]
    apply Finset.sum_eq_zero
    intro q hq
    exact projectedOrdered_transverse u u hk p q

/-- Viscosity is the only longitudinal contribution. -/
theorem divergence_viscous_identity (u : State) (k : Mode) :
    bilinearDot (kComplex k) (viscousLinear u k) =
      -(normSq k : ℂ) * bilinearDot (kComplex k) (u k) := by
  by_cases hk : isZeroMode k
  · have hnorm : normSq k = 0 := by
      rw [normSq_three]
      have hx := hk (0 : Fin 3)
      have hy := hk (1 : Fin 3)
      have hz := hk (2 : Fin 3)
      norm_num [kReal] at hx hy hz ⊢
      rw [hx, hy, hz]
      norm_num
    simp [viscousLinear, hk, hnorm, bilinearDot]
  · simp only [viscousLinear, hk, if_false]
    rw [show (fun j => -(normSq k : ℂ) * u k j) =
        (-(normSq k : ℂ)) • u k by rfl]
    rw [bilinearDot_smul_right]

/-- Exact divergence equation for the literal Galerkin field. -/
theorem divergence_field_identity (u : State) (k : Mode) :
    bilinearDot (kComplex k) (galerkinField u k) =
      -(normSq k : ℂ) * bilinearDot (kComplex k) (u k) := by
  rw [galerkinField_eq_linear_add_bilinear]
  change bilinearDot (kComplex k)
      (viscousLinear u k + projectedNonlinearity u k) = _
  rw [bilinearDot_add_right, projectedNonlinearity_transverse,
      add_zero, divergence_viscous_identity]

/-- In particular, the field is tangent to the divergence-free subspace. -/
theorem galerkinField_transverse_of_transverse
    (u : State)
    (hu : ∀ k, bilinearDot (kComplex k) (u k) = 0)
    (k : Mode) :
    bilinearDot (kComplex k) (galerkinField u k) = 0 := by
  rw [divergence_field_identity, hu]
  simp

/-- Operator-level divergence preservation is closed. -/
def round71LiteralGalerkinTransverseClosed : Bool := true

end Rational345Round71TransverseField
end NSBControl
