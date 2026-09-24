import Mathlib
import Synthesis.SpinCoverBridge

/-!
# Synthesis layer 2''''''' (continued): a genuine *continuous* double cover

`Synthesis.SpinCoverBridge` instantiated the supplied spin interface with the
repository's finite quaternion cover `Q8 → V4Rotation`, and showed that the
supplied *continuous* `Spin(3,1) → SO⁺(3,1)` record is inhabited with all of its
propositional obligations set to `True`.  That left a gap: everything with real
cover content was finite.

This module closes half of that gap, honestly.  The squaring map on the circle
group,

  `sq : Circle → Circle`, `z ↦ z ^ 2`,

is a continuous group homomorphism of an infinite compact topological group which
is genuinely two-to-one: it is surjective, its kernel is `{1, -1}`, and every
fibre has exactly two elements (`sq_fiber_exact`).  Instantiating the spin
interface with it gives
`spin_interface_satisfiable_with_continuous_cover`: the interface admits an
instance whose carriers are *infinite topological groups* and whose cover field
really is a two-to-one continuous homomorphism.

## Boundary (kept explicit)

`Circle` is not `Spin(3,1)` and squaring is not the Lorentz cover.  What is
proved is exactly that the interface's cover field can be inhabited by a genuine
continuous double cover of Lie groups — not that the repository contains, or
implies, the spin cover of the Lorentz group.  The obligation to build
`Spin(3,1) → SO⁺(3,1)` remains open.
-/

namespace Synthesis.CircleCover

open AgdaMirror.SpinEmergence

/-- The non-trivial square root of `1` in the circle group. -/
noncomputable def negOne : Circle := Circle.exp Real.pi

@[simp] theorem coe_negOne : ((negOne : Circle) : ℂ) = -1 := by
  simp [negOne, Circle.exp, Complex.exp_pi_mul_I]

theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  have h2 : ((negOne : Circle) : ℂ) = ((1 : Circle) : ℂ) := congrArg _ h
  rw [coe_negOne] at h2
  norm_num at h2

@[simp] theorem negOne_sq : negOne ^ 2 = 1 := by
  rw [← Circle.coe_inj]
  push_cast
  rw [coe_negOne]
  norm_num

/-- Squaring, as a group homomorphism of the circle group. -/
noncomputable def sqHom : Circle →* Circle := powMonoidHom 2

@[simp] theorem sqHom_apply (z : Circle) : sqHom z = z ^ 2 := rfl

/-- Squaring is continuous. -/
theorem sqHom_continuous : Continuous fun z : Circle => sqHom z := by
  simpa [sqHom_apply] using (continuous_id.pow 2 : Continuous fun z : Circle => z ^ 2)

/-- Squaring is surjective: every element of the circle has a square root. -/
theorem sqHom_surjective : Function.Surjective sqHom := by
  intro w
  refine ⟨Circle.exp ((w : ℂ).arg / 2), ?_⟩
  have h : Circle.exp ((w : ℂ).arg / 2) ^ 2 = Circle.exp ((w : ℂ).arg) := by
    rw [sq, ← Circle.exp_add]; ring_nf
  rw [sqHom_apply, h, Circle.exp_arg]

/-- The square roots of `1` are exactly `1` and `-1`. -/
theorem sq_eq_one_iff (x : Circle) : x ^ 2 = 1 ↔ x = 1 ∨ x = negOne := by
  constructor
  · intro h
    have hx : (x : ℂ) ^ 2 = 1 := by
      have := congrArg (fun y : Circle => (y : ℂ)) h
      simpa using this
    have hfac : ((x : ℂ) - 1) * ((x : ℂ) + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 hfac with h1 | h1
    · left
      rw [← Circle.coe_inj]
      push_cast
      linear_combination h1
    · right
      rw [← Circle.coe_inj, coe_negOne]
      linear_combination h1
  · rintro (rfl | rfl)
    · simp
    · exact negOne_sq

/-- The kernel of squaring is the two-element subgroup `{1, -1}`. -/
theorem ker_sqHom : (sqHom.ker : Set Circle) = {1, negOne} := by
  ext x
  simp [MonoidHom.mem_ker, sq_eq_one_iff, Set.mem_insert_iff]

/-- **Every fibre has exactly two elements.**  The circle squaring map is a
genuine two-to-one cover. -/
theorem sq_fiber_exact (w : Circle) :
    ∃ a b : Circle, a ≠ b ∧ a ^ 2 = w ∧ b ^ 2 = w ∧
      ∀ c : Circle, c ^ 2 = w → c = a ∨ c = b := by
  obtain ⟨a, ha⟩ := sqHom_surjective w
  rw [sqHom_apply] at ha
  refine ⟨a, negOne * a, ?_, ha, ?_, ?_⟩
  · intro h
    have h1 : (1 : Circle) = negOne :=
      mul_right_cancel (b := a) (a := (1 : Circle)) (c := negOne) (by simpa using h)
    exact negOne_ne_one h1.symm
  · rw [mul_pow, negOne_sq, one_mul, ha]
  · intro c hc
    have hq : (c * a⁻¹) ^ 2 = 1 := by
      rw [mul_pow, hc, ← ha]
      simp [inv_pow]
    rcases (sq_eq_one_iff _).1 hq with h | h
    · exact Or.inl (mul_right_cancel (b := a⁻¹) (a := c) (c := a) (by simpa using h))
    · exact Or.inr (mul_right_cancel (b := a⁻¹) (a := c) (c := negOne * a)
        (by rw [h]; group))

/-- The circle group is infinite, so this cover is not a finite model. -/
instance instInfiniteCircle : Infinite Circle := by
  haveI : Infinite (Set.Ioo (0:ℝ) 1) := (Set.Ioo_infinite (by norm_num)).to_subtype
  refine Infinite.of_injective (fun x : Set.Ioo (0:ℝ) 1 => Circle.exp x) ?_
  intro a b hab
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hab
  obtain ⟨a1, a2⟩ := a.2
  obtain ⟨b1, b2⟩ := b.2
  have hpi : (3:ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hm0 : m = 0 := by
    by_contra h0
    have h1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have h := Int.one_le_abs (z := m) (by omega)
      have h' := (Int.cast_le (R := ℝ)).2 h
      rwa [Int.cast_abs, Int.cast_one] at h'
    have h2 : |(a:ℝ) - (b:ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
    have h3 : (a:ℝ) - (b:ℝ) = (m:ℝ) * (2*Real.pi) := by linarith [hm]
    rw [h3, abs_mul, abs_of_pos (show (0:ℝ) < 2*Real.pi by linarith)] at h2
    nlinarith
  rw [hm0] at hm
  simp at hm
  exact Subtype.ext hm

/-- The spin interface instantiated by the circle squaring cover. -/
noncomputable def circleSpinEmergence : SpinEmergenceAxioms.{0} where
  QuadraticForm := PUnit
  Signature31 := PUnit.unit
  CliffordAlgebra := fun _ => PUnit
  SpinGroup := Circle
  SO := fun _ _ => Circle
  SpinIsDoubleCover := fun z => z ^ 2

/-- **The spin interface admits a continuous, infinite, genuinely two-to-one
instance.**  Complementing the finite quaternion instance of
`Synthesis.SpinCoverBridge`, the cover field here is the squaring map of the
circle group: its carriers are infinite topological groups and every fibre has
exactly two elements.  This is a statement about the interface, not about
`Spin(3,1) → SO⁺(3,1)`. -/
theorem spin_interface_satisfiable_with_continuous_cover :
    ∃ (A : SpinEmergenceAxioms.{0}) (_ : TopologicalSpace A.SpinGroup)
      (_ : TopologicalSpace (A.SO 3 1)),
      Continuous A.SpinIsDoubleCover ∧ Infinite A.SpinGroup ∧ Infinite (A.SO 3 1) ∧
      ∀ x : A.SO 3 1, ∃ a b : A.SpinGroup, a ≠ b ∧
        A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x ∧
        ∀ c : A.SpinGroup, A.SpinIsDoubleCover c = x → c = a ∨ c = b :=
  ⟨circleSpinEmergence, inferInstanceAs (TopologicalSpace Circle),
    inferInstanceAs (TopologicalSpace Circle), sqHom_continuous,
    instInfiniteCircle, instInfiniteCircle, fun x => sq_fiber_exact x⟩

end Synthesis.CircleCover
