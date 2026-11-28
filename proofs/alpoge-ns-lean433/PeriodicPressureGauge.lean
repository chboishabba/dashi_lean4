import Mathlib

/-! Periodic pressure gauge for the original velocity-only torus clause.
The spatial pressure increment is constant when its derivative is
periodic. This file is the fixed-time geometric part; the time-dependent
accelerating-frame PDE transport is recorded separately in the roadmap.
-/
namespace DASHI.AlpogeBuckmaster

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pressure_increment_constant (p : E → ℝ)
    (hp : Differentiable ℝ p) (e : E)
    (hper : ∀ x, fderiv ℝ p (x+e)=fderiv ℝ p x) :
    ∀ x, p (x+e)-p x=p e-p 0 := by
  let f : E → ℝ := fun x => p (x+e)-p x
  have hshift (x : E) :
      HasFDerivAt (fun y : E => p (y+e)) (fderiv ℝ p (x+e)) x := by
    have h := (hp (x+e)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const e)
    simpa [Function.comp_def] using h
  have hf (x : E) : HasFDerivAt f 0 x := by
    have h := (hshift x).sub (hp x).hasFDerivAt
    rw [hper,sub_self] at h
    exact h
  have he : f = fun _ => f 0 :=
    eq_of_fderiv_eq (fun x => (hf x).differentiableAt)
      differentiable_const (fun x => by rw [(hf x).fderiv,fderiv_const]) 0 rfl
  intro x
  have h := congrFun he x
  simpa [f] using h

/-- Correct a periodic-gradient pressure by the unique affine function
with the same lattice increments. The value at zero is irrelevant. -/
theorem pressure_remove_affine_periodic (p : E → ℝ)
    (hp : Differentiable ℝ p) (e : E) (L : E →L[ℝ] ℝ)
    (hper : ∀ x, fderiv ℝ p (x+e)=fderiv ℝ p x)
    (hL : L e=p e-p 0) :
    ∀ x, p (x+e)-L (x+e)=p x-L x := by
  intro x
  rw [map_add,hL]
  have h := pressure_increment_constant p hp e hper x
  linarith

/-- Pointwise signed cancellation in the moving frame. All velocity,
advection and pressure terms are retained, including frame acceleration. -/
theorem accelerating_frame_balance {V : Type*} [AddCommGroup V]
    (ut adv visc grad cross acc : V)
    (h : ut+adv=visc-grad) :
    (ut+cross-acc)+(adv-cross)=visc-(grad+acc) := by
  calc
    (ut+cross-acc)+(adv-cross) = (ut+adv)-acc := by abel
    _ = visc-(grad+acc) := by rw [h]; abel

end DASHI.AlpogeBuckmaster
