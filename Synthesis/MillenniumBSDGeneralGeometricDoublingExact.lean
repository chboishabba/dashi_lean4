import Synthesis.MillenniumBSDOriginalPlaceSelmerShaExact
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Geometric doubling onto for the original GENERAL Weierstrass curve.
Reverse solve the tangent through -P. Its slope is a root of a monic
quartic, so algebraic closure supplies the slope without a selected
CM model or an assumed isogeny theorem. Classical chord-tangent
construction; native DASHI attachment to the original point group.
-/
namespace BSDCohomology
open WeierstrassCurve Polynomial
noncomputable section

variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

def halfX (x m : F) : F :=
  (m^2+W.a₁*m-W.a₂-x)/2

def halfY (x y m : F) : F :=
  W.toAffine.negY x y+m*(halfX W x m-x)

def tangentResidual (x y m : F) : F :=
  3*(halfX W x m)^2+2*W.a₂*halfX W x m+W.a₄-W.a₁*halfY W x y m-
    m*(2*halfY W x y m+W.a₁*halfX W x m+W.a₃)

def slopeQuartic (x y : F) : F[X] :=
  X^4+C (2*W.a₁)*X^3+C (W.a₁^2-2*W.a₂-6*x)*X^2+
    C (-2*W.a₁*W.a₂-10*W.a₁*x-4*W.a₃-8*y)*X+
    C (-4*W.a₁^2*x-4*W.a₁*W.a₃-4*W.a₁*y+
      W.a₂^2-2*W.a₂*x-4*W.a₄-3*x^2)

theorem slopeQuartic_eval (x y m : F) :
    (slopeQuartic W x y).eval m = -4*tangentResidual W x y m := by
  simp [slopeQuartic,tangentResidual,halfX,halfY,WeierstrassCurve.Affine.negY]
  ring

theorem slopeQuartic_degree_ne_zero (x y : F) :
    (slopeQuartic W x y).degree ≠ 0 := by
  have hc : (slopeQuartic W x y).coeff 4=1 := by
    simp [slopeQuartic,Polynomial.coeff_add,Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow,Polynomial.coeff_X,Polynomial.coeff_C]
  have hd := Polynomial.le_degree_of_ne_zero (p:=slopeQuartic W x y)
    (n:=4) (by rw [hc]; exact one_ne_zero)
  intro h
  rw [h] at hd
  norm_num at hd

def curveResidual (x y : F) :=
  y^2+W.a₁*x*y+W.a₃*y-(x^3+W.a₂*x^2+W.a₄*x+W.a₆)

theorem half_curve_residual (x y m : F) :
    curveResidual W (halfX W x m) (halfY W x y m)-curveResidual W x y =
      (x-halfX W x m)*tangentResidual W x y m := by
  unfold curveResidual tangentResidual halfX halfY WeierstrassCurve.Affine.negY
  ring

/-- A root of the monic slope quartic realizes the actual doubling,
including the flex case x_Q=x_P. Nonsingularity excludes the spurious
vertical-tangent denominator zero, rather than dividing by assumption. -/
theorem half_of_slope_root (x y m : F) (hP : W.toAffine.Nonsingular x y)
    (hm : (slopeQuartic W x y).eval m=0) :
    ∃ Q : W.toAffine.Point, Q+Q=WeierstrassCurve.Affine.Point.some hP := by
  let Xq := halfX W x m
  let Yq := halfY W x y m
  have ht : tangentResidual W x y m=0 := by
    rw [slopeQuartic_eval] at hm
    exact (mul_eq_zero.mp hm).resolve_left (by norm_num)
  have hP0 : curveResidual W x y=0 := by
    exact (W.toAffine.equation_iff' x y).mp
      ((W.toAffine.nonsingular_iff' x y).mp hP).1
  have hQ0 : curveResidual W Xq Yq=0 := by
    have he := half_curve_residual W x y m
    rw [ht,mul_zero,hP0,sub_zero] at he
    exact he
  have hQ : W.toAffine.Nonsingular Xq Yq :=
    W.equation_iff_nonsingular.mp ((W.toAffine.equation_iff' Xq Yq).mpr hQ0)
  have ht' : 3*Xq^2+2*W.a₂*Xq+W.a₄-W.a₁*Yq =
      m*(2*Yq+W.a₁*Xq+W.a₃) := sub_eq_zero.mp ht
  have hn : 2*Yq+W.a₁*Xq+W.a₃≠0 := by
    intro hz
    have hs := (W.toAffine.nonsingular_iff' Xq Yq).mp hQ
    rw [hz,mul_zero] at ht'
    rcases hs.2 with h | h
    · apply h
      linear_combination -ht'
    · exact h hz
  have hneg : Yq≠W.toAffine.negY Xq Yq := by
    intro h
    apply hn
    unfold WeierstrassCurve.Affine.negY at h
    linear_combination h
  have hsl : W.toAffine.slope Xq Xq Yq Yq=m := by
    rw [W.toAffine.slope_of_Y_ne rfl hneg]
    apply (div_eq_iff (sub_ne_zero.mpr hneg)).mpr
    unfold WeierstrassCurve.Affine.negY
    linear_combination ht'
  have hx : W.toAffine.addX Xq Xq m=x := by
    unfold WeierstrassCurve.Affine.addX Xq halfX
    ring
  have hy : W.toAffine.addY Xq Xq Yq m=y := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [hx]
    unfold Yq halfY WeierstrassCurve.Affine.negY
    ring
  refine ⟨.some hQ,?_⟩
  rw [WeierstrassCurve.Affine.Point.add_some (fun h=>hneg h.2)]
  simp only [hsl]
  -- Both output coordinates are the original target, with proof irrelevance
  -- for the nonsingularity witnesses.
  generalize W.toAffine.addX Xq Xq m = x' at *
  generalize W.toAffine.addY Xq Xq Yq m = y' at *
  subst x'
  subst y'
  rfl

theorem general_affine_doubling_onto [IsAlgClosed F] :
    Function.Surjective (fun Q : W.toAffine.Point => (2:ℕ) • Q) := by
  intro P
  cases P with
  | zero => exact ⟨0,by simp⟩
  | some x y hP =>
    obtain ⟨m,hm⟩ := IsAlgClosed.exists_root (slopeQuartic W x y)
      (slopeQuartic_degree_ne_zero W x y)
    obtain ⟨Q,hQ⟩ := half_of_slope_root W x y m hP hm
    exact ⟨Q,by simpa [two_nsmul] using hQ⟩

theorem general_geometric_doubling_onto {K : Type*} [Field K] [CharZero K]
    (V : WeierstrassCurve K) [V.IsElliptic] :
    Function.Surjective (fun Q : GeometricPoint V => (2:ℕ) • Q) :=
  general_affine_doubling_onto (V⁄(AlgebraicClosure K))

/-- Remove the explicit doubling hypotheses from the original
place-indexed Selmer quotient, using the same curve at every place. -/
def generalSelmerQuotientEquivShaTwo {K : Type*} [Field K] [NumberField K]
    (V : WeierstrassCurve K) [V.IsElliptic] :=
  selmerQuotientEquivShaTwo V (general_geometric_doubling_onto V)
    (fun v=>general_geometric_doubling_onto (localCurve V v))

end
end BSDCohomology
