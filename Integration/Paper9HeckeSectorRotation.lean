import Integration.Paper9HeckeProductAssembly
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots

/-! SOURCE-WRITTEN, UNCOMPILED. Actual phase rotation of the ORIGINAL
normalized polynomial residuals. This removes the off-sector coefficient
premise from the existing packet consumer; the 83 and 43 on-sector
integer recurrence reflections remain explicit. -/
namespace Integration.Paper9HeckeSectorRotation

open Complex Polynomial
open scoped BigOperators
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9HeckeProductAssembly

noncomputable section

def ζ : ℂ := phase (1 : Fin 41)

theorem zetaPow : ζ^41=1 := phasePower (1 : Fin 41)

theorem zetaNeOne : ζ≠1 := by
  intro h
  change Complex.exp (2*Real.pi*Complex.I*(1:Fin 41).val/41)=1 at h
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp h
  have hi := congrArg Complex.im hk
  simp [Complex.mul_im,Complex.div_im] at hi
  have hp : 0 < Real.pi := Real.pi_pos
  have he : (k:ℝ)=1/41 := by
    apply (mul_left_cancel₀ (show (2*Real.pi:ℝ)≠0 by positivity))
    nlinarith
  have h0 : (0:ℤ)<k := by exact_mod_cast (show (0:ℝ)<(k:ℝ) by linarith)
  have h1 : k<(1:ℤ) := by exact_mod_cast (show (k:ℝ)<1 by linarith)
  omega

theorem zetaPrimitive : IsPrimitiveRoot ζ 41 := by
  have hd : orderOf ζ ∣ 41 := orderOf_dvd_of_pow_eq_one zetaPow
  have hp : Nat.Prime 41 := by decide
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact (zetaNeOne (orderOf_eq_one_iff.mp h)).elim
  · simpa [h] using IsPrimitiveRoot.orderOf ζ

-- The primitive phase is the original complex exponential, not a
-- separately chosen abstract root of unity.
theorem phaseAsPower (a : Fin 41) : phase a=ζ^a.val := by
  unfold phase ζ
  rw [← Complex.exp_nat_mul]
  congr 1
  simp
  ring

def next (a : Fin 41) : Fin 41 := ⟨(a.val+1)%41,by omega⟩
def prev (a : Fin 41) : Fin 41 := ⟨(a.val+40)%41,by omega⟩

theorem cycleInverse : ∀ a : Fin 41, prev (next a)=a ∧ next (prev a)=a := by decide

def cycle : Equiv.Perm (Fin 41) where
  toFun := next
  invFun := prev
  left_inv a := (cycleInverse a).1
  right_inv a := (cycleInverse a).2

theorem phaseNext (a : Fin 41) : phase a*ζ=phase (cycle a) := by
  rw [phaseAsPower,phaseAsPower,← pow_succ]
  have h : a.val+1=(cycle a).val ∨ a.val+1=41 ∧ (cycle a).val=0 := by
    change a.val+1=(a.val+1)%41 ∨ a.val+1=41 ∧ (a.val+1)%41=0
    omega
  rcases h with h | ⟨h,h0⟩
  · rw [h]
  · rw [h,h0,zetaPow,pow_zero]

theorem qRotation (z : ℂ) : (ζ*z)^41=z^41 := by rw [mul_pow,zetaPow,one_mul]

theorem diagonalRotation (V : ℂ → ℂ) (z : ℂ) :
    diagonalNormalized V (ζ*z)=diagonalNormalized V z := by
  unfold diagonalNormalized
  rw [qRotation]
  congr 1
  calc
    _ = ∏ a : Fin 41, (V (z^41)-(phase (cycle a)*z)^40*V (phase (cycle a)*z)) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [← mul_assoc,phaseNext]
    _ = _ := cycle.prod_comp (fun a => V (z^41)-(phase a*z)^40*V (phase a*z))

theorem sliceRotation (V : ℂ → ℂ) (K z : ℂ) :
    sliceNormalized V K (ζ*z)=sliceNormalized V K z := by
  unfold sliceNormalized
  rw [qRotation]
  congr 1
  calc
    _ = ∏ a : Fin 41, (V (phase (cycle a)*z)-K*(phase (cycle a)*z)) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [← mul_assoc,phaseNext]
    _ = _ := cycle.prod_comp (fun a => V (phase a*z)-K*(phase a*z))

theorem columnRotation (V : ℂ → ℂ) (d : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    normalizedColumnEval V d c (ζ*z)=normalizedColumnEval V d c z := by
  unfold normalizedColumnEval
  rw [qRotation]

-- Coefficient action of the actual ramified rotation. No approximation
-- of ζ, and no arbitrary equality of coefficients.
theorem scaleCoeff (P : Polynomial ℂ) (s : ℂ) (n : ℕ) :
    (P.comp (Polynomial.C s*Polynomial.X)).coeff n=s^n*P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.add_comp,Polynomial.coeff_add,hP,hQ,Polynomial.coeff_add,mul_add]
  | monomial k a =>
    rw [Polynomial.monomial_comp,mul_pow,← Polynomial.C_pow,← mul_assoc,← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial]
    by_cases h : k=n
    · subst k
      simp [mul_comm]
    · simp [Polynomial.coeff_monomial,h]

theorem coeffCovariance (P : Polynomial ℂ) (h : ∀ z, P.eval (ζ*z)=P.eval z) :
    ∀ n, ζ^n*P.coeff n=P.coeff n := by
  have hp : P.comp (Polynomial.C ζ*Polynomial.X)=P := by
    apply Polynomial.funext
    intro z
    simpa [Polynomial.eval_comp] using h z
  intro n
  rw [← scaleCoeff, hp]

theorem diagonalCovariance (m d : ℕ) (c : ℕ → ℂ) :
    ∀ n, ζ^n*(diagonalPoly m-columnPoly m d c).coeff n=
      (diagonalPoly m-columnPoly m d c).coeff n := by
  apply coeffCovariance
  intro z
  simp only [Polynomial.eval_sub,diagonalPolyEval,columnPolyEval,
    diagonalRotation,columnRotation]

theorem sliceCovariance (m d : ℕ) (K : ℂ) (c : ℕ → ℂ) :
    ∀ n, ζ^n*(slicePoly m K-columnPoly m d c).coeff n=
      (slicePoly m K-columnPoly m d c).coeff n := by
  apply coeffCovariance
  intro z
  simp only [Polynomial.eval_sub,slicePolyEval,columnPolyEval,
    sliceRotation,columnRotation]

-- Exact original analytic identities from ONLY the on-sector packet.
theorem diagonalFromSector (c : ℕ → ℂ)
    (h : ∀ i≤82, (diagonalPoly 3322-columnPoly 3322 82 c).coeff (41*i)=0) :
    ∀ τ, Integration.Paper9Hecke41ChartGeometry.actualProduct τ
      (Integration.MoonshineEisensteinAgdaTarget.jTarget τ)=
      (packet 82 c).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ) := by
  apply diagonalFromCoefficients
  exact sectorPacketZero ζ 41 82 _ (by decide) zetaPrimitive (diagonalCovariance _ _ _) h

theorem sliceFromSector (K : ℂ) (c : ℕ → ℂ)
    (h : ∀ i≤42, (slicePoly 1722 K-columnPoly 1722 42 c).coeff (41*i)=0) :
    ∀ τ, Integration.Paper9Hecke41ChartGeometry.actualProduct τ K=
      (packet 42 c).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ) := by
  apply sliceFromCoefficients
  exact sectorPacketZero ζ 41 42 _ (by decide) zetaPrimitive (sliceCovariance _ _ _ _) h

end
end Integration.Paper9HeckeSectorRotation
