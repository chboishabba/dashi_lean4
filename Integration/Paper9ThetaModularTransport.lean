import Integration.Paper9ThetaShellCoefficientWeld
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Integration.MoonshineEta24CuspPinned

/-! SOURCE-WRITTEN, kernel pending. Classical theta transformations
from Mathlib's original two-variable theta and Poisson functional
equation. DASHI contribution: signed fourth-power sheet readout and
transport to the original level-one modular-form interfaces.
No Jacobi quartic identity is required to prove these S/T laws. -/
namespace Integration.Paper9ThetaModularTransport
open Complex Filter Function UpperHalfPlane ModularGroup ModularForm
open SlashInvariantForm SlashInvariantFormClass
open scoped MatrixGroups Real Topology Manifold
noncomputable section

def p : ℂ := Real.pi * Complex.I
def th3 (z : ℂ) : ℂ := jacobiTheta₂ 0 z
def th4 (z : ℂ) : ℂ := jacobiTheta₂ (1/2) z
def th2 (z : ℂ) : ℂ := Complex.exp (p*z/4)*jacobiTheta₂ (z/2) z

def A (z : ℂ) := th2 z ^ 4
def B (z : ℂ) := th3 z ^ 4
def C (z : ℂ) := th4 z ^ 4

def thetaE4 (z : ℂ) := (A z^2+B z^2+C z^2)/2
def thetaE6 (z : ℂ) := (A z+B z)*(B z+C z)*(C z-A z)/2

def sFactor (z : ℂ) : ℂ := (-Complex.I*z)^(1/2:ℂ)

theorem sFactorNonzero {z : ℂ} (hz : z≠0) : sFactor z≠0 := by
  unfold sFactor
  exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num : (1/2:ℂ)≠0) |>.2
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz)

theorem sFactorFourth (z : ℂ) : sFactor z^4 = -z^2 := by
  unfold sFactor
  rw [← Complex.cpow_mul_nat]
  rw [show (1/2:ℂ)*(4:ℕ)=(2:ℂ) by norm_num, Complex.cpow_two]
  rw [mul_pow, neg_pow, Complex.I_sq]
  norm_num

-- Solve the actual Poisson equation backwards, keeping the same
-- square root on all three sheets before raising to fourth powers.
theorem thetaS (u z : ℂ) (hz : z≠0) :
    jacobiTheta₂ (u/z) (-1/z) =
      sFactor z*Complex.exp (p*u^2/z)*jacobiTheta₂ u z := by
  have h := jacobiTheta₂_functional_equation u z
  have hs := sFactorNonzero hz
  change jacobiTheta₂ u z =
    1/sFactor z * Complex.exp (-p*u^2/z) *
      jacobiTheta₂ (u/z) (-1/z) at h
  have he : Complex.exp (p*u^2/z)*Complex.exp (-p*u^2/z)=1 := by
    rw [← Complex.exp_add]
    simp [show p*u^2/z+(-p*u^2/z)=0 by ring]
  calc
    _ = (sFactor z*(1/sFactor z))*
        (Complex.exp (p*u^2/z)*Complex.exp (-p*u^2/z))*
          jacobiTheta₂ (u/z) (-1/z) := by simp [hs,he]
    _ = _ := by rw [h]; ring

theorem th3S (z : ℂ) (hz : z≠0) :
    th3 (-1/z)=sFactor z*th3 z := by
  simpa [th3] using thetaS 0 z hz

theorem th4S (z : ℂ) (hz : z≠0) :
    th4 (-1/z)=sFactor z*th2 z := by
  have h := thetaS (z/2) z hz
  rw [show (z/2)/z=1/2 by field_simp [hz]; ring] at h
  rw [show p*(z/2)^2/z=p*z/4 by field_simp [hz]; ring] at h
  simpa [th4,th2,mul_assoc] using h

theorem th2S (z : ℂ) (hz : z≠0) :
    th2 (-1/z)=sFactor z*th4 z := by
  have h := thetaS (1/2) z hz
  unfold th2 th4
  rw [show (-1/z)/2= -((1/2)/z) by ring, jacobiTheta₂_neg_left,h]
  have he : Complex.exp (p*(-1/z)/4)*Complex.exp (p*(1/2)^2/z)=1 := by
    rw [← Complex.exp_add]
    rw [show p*(-1/z)/4+p*(1/2)^2/z=0 by ring]
    simp
  calc
    _ = sFactor z*(Complex.exp (p*(-1/z)/4)*Complex.exp (p*(1/2)^2/z))*
        jacobiTheta₂ (1/2) z := by ring
    _ = _ := by rw [he,mul_one]

-- T is the retained parity character. Difference of the two literal
-- exponents is an even integer times pi*i.
theorem phaseEven (n : ℤ) :
    Complex.exp (p*((n:ℂ)^2-n))=1 := by
  have hp := Integration.Paper9ThetaHadamardGeometry.squareParity n
  have hk : n^2-n=2*((n^2-n)/2) := by omega
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨(n^2-n)/2,?_⟩
  have hkc : (n:ℂ)^2-n=2*(((n^2-n)/2 : ℤ):ℂ) := by exact_mod_cast hk
  rw [hkc]
  unfold p
  ring

theorem thetaT (u z : ℂ) :
    jacobiTheta₂ u (z+1)=jacobiTheta₂ (u+1/2) z := by
  unfold jacobiTheta₂
  apply tsum_congr
  intro n
  unfold jacobiTheta₂_term
  rw [show 2*(Real.pi:ℂ)*Complex.I*n*u+
      (Real.pi:ℂ)*Complex.I*(n:ℂ)^2*(z+1) =
      (2*(Real.pi:ℂ)*Complex.I*n*(u+1/2)+
      (Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z)+p*((n:ℂ)^2-n)
      by unfold p; ring,Complex.exp_add,phaseEven,mul_one]

theorem th3T (z : ℂ) : th3 (z+1)=th4 z := by
  simpa [th3,th4] using thetaT 0 z

theorem th4T (z : ℂ) : th4 (z+1)=th3 z := by
  unfold th4 th3
  rw [thetaT,show (1/2:ℂ)+1/2=0+1 by norm_num,jacobiTheta₂_add_left]

theorem th2T (z : ℂ) : th2 (z+1)=Complex.exp (p/4)*th2 z := by
  unfold th2
  rw [thetaT,show (z+1)/2+1/2=z/2+1 by ring,jacobiTheta₂_add_left]
  rw [show p*(z+1)/4=p/4+p*z/4 by ring,Complex.exp_add]
  ring

theorem phaseFourth : Complex.exp (p/4)^4 = -1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (4:ℂ)*(p/4)=p by ring]
  exact Complex.exp_pi_mul_I

theorem sheetsS (z : ℂ) (hz : z≠0) :
    A (-1/z)= -z^2*C z ∧ B (-1/z)= -z^2*B z ∧
      C (-1/z)= -z^2*A z := by
  unfold A B C
  rw [th2S z hz,th3S z hz,th4S z hz]
  simp only [mul_pow,sFactorFourth,and_self]

theorem sheetsT (z : ℂ) :
    A (z+1)= -A z ∧ B (z+1)=C z ∧ C (z+1)=B z := by
  unfold A B C
  rw [th2T,th3T,th4T,mul_pow,phaseFourth]
  simp

theorem E4S (z : ℂ) (hz : z≠0) :
    thetaE4 (-1/z)=z^4*thetaE4 z := by
  obtain ⟨ha,hb,hc⟩ := sheetsS z hz
  unfold thetaE4
  rw [ha,hb,hc]
  ring

theorem E6S (z : ℂ) (hz : z≠0) :
    thetaE6 (-1/z)=z^6*thetaE6 z := by
  obtain ⟨ha,hb,hc⟩ := sheetsS z hz
  unfold thetaE6
  rw [ha,hb,hc]
  ring

theorem E4T (z : ℂ) : thetaE4 (z+1)=thetaE4 z := by
  obtain ⟨ha,hb,hc⟩ := sheetsT z
  unfold thetaE4
  rw [ha,hb,hc]
  ring

theorem E6T (z : ℂ) : thetaE6 (z+1)=thetaE6 z := by
  obtain ⟨ha,hb,hc⟩ := sheetsT z
  unfold thetaE6
  rw [ha,hb,hc]
  ring

theorem th3Differentiable (z : ℍ) : DifferentiableAt ℂ th3 (z:ℂ) :=
  differentiableAt_jacobiTheta₂_snd 0 z.2

theorem th4Differentiable (z : ℍ) : DifferentiableAt ℂ th4 (z:ℂ) :=
  differentiableAt_jacobiTheta₂_snd (1/2) z.2

theorem th2Differentiable (z : ℍ) : DifferentiableAt ℂ th2 (z:ℂ) := by
  have h := (hasFDerivAt_jacobiTheta₂ ((z:ℂ)/2) z.2).differentiableAt
  have h' := h.comp (z:ℂ)
    (show DifferentiableAt ℂ (fun w : ℂ => (w/2,w)) z by fun_prop)
  unfold th2
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (p*w/4)) z).mul h'

theorem E4Differentiable (z : ℍ) : DifferentiableAt ℂ thetaE4 (z:ℂ) := by
  have ha := (th2Differentiable z).pow 4
  have hb := (th3Differentiable z).pow 4
  have hc := (th4Differentiable z).pow 4
  unfold thetaE4 A B C
  exact (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)).div_const 2

theorem E6Differentiable (z : ℍ) : DifferentiableAt ℂ thetaE6 (z:ℂ) := by
  have ha := (th2Differentiable z).pow 4
  have hb := (th3Differentiable z).pow 4
  have hc := (th4Differentiable z).pow 4
  unfold thetaE6 A B C
  exact (((ha.add hb).mul (hb.add hc)).mul (hc.sub ha)).div_const 2

def at4 (z : ℍ) := thetaE4 z
def at6 (z : ℍ) := thetaE6 z

-- Reuse the repository's existing pinned generator theorem.
theorem slashFromST (f : ℂ → ℂ) (k : ℕ)
    (hS : ∀ z : ℍ, f (-1/(z:ℂ))=(z:ℂ)^k*f z)
    (hT : ∀ z : ℍ, f ((z:ℂ)+1)=f z) :
    ∀ γ : SL(2,ℤ), (fun z : ℍ => f z) ∣[(k:ℤ)] γ = fun z : ℍ => f z := by
  apply Integration.MoonshineEta24CuspPinned.slash_action_generators_SL2Z
  · funext z
    rw [SlashInvariantForm.SL_slash_apply]
    simp only [ModularGroup.denom_S,UpperHalfPlane.modular_S_smul,zpow_neg,zpow_natCast]
    rw [hS z]
    field_simp [z.ne_zero] <;> ring
  · funext z
    rw [SlashInvariantForm.SL_slash_apply]
    simpa [ModularGroup.denom_T,UpperHalfPlane.modular_T_smul] using hT z

theorem slash4 (γ : SL(2,ℤ)) : at4 ∣[(4:ℤ)] γ=at4 :=
  slashFromST thetaE4 4 (fun z => E4S z z.ne_zero) (fun z => E4T z) γ

theorem slash6 (γ : SL(2,ℤ)) : at6 ∣[(6:ℤ)] γ=at6 :=
  slashFromST thetaE6 6 (fun z => E6S z z.ne_zero) (fun z => E6T z) γ

#print axioms sheetsS
#print axioms sheetsT
#print axioms slash4
#print axioms slash6
end
end Integration.Paper9ThetaModularTransport
