import Integration.Paper9CMOriginalMachinWindow
import Integration.Paper9ScalarReciprocal

/-! SOURCE-WRITTEN, UNCOMPILED.
A4 normalized cusp window. Retain the original signed q, Machin
dyadic endpoints and original E4/E6. Avoid tiny discriminant division.
The exp-tail and original Fourier majorant reflection remain explicit.
-/
namespace Integration.Paper9CMNormalizedCuspWindow
open Complex
open scoped BigOperators
open Integration.Paper9CMOriginalMachinWindow
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualCMRoot
open Integration.Paper9CMShiftCheck
open Integration.Paper9ExecutableCM163

def xLo : ℚ := (piLo:ℚ)*(sqrtLo:ℚ)/(scale:ℚ)^2
def xHi : ℚ := (piHi:ℚ)*(sqrtHi:ℚ)/(scale:ℚ)^2

def expPrefix (x : ℚ) : ℚ :=
  ∑ n ∈ Finset.range 180, x^n/(n.factorial:ℚ)
def expUpper (x : ℚ) : ℚ :=
  expPrefix x+2*x^180/(Nat.factorial 180:ℚ)

def expWindowOK : Prop :=
  0≤xLo ∧ xLo≤xHi ∧ 2*xHi<181 ∧
  (640320:ℚ)^3+744-1/4<expPrefix xLo ∧
  expUpper xHi<(640320:ℚ)^3+744+1/4

instance : Decidable expWindowOK := by unfold expWindowOK; infer_instance

-- The existing exponential and Fourier analytic owners must bind
-- these actual values to the checked rational inequalities.
noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem halfUnitFromCusp (J : ℂ) (e : ℝ)
    (he : |e-((640320:ℝ)^3+744)|≤1/4)
    (hj : ‖J+(e:ℂ)-744‖≤1/4) :
    |J.re+(640320:ℝ)^3|≤1/2 := by
  have h := (Complex.abs_re_le_norm (J+(e:ℂ)-744)).trans hj
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.natCast_re] at h
  rw [abs_le] at h he ⊢
  constructor <;> linarith [h.1,h.2,he.1,he.2]

theorem actualHalfUnit (he :
    |Real.exp (Real.pi*root163)-((640320:ℝ)^3+744)|≤1/4)
    (hj : ‖j cmTau+(Real.exp (Real.pi*root163):ℂ)-744‖≤1/4) :
    |(j cmTau).re-(K:ℝ)|≤1/2 := by
  have h := halfUnitFromCusp (j cmTau) _ he hj
  norm_num [K] at h ⊢
  exact h

theorem rootFromCuspChecks (hu : unitOK=true) (hd : diagOK=true)
    (hs : shiftOK=true)
    (he : |Real.exp (Real.pi*root163)-((640320:ℝ)^3+744)|≤1/4)
    (hj : ‖j cmTau+(Real.exp (Real.pi*root163):ℂ)-744‖≤1/4) :
    j cmTau=(K:ℂ) :=
  rootOfChecks hu hd hs (actualHalfUnit he hj)

end
end Integration.Paper9CMNormalizedCuspWindow
