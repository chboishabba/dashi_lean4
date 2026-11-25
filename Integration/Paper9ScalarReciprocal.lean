import Integration.Paper9MobiusDiskPeriod
import Integration.Paper9CMShiftCheck

/-! SOURCE-WRITTEN, UNCOMPILED. Scalar axis/diagonal reduction.
No bivariate analytic division, inverse j, or new Hecke carrier.
The local original-chart germ attachment is a separate obligation. -/
namespace Integration.Paper9ScalarReciprocal
open Complex Filter UpperHalfPlane
open scoped BigOperators Matrix Topology
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet
open Integration.Paper9Hecke41ChartGeometry hiding (a)
open Integration.Paper9OriginalCMChartWeld
open Integration.Paper9MobiusDiskPeriod

noncomputable section

-- T^-1 S, an integral determinant-one correction of original chart 0.
def reverseSL : SL(2, ℤ) :=
  ⟨!![-1,-1;1,0], by decide⟩

theorem reverseChartAt (τ : ℍ) :
    ((reverseSL • chartPoint 0 τ : ℍ) : ℂ) = reverseHecke τ := by
  rw [← slEval]
  have hτ : (τ : ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    simp at he
    linarith [τ.im_pos]
  have hc : (chartPoint 0 τ : ℂ) = (τ : ℂ)/41 := by
    simp [chartPoint]
  rw [hc]
  unfold eval numer denom reverseHecke reverseSL
  simp
  field_simp [hτ] <;> ring

local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem reverseChartValue (τ : ℍ) :
    chartValue 0 τ = jExt (reverseHecke τ) := by
  unfold chartValue
  rw [← jInvariant reverseSL (chartPoint 0 τ),
    ← jExtAt (reverseSL • chartPoint 0 τ), reverseChartAt]

theorem forwardChartValue (τ : ℍ) :
    chartValue 1 τ = jExt (hecke τ) := by
  unfold chartValue
  rw [← jInvariant ModularGroup.S (chartPoint 1 τ),
    ← jExtAt (ModularGroup.S • chartPoint 1 τ), heckeChartAt]

-- Preserve all remaining original chart indices and multiplicities.
def remaining : Finset Chart := (Finset.univ.erase 0).erase 1
theorem remainingCard : remaining.card = 40 := by decide

def restProduct (τ : ℍ) (Y : ℂ) : ℂ :=
  ∏ i ∈ remaining, (Y-chartValue i τ)

theorem productSplit (τ : ℍ) (Y : ℂ) :
    actualProduct τ Y =
      (Y-chartValue 0 τ)*(Y-chartValue 1 τ)*restProduct τ Y := by
  have h0 : (0 : Chart) ∈ (Finset.univ : Finset Chart) := Finset.mem_univ _
  have h1 : (1 : Chart) ∈ (Finset.univ : Finset Chart).erase 0 := by decide
  unfold actualProduct restProduct remaining
  rw [← Finset.mul_prod_erase _ _ h0, ← Finset.mul_prod_erase _ _ h1]
  ring

-- Polynomial difference as a finite telescoping sum, not division
-- by a potentially zero input. The recursion preserves multiplicity.
def prodAt (c : List ℂ) (Y : ℂ) : ℂ :=
  (c.map fun a => Y+a).prod

def diffAt : List ℂ → ℂ → ℂ
  | [], _ => 0
  | a :: c, Y => prodAt c Y + a*diffAt c Y

theorem productDifference (c : List ℂ) (Y : ℂ) :
    prodAt c Y - prodAt c 0 = Y*diffAt c Y := by
  induction c with
  | nil => simp [prodAt,diffAt]
  | cons a c ih =>
    simp only [prodAt,List.map_cons,List.prod_cons,zero_add] at ih ⊢
    change (Y+a)*prodAt c Y-a*prodAt c 0 =
      Y*(prodAt c Y+a*diffAt c Y)
    linear_combination a*ih

-- Normalized branch products on the two scalar lines. The remaining
-- factor may have zero entries; only A and S2 are canceled.
theorem scalarPeriodAlgebra (A B P2 P3 S2 S3 R0 R1 : ℂ)
    (hA : A≠0) (hS : S2≠0)
    (hs0 : S2*A^2=A^2*R0)
    (hp0 : P2*A^2=(163/41)*A^2*R0)
    (hs1 : S3*A^3+2*S2*A*B =
      -(81/41)*A*B*R0+A^2*R1)
    (hp1 : P3*A^3+2*P2*A*B =
      (163/41)*(1/41)*A*B*R0+(163/41)*A^2*(R1+A*S3)) :
    2*B/A^2=(41*P3-326*S3)/(163*S2) := by
  have hR : R0=S2 := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hA))
    linear_combination -hs0
  have hq : 41*P2=163*S2 := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hA))
    linear_combination 41*hp0-163*hs0
  rw [hR] at hs1 hp1
  have hh : A*((41*P3-326*S3)*A^2-326*S2*B)=0 := by
    linear_combination 41*hp1-163*hs1-2*A*B*hq
  have h := (mul_eq_zero.mp hh).resolve_left hA
  field_simp [hA,hS] <;> linear_combination -h

-- Scalar germ extraction, using only ordinary product/chain rules.
-- N,M are normalized branch products; T is the finite telescoping
-- polynomial quotient evaluated at x(w), with T(0)=S3.
theorem scalarGermPeriod
    (X N M p s R T : ℂ → ℂ)
    (A B P2 P3 S2 S3 R0 R1 T1 : ℂ)
    (hA : A≠0) (hS : S2≠0)
    (x0 : X 0=A) (n0 : N 0=A^2) (m0 : M 0=(163/41)*A^2)
    (p0 : p 0=P2) (s0 : s 0=S2) (r0 : R 0=R0) (t0 : T 0=S3)
    (hx : HasDerivAt X B 0)
    (hn : HasDerivAt N (-(81/41)*A*B) 0)
    (hm : HasDerivAt M ((163/41)*(1/41)*A*B) 0)
    (hp : HasDerivAt p (P3*A) 0)
    (hs : HasDerivAt s (S3*A) 0)
    (hr : HasDerivAt R R1 0)
    (ht : HasDerivAt T T1 0)
    (ha : (fun w => s w*(X w)^2) =ᶠ[𝓝 0] (fun w => N w*R w))
    (hd : (fun w => p w*(X w)^2) =ᶠ[𝓝 0]
      (fun w => M w*(R w+w*X w*T w))) :
    2*B/A^2=(41*P3-326*S3)/(163*S2) := by
  have h0 := ha.eq_of_nhds
  have h1 := hd.eq_of_nhds
  have haxis := ((hs.mul (hx.pow 2)).congr_of_eventuallyEq ha.symm).unique
    (hn.mul hr)
  have hdiag := ((hp.mul (hx.pow 2)).congr_of_eventuallyEq hd.symm).unique
    (hm.mul (hr.add (((hasDerivAt_id (0:ℂ)).mul hx).mul ht)))
  rw [s0,x0,n0,r0] at h0
  rw [p0,x0,m0,r0,t0] at h1
  rw [s0,x0,n0,r0] at haxis
  rw [p0,x0,m0,r0,t0] at hdiag
  simp at h1 haxis hdiag
  apply scalarPeriodAlgebra A B P2 P3 S2 S3 R0 R1 hA hS h0 h1
  · linear_combination haxis
  · linear_combination hdiag

-- Consume the scalar correction directly at the existing positive
-- period endpoint; no mixed cubic argument in this consumer.
theorem periodFromScalar (hj : j cmTau=-(640320:ℂ)^3)
    (P2 P3 S2 S3 R0 R1 : ℂ)
    (hS : S2≠0)
    (hκ : (41*P3-326*S3)/(163*S2)=
      -(77859659565707:ℂ)/19943834790540897829879824384000)
    (hs0 : S2*(a*d)^2=(a*d)^2*R0)
    (hp0 : P2*(a*d)^2=(163/41)*(a*d)^2*R0)
    (hs1 : S3*(a*d)^3+2*S2*(a*d)*(a*d+b*d^2/2) =
      -(81/41)*(a*d)*(a*d+b*d^2/2)*R0+(a*d)^2*R1)
    (hp1 : P3*(a*d)^3+2*P2*(a*d)*(a*d+b*d^2/2) =
      (163/41)*(1/41)*(a*d)*(a*d+b*d^2/2)*R0+
        (163/41)*(a*d)^2*(R1+(a*d)*S3)) :
    Tendsto (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N : ℂ))
      atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi : ℝ) : ℂ)) := by
  have ha := aNonzero hj
  have h := scalarPeriodAlgebra (a*d) (a*d+b*d^2/2) P2 P3 S2 S3 R0 R1
    (mul_ne_zero ha dNe) hS hs0 hp0 hs1 hp1
  rw [diskJetCorrection a b d ha dNe,hκ] at h
  apply Integration.Paper9SignedCMPeriod.actualLiteralPrefixPeriod hj
  exact h.symm

end
end Integration.Paper9ScalarReciprocal
