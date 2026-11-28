import Synthesis.YMCMP99Path13QuaternionExpTangentExact

namespace CMP99Pivot.Path13
open scoped Quaternion
noncomputable section

structure ActualSignedBond where
  q : Q
  h : Q
  negative : Bool

def ActualSignedBond.value (b : ActualSignedBond) : Q :=
  if b.negative then star b.q else b.q

def ActualSignedBond.velocity (b : ActualSignedBond) : Q :=
  if b.negative then -(b.h*star b.q) else b.q*b.h

def ActualSignedBond.curve (b : ActualSignedBond) (t : ℝ) : Q :=
  if b.negative then qNegativeBondCurve b.q b.h t else qBondCurve b.q b.h t

theorem ActualSignedBond.curve_zero (b : ActualSignedBond) :
    b.curve 0=b.value := by
  cases h : b.negative <;> simp [ActualSignedBond.curve,ActualSignedBond.value,h,
    qBondCurve,qNegativeBondCurve]

theorem ActualSignedBond.curve_derivative (b : ActualSignedBond) :
    HasDerivAt b.curve b.velocity 0 := by
  cases h : b.negative
  · simpa [ActualSignedBond.curve,ActualSignedBond.velocity,h,qLeft,qLeftLinear] using
      qBondCurve_derivative_zero b.q b.h
  · simpa [ActualSignedBond.curve,ActualSignedBond.velocity,h] using
      qNegativeBondCurve_derivative_zero b.q b.h

def actualWordCurve : List ActualSignedBond → ℝ → Q
  | [], _ => 1
  | b::bs, t => b.curve t*actualWordCurve bs t

def actualWordValue : List ActualSignedBond → Q
  | [] => 1
  | b::bs => b.value*actualWordValue bs

def actualWordVelocity : List ActualSignedBond → Q
  | [] => 0
  | b::bs => b.velocity*actualWordValue bs+b.value*actualWordVelocity bs

theorem actualWordCurve_zero (bs : List ActualSignedBond) :
    actualWordCurve bs 0=actualWordValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [actualWordCurve,actualWordValue,b.curve_zero,ih]

/-- Differentiate the actual ordered product, not a commutative proxy.
The suffix and prefix multiplication order is retained. -/
theorem actualWordCurve_derivative (bs : List ActualSignedBond) :
    HasDerivAt (actualWordCurve bs) (actualWordVelocity bs) 0 := by
  induction bs with
  | nil => simpa [actualWordCurve,actualWordVelocity] using hasDerivAt_const (0:ℝ) (1:Q)
  | cons b bs ih =>
    have h := b.curve_derivative.mul ih
    simpa [actualWordCurve,actualWordVelocity,b.curve_zero,actualWordCurve_zero,add_comm] using h

theorem actualWordValue_unit (bs : List ActualSignedBond)
    (hu : ∀ b∈bs,‖b.q‖=1) : ‖actualWordValue bs‖=1 := by
  induction bs with
  | nil => simp [actualWordValue]
  | cons b bs ih =>
    have hb := hu b List.mem_cons_self
    have ht := ih (fun c hc=>hu c (List.mem_cons_of_mem _ hc))
    cases h : b.negative <;> simp [actualWordValue,ActualSignedBond.value,h,norm_mul,norm_star,hb,ht]

/-- Actual word velocity is bounded by total paid bond velocity.
No assumption of commuting bonds or pure derivative directions. -/
theorem actualWordVelocity_bound (bs : List ActualSignedBond)
    (hu : ∀ b∈bs,‖b.q‖=1) :
    ‖actualWordVelocity bs‖≤(bs.map (fun b=>‖b.h‖)).sum := by
  induction bs with
  | nil => simp [actualWordVelocity]
  | cons b bs ih =>
    have hb := hu b List.mem_cons_self
    have ht := fun c hc=>hu c (List.mem_cons_of_mem _ hc)
    have hv : ‖b.value‖=1 := by
      cases h : b.negative <;> simp [ActualSignedBond.value,h,norm_star,hb]
    have hd : ‖b.velocity‖=‖b.h‖ := by
      cases h : b.negative <;> simp [ActualSignedBond.velocity,h,norm_mul,norm_star,hb]
    calc
      _ ≤ ‖b.velocity*actualWordValue bs‖+‖b.value*actualWordVelocity bs‖ := by
        exact norm_add_le _ _
      _ = ‖b.h‖+‖actualWordVelocity bs‖ := by
        rw [norm_mul,norm_mul,actualWordValue_unit bs ht,hv,hd,mul_one,one_mul]
      _ ≤ _ := by simpa using add_le_add_left (ih ht) ‖b.h‖

end
end CMP99Pivot.Path13
