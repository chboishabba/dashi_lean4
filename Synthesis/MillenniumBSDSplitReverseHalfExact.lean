import Synthesis.MillenniumBSDSplitSquareclassGaloisExact

/-! Reverse solve the actual split-cubic half from its three signed
x-T square roots. Classical elliptic doubling formula; retain the
original tangent-root coordinates rather than a new quotient.
Distinct roots exclude every pair-sum denominator on this chart.
This handles nonexceptional doubled points; the nonsplit descent and
actual cohomology comparison are separate. -/
namespace DASHI.BSD.SplitTangent
variable {F : Type*} [Field F] [CharZero F]

def pairSum (r s t : F) := r*s+s*t+t*r
def reverseHalfX (x r s t : F) := x+pairSum r s t
def reverseHalfY (r s t : F) := -(r+s)*(s+t)*(t+r)

theorem reverseHalf_pair_nonzero (r s e f x : F)
    (hr : r^2=x-e) (hs : s^2=x-f) (hef : e≠f) : r+s≠0 := by
  intro h
  apply hef
  have he : r = -s := eq_neg_of_add_eq_zero_left h
  rw [he] at hr
  linear_combination hr-hs

/-- The original three root equations become products of pair sums.
This is the square-root fibre geometry, including all four even signs. -/
theorem reverseHalf_factors (x r s t e0 e1 e2 : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2) :
    reverseHalfX x r s t-e0=(r+s)*(r+t) ∧
    reverseHalfX x r s t-e1=(s+r)*(s+t) ∧
    reverseHalfX x r s t-e2=(t+r)*(t+s) := by
  unfold reverseHalfX pairSum
  constructor
  · linear_combination -hr
  constructor
  · linear_combination -hs
  · linear_combination -ht

theorem reverseHalf_curve (x r s t e0 e1 e2 : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2) :
    reverseHalfY r s t ^ 2 =
      (reverseHalfX x r s t-e0)*(reverseHalfX x r s t-e1)*(reverseHalfX x r s t-e2) := by
  obtain ⟨h0,h1,h2⟩ := reverseHalf_factors x r s t e0 e1 e2 hr hs ht
  rw [h0,h1,h2]
  unfold reverseHalfY
  ring

/-- The tangent factorization holds identically as a polynomial in z;
the line passes through the negative original point and has double
contact at the constructed half. No root-search or division needed. -/
theorem reverseHalf_tangent_factor (x y r s t e0 e1 e2 z : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2)
    (hp : r*s*t= -y) :
    (z-e0)*(z-e1)*(z-e2)-(-y-(r+s+t)*(z-x))^2 =
      (z-reverseHalfX x r s t)^2*(z-x) := by
  have he0 : e0=x-r^2 := by linear_combination hr
  have he1 : e1=x-s^2 := by linear_combination hs
  have he2 : e2=x-t^2 := by linear_combination ht
  have hy : y= -r*s*t := by linear_combination hp
  rw [he0,he1,he2,hy]
  unfold reverseHalfX pairSum
  ring

theorem reverseHalf_line_at_half (x y r s t : F) (hp : r*s*t= -y) :
    -y-(r+s+t)*(reverseHalfX x r s t-x)=reverseHalfY r s t := by
  unfold reverseHalfX reverseHalfY pairSum
  linear_combination -hp

/-- Recover the exact original tangent-root coordinates from the
reverse-solved half, rather than merely obtaining a point above P. -/
theorem reverseHalf_root_recovery (x r s t e0 e1 e2 : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2)
    (h01 : e0≠e1) (h02 : e0≠e2) (h12 : e1≠e2) :
    reverseHalfY r s t/(reverseHalfX x r s t-e0)+(r+s+t)=r ∧
    reverseHalfY r s t/(reverseHalfX x r s t-e1)+(r+s+t)=s ∧
    reverseHalfY r s t/(reverseHalfX x r s t-e2)+(r+s+t)=t := by
  obtain ⟨h0,h1,h2⟩ := reverseHalf_factors x r s t e0 e1 e2 hr hs ht
  have hrs := reverseHalf_pair_nonzero r s e0 e1 x hr hs h01
  have hrt := reverseHalf_pair_nonzero r t e0 e2 x hr ht h02
  have hst := reverseHalf_pair_nonzero s t e1 e2 x hs ht h12
  have hsr : s+r≠0 := by simpa [add_comm] using hrs
  have htr : t+r≠0 := by simpa [add_comm] using hrt
  have hts : t+s≠0 := by simpa [add_comm] using hst
  rw [h0,h1,h2]
  unfold reverseHalfY
  constructor
  · field_simp [hrs,hrt] <;> ring
  constructor
  · field_simp [hsr,hst] <;> ring
  · field_simp [htr,hts] <;> ring

/-- A field automorphism fixing the original cubic and doubled x
coordinate acts on the reconstructed half by the same sign row.
No independent choice of a geometric half is made. -/
theorem reverseHalf_galois (σ : F ≃+* F) (x r s t : F)
    (hx : σ x=x) (hr : r≠0) (hs : s≠0) (ht : t≠0) :
    σ (reverseHalfX x r s t)=
      reverseHalfX x (rootSign σ r*r) (rootSign σ s*s) (rootSign σ t*t) ∧
    σ (reverseHalfY r s t)=
      reverseHalfY (rootSign σ r*r) (rootSign σ s*s) (rootSign σ t*t) := by
  have er : rootSign σ r*r=σ r := div_mul_cancel₀ _ hr
  have es : rootSign σ s*s=σ s := div_mul_cancel₀ _ hs
  have et : rootSign σ t*t=σ t := div_mul_cancel₀ _ ht
  rw [er,es,et]
  simp [reverseHalfX,reverseHalfY,pairSum,hx]

end DASHI.BSD.SplitTangent
