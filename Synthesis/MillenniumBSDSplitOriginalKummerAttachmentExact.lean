import Synthesis.MillenniumBSDSplitActualDoublingExact

namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.SplitTangent
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic]
local notation "F" => AlgebraicClosure K
local notation "V" => W⁄F

/-- The explicit split reverse half inhabits the original geometric
half type used by the existing Kummer class, not a parallel torsor. -/
def actualSplitHalfData (a b c : F) (h : SplitCoefficients V a b c)
    (x y r s t : F) (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hp : r*s*t= -y) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hP : V.toAffine.Nonsingular x y) :
    GeometricHalfData W (.some hP) :=
  ⟨reverseHalfPoint V a b c h x r s t hr hs ht,
    reverseHalf_actual_double V a b c h x y r s t hr hs ht hp hab hac hbc hP⟩

/-- Original absolute Galois point map acts on the reverse-half
coordinates by its actual field automorphism. Split roots and target x
are fixed here; permuted nonsplit roots require a separate chart. -/
theorem actualSplitHalf_galois (a b c : F) (h : SplitCoefficients V a b c)
    (σ : Field.absoluteGaloisGroup K) (x r s t : F)
    (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hx : σ x=x) (ha : σ a=a) (hb : σ b=b) (hc : σ c=c) :
    galoisPointMap W σ (reverseHalfPoint V a b c h x r s t hr hs ht)=
      reverseHalfPoint V a b c h x (σ r) (σ s) (σ t)
        (by rw [← map_pow,hr,map_sub,hx,ha])
        (by rw [← map_pow,hs,map_sub,hx,hb])
        (by rw [← map_pow,ht,map_sub,hx,hc]) := by
  unfold reverseHalfPoint
  simp only [galoisPointMap,WeierstrassCurve.Affine.Point.map_some]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor <;> simp [reverseHalfX,reverseHalfY,pairSum,map_add,map_mul,hx]

/-- On the nonexceptional split chart, the actual original Kummer
cocycle value is one of the four literal point addresses. The sign
row theorem supplies the classification on the same chosen half.
No Weil-pairing identification or nonsplit arithmetic claim. -/
theorem actualSplitKummer_addresses (a b c : F) (h : SplitCoefficients V a b c)
    (σ : Field.absoluteGaloisGroup K) (x y r s t : F)
    (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hp : r*s*t= -y) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hr0 : r≠0) (hs0 : s≠0) (ht0 : t≠0)
    (hP : V.toAffine.Nonsingular x y)
    (hfix : IsGaloisFixedPoint W (.some hP))
    (hx : σ x=x) (hy : σ y=y) (ha : σ a=a) (hb : σ b=b) (hc : σ c=c) :
    let Q := actualSplitHalfData W a b c h x y r s t hr hs ht hp hab hac hbc hP
    let z := (kummerCocycleValue W hfix Q σ).1
    z=0 ∨ z=splitRootPoint V a b c h ∨
      z=splitRootPoint V b c a (h.cycle V) ∨
      z=splitRootPoint V c a b ((h.cycle V).cycle V) := by
  dsimp
  change _ - reverseHalfPoint V a b c h x r s t hr hs ht = 0 ∨ _
  rw [actualSplitHalf_galois W a b c h σ x r s t hr hs ht hx ha hb hc]
  have hr2 : σ (r^2)=r^2 := by rw [hr,map_sub,hx,ha]
  have hs2 : σ (s^2)=s^2 := by rw [hs,map_sub,hx,hb]
  have ht2 : σ (t^2)=t^2 := by rw [ht,map_sub,hx,hc]
  have hprod : σ (r*s*t)=r*s*t := by rw [hp,map_neg,hy]
  exact actual_split_sign_difference V a b c h σ.toRingEquiv x r s t
    hr hs ht hr0 hs0 ht0 hab hac hbc hr2 hs2 ht2 hprod

end
end BSDCohomology
