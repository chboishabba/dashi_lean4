import Synthesis.MillenniumBSDSplitTorsionRootSignExact
import Synthesis.MillenniumBSDGeneralGeometricDoublingExact

/-! Actual arithmetic comparison on the nonexceptional split cubic.
The three tangent roots are indexed by the original roots of the
cubic. Rational Galois automorphisms act through ratios of square
roots. The fixed-half/cocycle comparison is not replaced by a
fresh square-class quotient; this constructs its sign coordinates.
The exceptional charts, nonsplit etale algebra and rank remain open. -/
namespace DASHI.BSD.SplitTangent
open scoped BigOperators

section Characters
variable {F : Type*} [Field F] [CharZero F]

def rootSign (σ : F ≃+* F) (r : F) : F := σ r / r

theorem rootSign_square (σ : F ≃+* F) (r : F) (hr : r≠0)
    (h : σ (r^2)=r^2) : rootSign σ r ^ 2=1 := by
  rw [rootSign,div_pow,← map_pow,h,div_self (pow_ne_zero _ hr)]

theorem rootSign_eq_one_or_neg_one (σ : F ≃+* F) (r : F) (hr : r≠0)
    (h : σ (r^2)=r^2) : rootSign σ r=1 ∨ rootSign σ r= -1 := by
  have hh := rootSign_square σ r hr h
  have hp : (rootSign σ r-1)*(rootSign σ r+1)=0 := by linear_combination hh
  rcases mul_eq_zero.mp hp with hp|hp
  · left; exact sub_eq_zero.mp hp
  · right; exact eq_neg_of_add_eq_zero_left hp

theorem rootSign_fixed (σ τ : F ≃+* F) (r : F) (hr : r≠0)
    (h : τ (r^2)=r^2) : σ (rootSign τ r)=rootSign τ r := by
  rcases rootSign_eq_one_or_neg_one τ r hr h with hh|hh <;> simp [hh]

/-- Ratios compose as a genuine multiplicative sign character,
not only as arbitrary elements of the field. -/
theorem rootSign_comp (σ τ : F ≃+* F) (r : F) (hr : r≠0)
    (hτ : τ (r^2)=r^2) :
    rootSign (τ.trans σ) r=rootSign σ r*rootSign τ r := by
  have h := rootSign_fixed σ τ r hr hτ
  unfold rootSign at *
  rw [map_div] at h
  change σ (τ r)/r=(σ r/r)*(τ r/r)
  have hs : σ r≠0 := fun hh=>hr (σ.injective (by simpa using hh))
  field_simp [hr,hs] at h ⊢
  linear_combination h

theorem rootSign_product_one (σ : F ≃+* F) (r : Fin 3 → F)
    (hr : ∀ i,r i≠0) (h : σ (∏ i,r i)=∏ i,r i) :
    ∏ i,rootSign σ (r i)=1 := by
  unfold rootSign
  rw [Finset.prod_div_distrib,← map_prod,h,div_self]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hr i)

/-- Actual product of the three tangent roots. The sign is minus
the doubled ordinate for the source line through the negative
doubled point. The residual factor is the original cubic equation. -/
theorem tangent_root_product (a b u Y : F) (hy : Y≠0)
    (hc : Y^2=u*(u+a)*(u+b)) :
    let m := shiftedSlope a b u Y
    let x := m^2-a-b-2*u
    let y := -Y-m*(x-u)
    rootZero a b u Y*rootA a b u Y*rootB a b u Y= -y := by
  dsimp
  unfold rootZero rootA rootB shiftedSlope
  field_simp [hy]
  ring_nf at hc ⊢
  linear_combination (-8*Y^2+4*a^2*b+8*a^2*u+4*a*b^2+20*a*b*u+
    28*a*u^2+8*b^2*u+28*b*u^2+28*u^3)*hc

/-- On a rational doubled point the product condition forces even
signs. The values are the actual three tangent roots and therefore
the square-class character of the literal x-T coordinate. -/
theorem tangent_squareclass_sign_row (σ : F ≃+* F)
    (r : Fin 3 → F) (x : F) (e : Fin 3 → F) (Y : F)
    (hs : ∀ i,r i^2=x-e i) (hr : ∀ i,r i≠0)
    (hprod : ∏ i,r i=Y) (hx : σ x=x)
    (he : ∀ i,σ (e i)=e i) (hy : σ Y=Y) :
    (∀ i,rootSign σ (r i)=1 ∨ rootSign σ (r i)= -1) ∧
      ∏ i,rootSign σ (r i)=1 := by
  constructor
  · intro i
    apply rootSign_eq_one_or_neg_one _ _ (hr i)
    rw [hs,map_sub,hx,he]
  · exact rootSign_product_one σ r hr (by rw [hprod,hy])

end Characters
end DASHI.BSD.SplitTangent

namespace BSDCohomology
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The actual global Sha[2] condition agrees with multiplication by
two, not merely an abstract endomorphism named doubling. -/
theorem originalPointShaTwo_mem_iff_nsmul (x : EllipticPointH1 W) :
    x∈originalPointShaTwo W ↔
      (2:ℕ) • x=0 ∧ ∀ v : OriginalPlace K,placePointLoc W v x=0 := by
  simp only [originalPointShaTwo,AddSubgroup.mem_inf,AddSubgroup.mem_iInf,
    AddMonoidHom.mem_ker]
  rw [← originalDoublingH1_eq_two W]
  rfl

end
end BSDCohomology
