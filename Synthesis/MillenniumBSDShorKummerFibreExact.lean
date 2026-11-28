import Synthesis.MillenniumBSDSplitReverseHalfExact

/-! Shor/RSA cross-pollination: the exact coset law, not an algorithmic
speedup. GeneralShor.FiniteAbelianHiddenSubgroupProblem.sameCosetLaw
is instantiated here at the original geometric doubling map, whose
kernel is the original E[2]. The rational Kummer quotient is a
different observation with kernel 2E(K). No finite group hypothesis
on E(K) or E(Kbar), and no arithmetic rank inference from a fibre. -/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

theorem double_sameCoset (Q R : GeometricPoint W) :
    (2:ℕ) • Q=(2:ℕ) • R ↔ (2:ℕ) • (Q-R)=0 := by
  rw [nsmul_sub,sub_eq_zero]

def actualDoubleFibreEquiv {P : GeometricPoint W} (Q : GeometricHalfData W P) :
    EllipticTwoTorsion W ≃ {R : GeometricPoint W // (2:ℕ) • R=P} where
  toFun T := ⟨Q.half+T.1,by rw [nsmul_add,Q.double_half,T.2,add_zero]⟩
  invFun R := ⟨R.1-Q.half,by rw [nsmul_sub,R.2,Q.double_half,sub_self]⟩
  left_inv T := by apply Subtype.ext; dsimp; abel
  right_inv R := by apply Subtype.ext; dsimp; abel

/-- The actual Kummer cocycle is the fibre address of the Galois
image of the chosen half, not a freely chosen sign or observation. -/
theorem actualDoubleFibre_galois_address {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P) (Q : GeometricHalfData W P)
    (σ : Field.absoluteGaloisGroup K) :
    (actualDoubleFibreEquiv W Q).symm
      ⟨galoisPointMap W σ Q.half,by
        rw [← map_nsmul,Q.double_half,hP σ]⟩ =
        kummerCocycleValue W hP Q σ := by
  apply Subtype.ext
  rfl

/-- RSA/Shor-style exact observation equality on the actual rational
Kummer map is equality modulo the actual doubles subgroup. This is
the other kernel; it is not the geometric two-torsion kernel. -/
theorem rationalKummer_sameCoset
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (P R : BasePoint W) :
    rationalKummerClass W hs P=rationalKummerClass W hs R ↔
      ∃ S : BasePoint W,(2:ℕ) • S=P-R := by
  have he : rationalKummerClass W hs (P-R)=
      rationalKummerClass W hs P-rationalKummerClass W hs R :=
    (rationalKummerHom W hs).map_sub P R
  rw [← sub_eq_zero,← he,rationalKummerClass_zero_iff_double]

end
end BSDCohomology

namespace DASHI.BSD.SplitTangent
variable {F : Type*} [Field F] [CharZero F]

/-- Reverse-half equivariance with the original root-zero translation
owner. Two sign changes, and only two, are the nontrivial translation
at that root. Cyclic relabeling supplies the other two translations. -/
theorem reverseHalf_evenFlip_torsion (x r s t e0 e1 e2 : F)
    (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2)
    (h01 : e0≠e1) (h02 : e0≠e2) :
    reverseHalfX x r (-s) (-t)-e0 =
      torsionU (e0-e1) (e0-e2) (reverseHalfX x r s t-e0) ∧
    reverseHalfY r (-s) (-t)=
      torsionV (e0-e1) (e0-e2) (reverseHalfX x r s t-e0)
        (reverseHalfY r s t) := by
  have h := (reverseHalf_factors x r s t e0 e1 e2 hr hs ht).1
  have hrs := reverseHalf_pair_nonzero r s e0 e1 x hr hs h01
  have hrt := reverseHalf_pair_nonzero r t e0 e2 x hr ht h02
  have h01' : e0-e1=s^2-r^2 := by linear_combination hs-hr
  have h02' : e0-e2=t^2-r^2 := by linear_combination ht-hr
  have h0 : e0=x-r^2 := by linear_combination hr
  rw [h,h01',h02']
  constructor
  · unfold torsionU reverseHalfX pairSum
    rw [h0]
    field_simp [hrs,hrt] <;> ring
  · unfold torsionV reverseHalfY
    field_simp [hrs,hrt] <;> ring

/-- The zero or double-sign row has no fixed half unless it is the
identity row, on the nonexceptional chart. Use the original root
recovery theorem: both coordinates and the tangent slope (fixed by
the doubled point when needed) carry the address. -/
theorem reverseHalf_evenFlip_x_ne (x r s t : F)
    (hr : r≠0) (hst : s+t≠0) :
    reverseHalfX x r (-s) (-t)≠reverseHalfX x r s t := by
  intro h
  have hz : 2*r*(s+t)=0 := by
    unfold reverseHalfX pairSum at h
    linear_combination -h
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hr) hst) hz

end DASHI.BSD.SplitTangent
