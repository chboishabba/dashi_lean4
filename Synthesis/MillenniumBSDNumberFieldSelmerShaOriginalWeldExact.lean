import Synthesis.MillenniumBSDGeneralGeometricDoublingExact
import Synthesis.MillenniumBSDOriginalPlaceSelmerShaExact

/-!
Original number-field Selmer / Sha source weld.

The general tangent-quartic geometric doubling theorem eliminates every
surjectivity hypothesis previously carried by the original global/local
Selmer exact sequence. No independently specified Kummer or Sha groups.
This is an unconditional theorem about the *original algebraic*
2-Selmer exact sequence, NOT BSD analytic rank equality or finiteness.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

private theorem globalHalfOnto :
    Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q) :=
  general_geometric_doubling_onto W

private theorem localHalfOnto (v : OriginalPlace K) :
    Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2 : ℕ) • Q) :=
  general_geometric_doubling_onto (localCurve W v)

/-- The *original* all-place two-Selmer subgroup, using the actual
geometric 2-division rather than a supplied half witness. -/
def numberFieldSelmerTwo : AddSubgroup (EllipticTwoTorsionH1 W) :=
  originalSelmerTwo W (localHalfOnto W)

/-- The original number-field global Kummer map into the SAME Selmer
subgroup and physical completion carrier. -/
def numberFieldKummerToSelmer :
    BasePoint W →+ numberFieldSelmerTwo W :=
  globalKummerToSelmer W (globalHalfOnto W) (localHalfOnto W)

/-- Every source-native global Kummer class obeys the original local
conditions; the local choices are discharged by geometric doubling. -/
theorem numberField_globalKummer_mem_selmer (P : BasePoint W) :
    rationalKummerClass W (globalHalfOnto W) P ∈
      numberFieldSelmerTwo W :=
  globalKummer_mem_selmer W (globalHalfOnto W) (localHalfOnto W) P

/-- Original number-field Selmer/Sha exactness, with NO arbitrary
surjectivity hypothesis. The remaining BSD analytic rank and all-prime
Sha finiteness questions are logically separate. -/
theorem numberField_selmerToSha_surjective :
    Function.Surjective
      (selmerToShaTwo W (globalHalfOnto W) (localHalfOnto W)) :=
  selmerToShaTwo_surjective W (globalHalfOnto W) (localHalfOnto W)

theorem numberField_selmerToSha_kernel :
    (selmerToShaTwo W (globalHalfOnto W) (localHalfOnto W)).ker =
      (numberFieldKummerToSelmer W).range :=
  selmerToShaTwo_ker W (globalHalfOnto W) (localHalfOnto W)

/-- The original quotient-by-rational-doubles lands in the
place-locally-trivial TWO-TORSION point-cohomology subgroup, without
another quotient object or hand-provided geometric half. -/
def numberFieldSelmerQuotientEquivShaTwo :
    (numberFieldSelmerTwo W ⧸ (numberFieldKummerToSelmer W).range) ≃+
      originalPointShaTwo W :=
  selmerQuotientEquivShaTwo W (globalHalfOnto W) (localHalfOnto W)

end
end BSDCohomology
