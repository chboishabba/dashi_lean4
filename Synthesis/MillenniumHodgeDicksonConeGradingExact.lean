import Synthesis.MillenniumHodgeDicksonProjectiveConeExact
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

def coneAffineValue (i : Option OriginalCoord) : ActualSourceOpen :=
  i.elim 1 originalOpenCoord

def coneAtOne : ProjectiveAmbientPoly →+* ActualSourceOpen :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ActualSourceOpen) coneAffineValue

theorem coneMap_monomial (m : Option OriginalCoord →₀ ℕ) (c : ℚ) :
    actualConeMap (MvPolynomial.monomial m c)=
      Polynomial.C (coneAtOne (MvPolynomial.monomial m c))*Polynomial.X^m.degree := by
  classical
  unfold actualConeMap coneAtOne
  rw [MvPolynomial.eval₂Hom_monomial,MvPolynomial.eval₂Hom_monomial]
  have hv (i : Option OriginalCoord) :
      (match i with | none => Polynomial.X
                     | some j => Polynomial.C (originalOpenCoord j)*Polynomial.X) =
        Polynomial.C (coneAffineValue i)*Polynomial.X := by
    cases i <;> simp [coneAffineValue]
  simp_rw [hv,mul_pow]
  unfold Finsupp.prod Finsupp.degree
  rw [Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]
  simp only [RingHom.comp_apply,map_mul,map_prod,map_pow]
  ring

/-- The coefficient of T^n is exactly the evaluation of the degree-n
homogeneous component, not an inference from finitely many points. -/
theorem coneMap_coeff (p : ProjectiveAmbientPoly) (n : ℕ) :
    (actualConeMap p).coeff n=
      coneAtOne (MvPolynomial.homogeneousComponent n p) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [MvPolynomial.homogeneousComponent_apply,map_sum,map_sum]
  simp_rw [coneMap_monomial,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d.degree=n
  · simp [h]
  · simp [h,Ne.symm h]

/-- The actual kernel is closed under every homogeneous component,
in both directions, using the exact original source coordinates. -/
theorem actualCone_mem_iff_components (p : ProjectiveAmbientPoly) :
    p∈actualConeIdeal ↔
      ∀ n, MvPolynomial.homogeneousComponent n p∈actualConeIdeal := by
  change actualConeMap p=0 ↔ _
  constructor
  · intro hp n
    change actualConeMap (MvPolynomial.homogeneousComponent n p)=0
    ext j
    rw [coneMap_coeff]
    have hh := MvPolynomial.homogeneousComponent_isHomogeneous n p
    rw [MvPolynomial.homogeneousComponent_of_mem hh]
    split
    · have he := congrArg (fun q : Polynomial ActualSourceOpen=>q.coeff n) hp
      simpa [coneMap_coeff] using he
    · simp
  · intro hp
    ext n
    rw [coneMap_coeff]
    have h := hp n
    change actualConeMap (MvPolynomial.homogeneousComponent n p)=0 at h
    have he := congrArg (fun q : Polynomial ActualSourceOpen=>q.coeff n) h
    simpa [coneMap_coeff,
      MvPolynomial.homogeneousComponent_eq_self
        (MvPolynomial.homogeneousComponent_isHomogeneous n p)] using he

/-- The same cone ideal, now attached to Mathlib's actual grading. -/
theorem actualConeIdeal_homogeneous :
    actualConeIdeal.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option OriginalCoord) ℚ) := by
  intro p hp n
  exact (actualCone_mem_iff_components p).mp hp n

end
end DASHI.Hodge.DicksonCoupled
