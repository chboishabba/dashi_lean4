import Synthesis.MillenniumBSDOriginalKummerH1Exact
import Mathlib.Tactic

/-! The actual degree-one doubling map is multiplication by two on the
original homogeneous cohomology object. The split cubic tangent formula
below supplies the nonexceptional arithmetic square roots, without
asserting the missing Galois-character comparison. -/
namespace BSDCohomology
open WeierstrassCurve CategoryTheory DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]
local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _

theorem originalDoublingH1_eq_two (x : EllipticPointH1 W) :
    originalDoublingH1 W x = (2 : ℕ) • x := by
  obtain ⟨c,hc,hx⟩ := actualClass_surjective (pointRep W) x
  rw [← hx, originalDoublingH1, actualClass_natural]
  have he : mappedCocycle (pointRep W) (pointRep W) idGal
      (geometricDoublingTopRep W) c = c+c := by
    ext g
    change (2 : ℕ) • c g = c g+c g
    rw [two_nsmul]
  calc
    _ = actualClass (pointRep W) (c+c)
          (crossed_add (pointRep W) c c hc hc) := by
      apply (actualClass_eq_iff_coboundary _ _ _ _ _).mpr
      refine ⟨0, fun g => ?_⟩
      rw [he,sub_self,map_zero,sub_zero]
    _ = _ := by rw [actualClass_add,two_nsmul]

theorem originalTwoTorsionH1_killed (x : EllipticTwoTorsionH1 W) :
    (2 : ℕ) • originalInclusionH1 W x = 0 := by
  rw [← originalDoublingH1_eq_two]
  obtain ⟨c,hc,hx⟩ := actualClass_surjective (torsionRep W) x
  rw [← hx,originalInclusionH1,actualClass_natural,
    originalDoublingH1,actualClass_natural]
  apply (actualClass_zero_iff_coboundary _ _ _).mpr
  refine ⟨0,fun g => ?_⟩
  change (2 : ℕ) • (c g).1 = galoisPointMap W g 0-0
  rw [(c g).2,map_zero,sub_zero]

end
end BSDCohomology

namespace DASHI.BSD.SplitTangent
variable {F : Type*} [Field F]

/-- At a root of the original split cubic, the tangent factorization
produces the square root of the x-T value of the doubled point. -/
theorem square_root_of_double (e X x l : F) (h : X ≠ e)
    (hfactor : -l^2 = (e-X)^2*(e-x)) :
    (l/(X-e))^2 = x-e := by
  have hn : X-e ≠ 0 := sub_ne_zero.mpr h
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hn)).2
  linear_combination -hfactor

/-- The sign is fixed by the line through the negative doubled point;
the factorization hypothesis is the actual tangent intersection law. -/
theorem split_xT_three (e : Fin 3 → F) (X x : F) (line : F → F)
    (hne : ∀ i, X ≠ e i)
    (hf : ∀ t, (t-e 0)*(t-e 1)*(t-e 2)-line t^2 =
      (t-X)^2*(t-x)) :
    ∀ i, (line (e i)/(X-e i))^2 = x-e i := by
  intro i
  apply square_root_of_double (e i) X x (line (e i)) (hne i)
  have h := hf (e i)
  fin_cases i <;> simpa using h

end DASHI.BSD.SplitTangent
