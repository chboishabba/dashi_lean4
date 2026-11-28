import Synthesis.MillenniumHodgeDicksonConeGradingExact

namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- On a homogeneous numerator, the cone kernel is exactly the kernel
of dehomogenization on the original coordinates. This is the numerator
criterion for the h-chart, not yet an isomorphism of Proj charts. -/
theorem homogeneous_cone_chart_kernel (p : ProjectiveAmbientPoly) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    p ∈ actualConeIdeal ↔ coneAtOne p = 0 := by
  constructor
  · intro h
    change actualConeMap p = 0 at h
    have hc := congrArg (fun q : Polynomial ActualSourceOpen => q.coeff d) h
    simpa [coneMap_coeff, MvPolynomial.homogeneousComponent_eq_self hp] using hc
  · intro h
    change actualConeMap p = 0
    ext n
    rw [coneMap_coeff]
    by_cases hn : n = d
    · subst n
      simpa [MvPolynomial.homogeneousComponent_eq_self hp] using h
    · rw [MvPolynomial.homogeneousComponent_of_mem hp]
      split
      · rename_i he
        exact (hn (by omega)).elim
      · simp

end
end DASHI.Hodge.DicksonCoupled
