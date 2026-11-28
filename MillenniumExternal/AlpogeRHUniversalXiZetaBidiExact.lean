import MillenniumExternal.AlpogeRHBoundaryExact

/-! Universal quantification over the actual xi/zeta zero equivalence:
no additional C3 labels or determinant observer are needed for this
terminal predicate. Does not assert either universal predicate. -/
namespace MillenniumExternal.AlpogeRH

theorem originalAllXiZerosAxis_iff_allNontrivialZetaCritical :
    (∀ t : {t : ℂ // Millennium.xi t = 0}, t.1.im = 0) ↔
      (∀ s : {s : ℂ // Millennium.IsNontrivialZero s},
        s.1.re = (1/2 : ℝ)) := by
  constructor
  · intro h s
    obtain ⟨t,ht⟩ := originalXiZetaZeroEquiv.surjective s
    rw [← ht]
    exact (originalXiZeroOnAxis_iff_zetaCritical t).mp (h t)
  · intro h t
    exact (originalXiZeroOnAxis_iff_zetaCritical t).mpr
      (h (originalXiZetaZeroEquiv t))

end MillenniumExternal.AlpogeRH
