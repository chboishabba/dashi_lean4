import YangMills.OSGramQuotientInnerProduct

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm) :
    InnerProductSpace.Core ℝ (V ⧸ B.ker) :=
  osGramQuotientInnerProductCore B hPositive hSymmetric

end RequestProject.YangMills
