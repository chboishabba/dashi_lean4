import YangMills.OSGramHilbertCompletion

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    CompleteSpace data.Hilbert := by infer_instance

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    InnerProductSpace ℝ data.Hilbert := by infer_instance

end RequestProject.YangMills
