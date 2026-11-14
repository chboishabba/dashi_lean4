import YangMills.WilsonCountableStoneWeierstrass

namespace RequestProject.YangMills

example
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    (wilson : ℕ → C(Ω, ℝ))
    (hInjective : Function.Injective (fun x i => wilson i x)) :
    (wilsonGeneratedAlgebra wilson).topologicalClosure = ⊤ :=
  wilson_generated_algebra_dense wilson hInjective

example
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    (wilson : ℕ → C(Ω, ℝ))
    (hInjective : Function.Injective (fun x i => wilson i x)) :
    (wilsonGeneratedAlgebra wilson).SeparatesPoints :=
  wilson_generated_algebra_separatesPoints wilson hInjective

end RequestProject.YangMills
