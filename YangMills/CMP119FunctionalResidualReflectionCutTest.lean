import YangMills.CMP119FunctionalResidualReflectionCut

namespace RequestProject.YangMills

example
    {X : Type*}
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  cmp119_functional_complete_residual_kernel_rp cut

example
    {X : Type*}
    (wilson residual : X → X → ℝ)
    (hWs : SymmetricKernel wilson)
    (hRs : SymmetricKernel residual)
    (hW : ReflectionPositiveKernel wilson)
    (hR : ReflectionPositiveKernel residual) :
    ReflectionPositiveKernel (fun x y => wilson x y * residual x y) :=
  reflectionPositiveKernel_mul wilson residual hWs hRs hW hR

end RequestProject.YangMills
