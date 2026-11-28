import YangMills.FunctionalReflectionPositiveKernel

namespace RequestProject.YangMills

example
    {X : Type*}
    (h : X → ℝ) :
    ReflectionPositiveKernel (fun x y => h x * h y) :=
  reflectionPositiveKernel_halfFactor h

example
    {X : Type*}
    (K H : X → X → ℝ)
    (hKs : SymmetricKernel K)
    (hHs : SymmetricKernel H)
    (hK : ReflectionPositiveKernel K)
    (hH : ReflectionPositiveKernel H) :
    ReflectionPositiveKernel (fun x y => K x y * H x y) :=
  reflectionPositiveKernel_mul K H hKs hHs hK hH

end RequestProject.YangMills
