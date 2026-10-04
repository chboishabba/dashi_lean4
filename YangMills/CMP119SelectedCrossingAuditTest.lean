import YangMills.CMP119SelectedCrossingAudit

namespace RequestProject.YangMills

example
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ) :
    CMP119CrossingKernelAuditOutcome kernel :=
  cmp119_crossing_kernel_audit_complete kernel

example
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (h : CMP119CrossingKernelAuditOutcome kernel) :
    (∀ f : ι → ℝ, 0 ≤ indexedReflectionQuadratic kernel f) ∨
      ∃ f : ι → ℝ, indexedReflectionQuadratic kernel f < 0 :=
  cmp119_crossing_kernel_audit_dichotomy kernel h

end RequestProject.YangMills
