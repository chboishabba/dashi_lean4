import YangMills.CMP119SelectedComponentReflectionAssembly

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n] {X : Type*}
    (sector : CMP119SelectedSectorComponents n)
    (certs : CMP119SelectedSectorFunctionalCertificates sector X) :
    ReflectionPositiveKernel (selectedSectorAssembledKernel certs) :=
  selected_sector_assembled_kernel_rp certs

example
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    ReflectionPositiveKernel source.sourceKernel :=
  cmp119_selected_source_functional_kernel_rp source

end RequestProject.YangMills
