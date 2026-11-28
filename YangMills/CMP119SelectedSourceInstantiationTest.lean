import YangMills.CMP119SelectedSourceInstantiation

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (links : SU2TorusLinks (2 * n)) :
    su2FullResidual
        source.residual.literalRegular
        source.residual.literalROperation
        source.residual.literalBoundary
        source.residual.literalVacuum links =
      source.residual.sourceResidual links :=
  source.literal_residual_eq_source links

example
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n) :
    CMP119LiteralDyadicResidualWeld (2 * n) :=
  source.toDyadicResidualWeld

end RequestProject.YangMills
