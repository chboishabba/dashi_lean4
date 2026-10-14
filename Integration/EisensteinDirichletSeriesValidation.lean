import Integration.EisensteinDirichletSeriesExact

namespace Dashi.EisensteinDirichletSeriesValidation

open Complex LSeries
open Dashi.EisensteinDirichletSeriesExact

example (s : ℂ) (hs : 1 < s.re) :
    LSeries eisensteinGeometricCoefficient s
      = 6 * riemannZeta s * chiMinus3LSeries s :=
  eisensteinGeometricLSeries_factorization s hs

end Dashi.EisensteinDirichletSeriesValidation
