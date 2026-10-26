import Integration.TetracodeE8MatrixIsometry

namespace Integration.TetracodeE8MatrixIsometryRegression

open Integration.TetracodeE8MatrixIsometry

example (v w : R8) : mappedPair v w = 12 * eisensteinPair v w :=
  matrix_isometry v w

example (v : R8) : mappedNorm v = 12 * eisensteinNorm4 v :=
  matrix_norm_isometry v

end Integration.TetracodeE8MatrixIsometryRegression
