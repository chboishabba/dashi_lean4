import Welds.YMBidiLatticeShell

namespace Welds.YMBidiLatticeShellRegression

open Finset
open _root_.YangMills

example {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {v : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n) :
    ∀ n, ((shell n).card : ℝ) ≤ 2 * Real.exp (lattice4EntropyRate * n) :=
  lattice4ShellCardBound hshell

end Welds.YMBidiLatticeShellRegression
