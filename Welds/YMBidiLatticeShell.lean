/-
# BIDI Row-B lattice shell specialization

The generic BIDI shell theorem accepts an entropy/cardinality hypothesis.
For the literal four-dimensional block lattice that input is already theorem
output: `LatticeAnimalEntropy.animal_shell_card_le` proves the cardinality bound
for every shell made of connected lattice animals.  This weld removes the
redundant `hcard` socket from the live Yang--Mills proof-search surface.

It deliberately does *not* manufacture the remaining physical/source input:
the literal differentiated CMP116 activity must still be identified with an
activity satisfying the required exponential majorant.
-/
import RequestProject.YangMills.BIDI.PolymerShellBridge
import RequestProject.YangMills.LatticeAnimalEntropy
import RequestProject.YangMills.RowBLatticePolymerEnergy

namespace Welds.YMBidiLatticeShell

open Finset
open _root_.YangMills

/-- The four-dimensional lattice-animal theorem supplies the exact entropy
cardinality hypothesis consumed by the generic BIDI polymer shell bridge. -/
theorem lattice4ShellCardBound
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {v : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n) :
    ∀ n, ((shell n).card : ℝ) ≤ 2 * Real.exp (lattice4EntropyRate * n) := by
  intro n
  have h := animal_shell_card_le
    (nb := nbFromE latticeStep) (nbE := latticeStep) (v := v)
    (nbFromE_enumerates latticeStep)
    (nbFromE_symm latticeStep_involutive)
    hshell n
  simpa [lattice4EntropyRate, card_latticeDir] using h

/-- Far-shell BIDI decay on the literal four-dimensional lattice: the entropy
input is compiler-owned.  The only analytic input left here is the activity
majorant itself. -/
theorem lattice4FarShellEnergyTsumLe
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))}
    {act : Finset (Fin 4 → ℤ) → ℝ} {A mu : ℝ} {v : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hact : ∀ n, ∀ S ∈ shell n, |act S| ≤ A * Real.exp (-(mu * n)))
    (hA : 0 ≤ A) (hmu : lattice4EntropyRate < mu) (d : ℕ) :
    ∑' n : ℕ, (∑ S ∈ shell (d + n), |act S|)
      ≤ ((A * 2) / (1 - shellRatio lattice4EntropyRate mu))
          * Real.exp (-((mu - lattice4EntropyRate) * d)) :=
  RequestProject.YangMills.BIDI.far_shell_energy_tsum_le
    hact (lattice4ShellCardBound hshell) hA (by norm_num) hmu d

/-- Cauchy-weighted form of the same literal-lattice shell estimate.  This is
the geometric input required by the BIDI mixed-log consumer, now with no
independent entropy/cardinality assumption. -/
theorem lattice4CauchyShellEstimate
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))}
    {act : Finset (Fin 4 → ℤ) → ℝ}
    {A mu rad Mshell : ℝ} {v : Fin 4 → ℤ}
    (hrad : 0 < rad)
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hact : ∀ n, ∀ S ∈ shell n, |act S| ≤ A * Real.exp (-(mu * n)))
    (hA : 0 ≤ A) (hmu : lattice4EntropyRate < mu) (d : ℕ)
    (hMshell : Mshell ≤ ∑' n : ℕ, (∑ S ∈ shell (d + n), |act S|)) :
    RequestProject.YangMills.BIDI.cauchyConst rad * Mshell
      ≤ (RequestProject.YangMills.BIDI.cauchyConst rad
          * ((A * 2) / (1 - shellRatio lattice4EntropyRate mu)))
          * Real.exp (-((mu - lattice4EntropyRate) * d)) :=
  RequestProject.YangMills.BIDI.cauchy_shell_estimate_of_polymer
    hrad hact (lattice4ShellCardBound hshell) hA (by norm_num) hmu d hMshell

#print axioms lattice4ShellCardBound
#print axioms lattice4FarShellEnergyTsumLe
#print axioms lattice4CauchyShellEstimate

end Welds.YMBidiLatticeShell
