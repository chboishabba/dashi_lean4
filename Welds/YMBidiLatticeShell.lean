/-
# BIDI Row-B lattice shell specialization

The generic BIDI shell theorem accepts an entropy/cardinality hypothesis.
For the literal four-dimensional block lattice that input is already theorem
output: `LatticeAnimalEntropy.animal_shell_card_le` proves the cardinality bound
for every shell made of connected lattice animals.  This weld removes the
redundant `hcard` socket from the live Yang--Mills proof-search surface.

The source-shaped extension below also removes a second artificial interface.
`CMP116ActivityRate` already converts the source's volume-form activity estimate

    A * n^m * exp (-(cmp116BlockRate kappa1 / M^4) * vol)

with `vol = M^4 n` into a block-unit marked exponential majorant.  Combining it
with the proved four-dimensional entropy theorem gives the actual far-shell BIDI
budget, with the mark cost and the surviving decay rate explicit.

What remains physical/source-specific is therefore the identification of the
literal differentiated CMP116 activities with the source majorant itself.  No
such identification is manufactured here.
-/
import RequestProject.YangMills.BIDI.PolymerShellBridge
import RequestProject.YangMills.LatticeAnimalEntropy
import RequestProject.YangMills.RowBLatticePolymerEnergy
import RequestProject.YangMills.CMP116ActivityRate

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

/-- The source-shaped CMP116 volume-form estimate already gives a finite total
marked activity energy.  This theorem exposes that source-native bound directly
in the active BIDI weld. -/
theorem cmp116VolumeMarkedTotalEnergyLe
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))}
    {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 : ℝ} {M m : ℕ} {v : Fin 4 → ℤ}
    (hM : 0 < M)
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1) :
    ∑' n : ℕ, (∑ S ∈ shell n, |act S|)
      ≤ ((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate)) :=
  cmp116_block_marked_shell_energy_tsum_le hM hshell hvol hact hA hkappa

/-- **Source-shaped far-shell payment.**

The only source input is the literal CMP116 volume-form majorant.  The `M^-4`
conversion, polynomial mark cost, lattice entropy, and far-shell geometric sum
are all theorem output.  The surviving mass is

`markedRate (cmp116BlockRate kappa1) lattice4EntropyRate - lattice4EntropyRate`,

i.e. one half of the original activity/entropy margin. -/
theorem cmp116VolumeMarkedFarShellEnergyTsumLe
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))}
    {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 : ℝ} {M m : ℕ} {v : Fin 4 → ℤ}
    (hM : 0 < M)
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1) (d : ℕ) :
    ∑' n : ℕ, (∑ S ∈ shell (d + n), |act S|)
      ≤ (((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate)))
        * Real.exp (-((markedRate (cmp116BlockRate kappa1) lattice4EntropyRate
            - lattice4EntropyRate) * d)) := by
  have hmu : lattice4EntropyRate < cmp116BlockRate kappa1 :=
    cmp116BlockRate_exceeds_entropy hkappa
  have hpoly := cmp116_block_activity_bound hM hvol hact
  have hmarked := marked_activity_bound hpoly hA hmu
  exact lattice4FarShellEnergyTsumLe hshell hmarked
    (mul_nonneg hA (markCost_nonneg hmu)) (markedRate_gt hmu) d

/-- **Source-shaped BIDI Cauchy shell estimate.**  This is the geometric input
of the mixed-log consumer with the generic activity and entropy sockets both
eliminated.  The sole remaining Row-B source obligation is proving that the
literal differentiated CMP116 activity satisfies the displayed source majorant. -/
theorem cmp116VolumeCauchyShellEstimate
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))}
    {act vol : Finset (Fin 4 → ℤ) → ℝ}
    {A kappa1 rad Mshell : ℝ} {M m : ℕ} {v : Fin 4 → ℤ}
    (hrad : 0 < rad) (hM : 0 < M)
    (hshell : ∀ n, ∀ S ∈ shell n,
      IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hvol : ∀ n, ∀ S ∈ shell n, vol S = (M : ℝ) ^ 4 * n)
    (hact : ∀ n, ∀ S ∈ shell n,
      |act S| ≤ A * (n : ℝ) ^ m
        * Real.exp (-(cmp116BlockRate kappa1 / (M : ℝ) ^ 4 * vol S)))
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1) (d : ℕ)
    (hMshell : Mshell ≤ ∑' n : ℕ, (∑ S ∈ shell (d + n), |act S|)) :
    RequestProject.YangMills.BIDI.cauchyConst rad * Mshell
      ≤ (RequestProject.YangMills.BIDI.cauchyConst rad
          * (((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
            / (1 - shellRatio lattice4EntropyRate
                (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate))))
        * Real.exp (-((markedRate (cmp116BlockRate kappa1) lattice4EntropyRate
            - lattice4EntropyRate) * d)) := by
  have hc : 0 ≤ RequestProject.YangMills.BIDI.cauchyConst rad :=
    le_of_lt (RequestProject.YangMills.BIDI.cauchyConst_pos hrad)
  have htail := cmp116VolumeMarkedFarShellEnergyTsumLe
    hM hshell hvol hact hA hkappa d
  have h := le_trans hMshell htail
  exact mul_le_mul_of_nonneg_left h hc

#print axioms lattice4ShellCardBound
#print axioms lattice4FarShellEnergyTsumLe
#print axioms lattice4CauchyShellEstimate
#print axioms cmp116VolumeMarkedTotalEnergyLe
#print axioms cmp116VolumeMarkedFarShellEnergyTsumLe
#print axioms cmp116VolumeCauchyShellEstimate

end Welds.YMBidiLatticeShell
