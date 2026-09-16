/-
# CMP116-native BIDI source covariance weld

`BIDI.EndToEnd.source_covariance_bound_of_polymer` is deliberately generic: it
accepts an exponential activity majorant and an independent polymer-cardinality
bound.  For the actual four-dimensional CMP116 lane both generic sockets can be
compiled away.

* `CMP116ActivityRate.cmp116_block_activity_bound` converts the source's
  volume-form estimate to block units; the explicit `M^-4` cancels against the
  `M^4` block volume.
* `MarkedPolymerDecay.marked_activity_bound` absorbs the fixed polynomial mark
  cost at half the available decay/entropy margin.
* `LatticeAnimalEntropy`, exposed through `YMBidiLatticeShell`, supplies the
  four-dimensional shell cardinality theorem.

The theorem below therefore runs all the way to the continuum covariance bound
from the source-shaped CMP116 activity hypothesis.  It still requires the
literal source attachment (`hattach`), source-domain holomorphy, and actual
finite-to-continuum covariance convergence.  Those are the remaining
same-object/source hypotheses; no receipt is substituted for them.
-/
import Welds.YMBidiLatticeShell
import RequestProject.YangMills.BIDI.EndToEnd

namespace Welds.YMCMP116SourceCovariance

open Metric Filter Topology Finset
open _root_.YangMills

/-- **CMP116 source form -> continuum covariance decay.**

The mass in the conclusion is the marked activity rate minus the proved
four-dimensional entropy rate.  Since `markedRate` splits the original margin
in half, this is strictly positive whenever the source parameter satisfies
`kappa1 > 5 + 8 log 8`.
-/
theorem cmp116VolumeSourceCovarianceBound
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
    (hA : 0 ≤ A) (hkappa : 5 + 8 * Real.log 8 < kappa1)
    {rad : ℝ} (hrad : 0 < rad) (d : ℕ) {t : ℝ} (htd : t ≤ (d : ℝ))
    {ν : Type*} {l : Filter ν} [l.NeBot]
    {logZ : ν → ℂ → ℂ → ℂ} {covInf : ℂ}
    (hslice : ∀ N, ∀ x ∈ closedBall (0 : ℂ) rad,
      DiffContOnCl ℂ (fun y => logZ N x y) (ball 0 rad))
    (houter : ∀ N,
      DiffContOnCl ℂ (fun x => deriv (fun y => logZ N x y) 0) (ball 0 rad))
    (hattach : ∀ N, ∀ x ∈ closedBall (0 : ℂ) rad, ∀ y ∈ sphere (0 : ℂ) rad,
      ‖logZ N x y‖ ≤ ∑' k : ℕ, (∑ z ∈ shell (d + k), |act z|))
    (hconv : Tendsto
      (fun N => RequestProject.YangMills.BIDI.covFinite (logZ N)) l (𝓝 covInf)) :
    ‖covInf‖ ≤
      (RequestProject.YangMills.BIDI.cauchyConst rad
        * (((A * markCost m (cmp116BlockRate kappa1) lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate
              (markedRate (cmp116BlockRate kappa1) lattice4EntropyRate))))
        * Real.exp (-((markedRate (cmp116BlockRate kappa1) lattice4EntropyRate
            - lattice4EntropyRate) * t)) := by
  have hmu : lattice4EntropyRate < cmp116BlockRate kappa1 :=
    cmp116BlockRate_exceeds_entropy hkappa
  have hpoly := cmp116_block_activity_bound hM hvol hact
  have hmarked := marked_activity_bound hpoly hA hmu
  exact RequestProject.YangMills.BIDI.source_covariance_bound_of_polymer
    hmarked (YMBidiLatticeShell.lattice4ShellCardBound hshell)
    (mul_nonneg hA (markCost_nonneg hmu)) (by norm_num)
    (markedRate_gt hmu) hrad d htd hslice houter hattach hconv

#print axioms cmp116VolumeSourceCovarianceBound

end Welds.YMCMP116SourceCovariance
