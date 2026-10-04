import Mathlib

namespace CondensedMatter
namespace YbSb2

/-!
ATTRIBUTION

SOURCE — Kataria et al., arXiv:2601.07460 / PRL accepted 3 Aug 2026:
* simplified effective normal-state model takes isotropic b and m;
* their stated model criterion is mb > 0 trivial and mb < 0 nontrivial;
* Figure 3 uses b = 0.5 and m = -0.7.

DASHI DERIVATION:
* represent those decimal values exactly as rationals 1/2 and -7/10;
* prove m*b = -7/20 < 0.

The theorem below does not independently prove the physical topological
criterion.  It proves that the paper's selected numerical parameters satisfy
the criterion's negative-mass-sign premise.
-/

def paperB : ℚ := 1 / 2
def paperM : ℚ := -7 / 10

theorem paper_mass_product_exact :
    paperM * paperB = (-7 : ℚ) / 20 := by
  norm_num [paperM, paperB]

theorem paper_mass_product_negative :
    paperM * paperB < 0 := by
  norm_num [paperM, paperB]

/-- Source-model interpretation kept separate from the arithmetic proof. -/
structure DiracMassTopologySourceLaw where
  TopologicallyNontrivial : Prop
  negativeMassProductImpliesNontrivial :
    paperM * paperB < 0 → TopologicallyNontrivial

theorem paper_parameters_satisfy_source_nontrivial_regime
    (L : DiracMassTopologySourceLaw) :
    L.TopologicallyNontrivial :=
  L.negativeMassProductImpliesNontrivial paper_mass_product_negative

end YbSb2
end CondensedMatter
