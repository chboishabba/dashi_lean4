import Mathlib
import CondensedMatter.BdGNambuParticleHoleExact
import CondensedMatter.YbSb2BdGSymmetryBoundary

namespace CondensedMatter
namespace YbSb2

/-!
ATTRIBUTION

SOURCE / MODEL INPUT:
A concrete YbSb2 effective model must supply the normal block h(k), pairing
blocks, momentum inversion, and the transpose/conjugation identities used by
the BdG construction.

DASHI DERIVATION:
Once those explicit algebraic identities are supplied, particle-hole symmetry
of the canonical Nambu block is a theorem, not an extra physical assertion.
That theorem then discharges the PHS field of SelectedINTBdGSourcePackage.

OPEN:
This adapter does not prove that the source's numerical Hamiltonian is
faithfully represented by a particular Mathlib matrix instance.
-/

variable {A : Type*} [AddGroup A]

structure YbSb2BdGAlgebraicModel where
  alg : BdGAlgebra (A := A)
  K : Type
  negK : K → K
  h : K → A
  Δ : K → A
  Δdag : K → A
  hypotheses : BdGPHSHypotheses alg negK h Δ Δdag

def YbSb2BdGAlgebraicModel.ParticleHoleSymmetry
    (M : YbSb2BdGAlgebraicModel (A := A)) : Prop :=
  ∀ k,
    BdGBlock.particleHole M.alg
      (canonicalBdG M.alg M.negK M.h M.Δ M.Δdag k)
    =
    BdGBlock.neg
      (canonicalBdG M.alg M.negK M.h M.Δ M.Δdag (M.negK k))

theorem YbSb2BdGAlgebraicModel.particleHoleSymmetry
    (M : YbSb2BdGAlgebraicModel (A := A)) :
    M.ParticleHoleSymmetry := by
  intro k
  exact canonicalBdG_particleHole
    M.alg M.negK M.h M.Δ M.Δdag M.hypotheses k

def YbSb2BdGAlgebraicModel.toSelectedINTBdGSourcePackage
    (M : YbSb2BdGAlgebraicModel (A := A)) :
    SelectedINTBdGSourcePackage where
  particleHoleSymmetry := M.ParticleHoleSymmetry
  particleHoleWitness := M.particleHoleSymmetry

theorem algebraic_model_selected_INT_not_DIII
    (M : YbSb2BdGAlgebraicModel (A := A)) :
    ¬ IsDIII (selectedINTBdGFacts M.toSelectedINTBdGSourcePackage) :=
  selected_INT_BdG_not_DIII M.toSelectedINTBdGSourcePackage

theorem algebraic_model_selected_INT_classD_compatible
    (M : YbSb2BdGAlgebraicModel (A := A)) :
    IsClassDCompatible
      (selectedINTBdGFacts M.toSelectedINTBdGSourcePackage) :=
  selected_INT_BdG_classD_compatible M.toSelectedINTBdGSourcePackage

end YbSb2
end CondensedMatter
