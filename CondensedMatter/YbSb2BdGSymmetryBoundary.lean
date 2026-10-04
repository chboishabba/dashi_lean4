import Mathlib
import CondensedMatter.YbSb2INTNonunitarySelected

namespace CondensedMatter
namespace YbSb2

/-!
ATTRIBUTION

Source claims from Kataria et al., arXiv:2601.07460 / PRL accepted 3 Aug 2026:
* the low-energy normal state is modeled by a 3D massive Dirac Hamiltonian;
* the INT state is inserted into a BdG Hamiltonian;
* the calculated quasiparticle DOS is fully gapped;
* the calculated surface spectral function has zero-energy SABS and a
  linearly dispersing Majorana branch at Γ.

DASHI contribution in this file:
* a symmetry-classification firewall separating source-modeled BdG
  particle-hole symmetry from time-reversal symmetry;
* a theorem that a state already proved to break TR modulo gauge cannot be
  promoted to a DIII witness merely because it is BdG;
* a typed surface-mode witness that distinguishes zero energy,
  particle-hole self-conjugacy, boundary localization and dispersion.

Open physical identification:
* no theorem here derives the paper's numerical transfer-matrix spectrum;
* no theorem here identifies a measured zero-bias signal with the modeled
  Majorana branch.
-/

/-- Minimal symmetry facts needed for Altland-Zirnbauer classification. -/
structure BdGSymmetryFacts where
  particleHole : Prop
  timeReversal : Prop
  chiral : Prop

/--
A DIII witness requires both particle-hole and time-reversal symmetries.
We intentionally keep this as a proposition rather than assigning an AZ label
from incomplete data.
-/
def IsDIII (S : BdGSymmetryFacts) : Prop :=
  S.particleHole ∧ S.timeReversal

/-- A class-D-compatible boundary: PHS present, TR absent. -/
def IsClassDCompatible (S : BdGSymmetryFacts) : Prop :=
  S.particleHole ∧ ¬ S.timeReversal

theorem trsb_excludes_DIII
    (S : BdGSymmetryFacts)
    (hTRSB : ¬ S.timeReversal) :
    ¬ IsDIII S := by
  intro h
  exact hTRSB h.2

theorem phs_and_trsb_is_classD_compatible
    (S : BdGSymmetryFacts)
    (hPHS : S.particleHole)
    (hTRSB : ¬ S.timeReversal) :
    IsClassDCompatible S :=
  ⟨hPHS, hTRSB⟩

/--
Material-specific bridge: the selected finite INT state already has an exact
proof of broken TR modulo represented global gauge.
-/
def selectedINTTimeReversal : Prop :=
  intTRSystem.TRGaugeEquivalent .selected

theorem selected_INT_not_time_reversal :
    ¬ selectedINTTimeReversal :=
  selectedINTBreaksTRUpToGauge

/--
A source/model package may independently provide BdG particle-hole symmetry.
Once that is supplied, the selected INT lane is class-D compatible and not DIII.
-/
structure SelectedINTBdGSourcePackage where
  particleHoleSymmetry : Prop
  particleHoleWitness : particleHoleSymmetry

def selectedINTBdGFacts
    (P : SelectedINTBdGSourcePackage) :
    BdGSymmetryFacts where
  particleHole := P.particleHoleSymmetry
  timeReversal := selectedINTTimeReversal
  chiral := False

theorem selected_INT_BdG_not_DIII
    (P : SelectedINTBdGSourcePackage) :
    ¬ IsDIII (selectedINTBdGFacts P) :=
  trsb_excludes_DIII _ selected_INT_not_time_reversal

theorem selected_INT_BdG_classD_compatible
    (P : SelectedINTBdGSourcePackage) :
    IsClassDCompatible (selectedINTBdGFacts P) :=
  phs_and_trsb_is_classD_compatible _
    P.particleHoleWitness
    selected_INT_not_time_reversal

/--
A zero-energy surface feature is not by itself a Majorana theorem.
The stronger witness keeps the independent obligations explicit.
-/
structure MajoranaSurfaceWitness where
  Mode : Type
  selectedMode : Mode
  zeroEnergy : Prop
  zeroEnergyWitness : zeroEnergy
  particleHoleSelfConjugate : Prop
  particleHoleSelfConjugateWitness : particleHoleSelfConjugate
  boundaryLocalized : Prop
  boundaryLocalizedWitness : boundaryLocalized
  linearlyDispersingNearGamma : Prop
  linearlyDispersingNearGammaWitness : linearlyDispersingNearGamma

/--
Source-scoped statement corresponding to the effective-model result in the
paper.  It remains a modeled surface witness, not an experimental observation.
-/
structure KatariaEffectiveModelSurfaceResult where
  witness : MajoranaSurfaceWitness

end YbSb2
end CondensedMatter
