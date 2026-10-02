import Mathlib

namespace CondensedMatter

/-!
ATTRIBUTION

EXTERNAL SOURCE:
Eric C. Rowell, "Braids, Motions and Topological Quantum Computing",
arXiv:2208.11762v1 (2022), surveys that Ising anyons / Majorana zero modes
have finite braid-group image and are not universal by braiding alone.

This file records that source claim as a promotion boundary.  It does not
derive braid-image non-density in SU(2) from first principles.
-/

structure IsingMajoranaUniversalitySourceClaim where
  braidingAloneUniversal : Prop
  notUniversalByBraidingAlone : ¬ braidingAloneUniversal

def canonicalIsingMajoranaUniversalitySourceClaim :
    IsingMajoranaUniversalitySourceClaim where
  braidingAloneUniversal := False
  notUniversalByBraidingAlone := by simp

theorem canonical_ising_braiding_not_universal :
    ¬ canonicalIsingMajoranaUniversalitySourceClaim.braidingAloneUniversal :=
  canonicalIsingMajoranaUniversalitySourceClaim.notUniversalByBraidingAlone

structure UniversalCompletionResource where
  Resource : Type
  resource : Resource

end CondensedMatter
