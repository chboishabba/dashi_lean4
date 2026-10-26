import Mathlib
import Integration.DASHITOE.HornHopfClaspVsHatcherF2NoGoCut

/-!
# Hatcher stage maps: injective but NEVER group-theoretically split

SOURCE ROOTS:
Hatcher, Algebraic Topology Example 2B.2 printed pp171–172 owns
the genuine injective stage homomorphism from F_(2^n) to F_(2^(n+1))
sending each old free basis meridian to a commutator of two fresh
generators. This file does NOT reclaim his stage injection result.
The elementary obstruction to SPLITTING follows from the ORIGINAL
Hatcher commutator formula and ordinary abelianization.

Prior repo owner: Agda horn #1244 actual C3 geometry, group transport,
and original abelian holonomy blindness; earlier Lean #84 module
HornHopfClaspVsHatcherF2NoGoCut owns an abelian detector killing any
commutator. This module explicitly REUSES that earlier proof instead
of creating another source group/groupoid engine.

NEW consumer: If a source free-stage G has a NONTRIVIAL abelian
character of any old generator, and the next stage H maps it to
a commutator, then NO homomorphic r:H→G can satisfy r∘f=id_G.
Hence no topological stage retraction Y_(n+1)→Y_n can exist
that is a left inverse to the ORIGINAL Hatcher inclusion on pi1.
This DOES NOT construct the actual 3D linked Hatcher X_n/Y_n
in the chosen supported satellite, and does not prove source
Euclidean meridian lengths or a native Lean kernel receipt.
-/

namespace DASHIHornStageNonsplitting

variable {G H A : Type*} [Group G] [Group H] [CommGroup A]

/-- A more general obstruction than the free-group case: ONE
nontrivial abelian character on ONE commutator-mapped generator
already excludes any left-inverse homomorphism. -/
theorem noStageRetractionAtCommutator
    (f : G →* H) (r : H →* G)
    (character : G →* A)
    (oldMeridian : G) (left right : H)
    (hStage : f oldMeridian =
      DASHIHornHopfClaspNoGo.comm left right)
    (hNonzero : character oldMeridian ≠ 1)
    (hLeftInverse : ∀ x : G, r (f x) = x) : False := by
  have hmap :
      r (DASHIHornHopfClaspNoGo.comm left right) =
        DASHIHornHopfClaspNoGo.comm (r left) (r right) := by
    simp [DASHIHornHopfClaspNoGo.comm, map_mul, map_inv]
  have hZero : character (r (f oldMeridian)) = 1 := by
    rw [hStage, hmap]
    exact DASHIHornHopfClaspNoGo.anyAbelianDetectorKillsCommutator
      character (r left) (r right)
  have hOldZero : character oldMeridian = 1 := by
    calc
      character oldMeridian =
          character (r (f oldMeridian)) := by
            rw [hLeftInverse oldMeridian]
      _ = 1 := hZero
  exact hNonzero hOldZero

/-- This abstract endpoint interface is what a 3D exterior
map Y_(n+1)→Y_n would produce at pi1 level IF it retracted
the source inclusion. It cannot be inhabited whenever an
old marked meridian has nonzero abelian character. -/
theorem noPi1RetractFromHatcherChildCommutator
    (inclusion : G →* H) (putativeRetraction : H →* G)
    (abelianWitness : G →* A)
    (meridian : G) (child1 child2 : H)
    (hMarked : inclusion meridian =
      DASHIHornHopfClaspNoGo.comm child1 child2)
    (hDetected : abelianWitness meridian ≠ 1)
    (hRetraction : ∀ x : G,
      putativeRetraction (inclusion x) = x) : False :=
  noStageRetractionAtCommutator inclusion putativeRetraction
    abelianWitness meridian child1 child2
    hMarked hDetected hRetraction

end DASHIHornStageNonsplitting
