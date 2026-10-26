import Mathlib
import Integration.DASHITOE.HornHopfClaspVsHatcherF2NoGoCut

/-!
# Hatcher all-depth extension discriminator: finite nonabelian SU3
# can be a false positive when its image is 2-step nilpotent.

ORIGINAL ROOTS:
Hatcher, Algebraic Topology Example 2B.2, pp171-172:
old meridian maps to a commutator of children at EACH depth.
Classical derived-series theory: every depth-two nested
commutator is trivial in a group of nilpotency class ≤2.
Classical Weyl/Heisenberg SU3 clock/shift example supplies
a nontrivial FIRST commutator but trivial second-depth word.
The previous original horn #1244 Abelians BIDI exact no-go is
strictly weaker (target abelian). #1247 owns chosen unrelated W.
#1249 owns the source-independent exact Python finite SU3 audit.
Nielsen-Schreier / Magnus free-group residual nilpotence imply
the stronger paper corollary perfect G_A has no nontrivial map
to a free group. These ORIGINAL classic theorems are NOT
kernel-proved below.

NEW narrow source-conditional Lean consumer: a true marked
TWO-LEVEL Hatcher word map and a class-2 receiver assumption
force receiver root identity. No actual stage geometry, 3D
wild meridian, native Lean kernel or physical prediction.
-/

namespace DASHIHornNilpotentReceiverNoGo

variable {G H : Type*} [Group G] [Group H]

def comm (a b : G) : G := a * b * a⁻¹ * b⁻¹

/-- Any homomorphism maps exact commutator words to commutators.
This group-level functoriality requires no geometric assumptions. -/
theorem imageComm (rho : G →* H) (a b : G) :
    rho (comm a b) =
      DASHIHornHopfClaspNoGo.comm (rho a) (rho b) := by
  simp [comm, DASHIHornHopfClaspNoGo.comm, map_mul, map_inv]

/-- A two-step nilpotent receiver can show a first-level
nontrivial Wilson commutator, but NOT a source-compatible
nontrivial depth-two parent Hatcher commutator. -/
theorem twoLevelHatcherRootVanishes
    (rho : G →* H)
    (root a b c d : G)
    (hMarked : root = comm (comm a b) (comm c d))
    (hClassTwo :
      ∀ x y u v : H,
        DASHIHornHopfClaspNoGo.comm
          (DASHIHornHopfClaspNoGo.comm x y)
          (DASHIHornHopfClaspNoGo.comm u v) = 1) :
    rho root = 1 := by
  rw [hMarked, imageComm, imageComm, imageComm]
  exact hClassTwo (rho a) (rho b) (rho c) (rho d)

/-- A nontrivial source-selected W cannot be realised by a
representation into a class-2 receiver subgroup, EVEN THOUGH
that subgroup has nontrivial first-depth SU3 commutators. -/
theorem selectedWNeedsBeyondClassTwo
    (rho : G →* H)
    (root a b c d : G)
    (hMarked : root = comm (comm a b) (comm c d))
    (hClassTwo :
      ∀ x y u v : H,
        DASHIHornHopfClaspNoGo.comm
          (DASHIHornHopfClaspNoGo.comm x y)
          (DASHIHornHopfClaspNoGo.comm u v) = 1)
    (hNontrivial : rho root ≠ 1) : False :=
  hNontrivial
    (twoLevelHatcherRootVanishes rho root a b c d
      hMarked hClassTwo)

end DASHIHornNilpotentReceiverNoGo
