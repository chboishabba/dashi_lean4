import Mathlib
import Integration.DASHITOE.HornFiniteDepthWilsonWordNonidentifiabilityCut

/-!
# All-depth C3 Hatcher commutator mapping telescope: CW comparator

Original classical mathematical owners:
* Hatcher, Algebraic Topology, Example 2B.2 (horn free-group stages
  F_(2^n), injective child-commutator transition).
* Hatcher, Algebraic Topology, Section 3.F (mapping telescope as
  countable CW mapping cylinders, finite truncations retract to last
  stage, direct-limit homology). Fundamental groups follow from
  ordinary Seifert-van Kampen and CW compactness.
* Hatcher Example 1.21 rose graph free group, already a pinned
  original Deicyde/hatcher-at theorem donor.
* Original C3 geometry and source group PR #1244; selected W PR #1247.
  Existing hyperfabric #1249 and Lean #84 own finite-word no-go.

DERIVED CONSEQUENCE (not an original discovery of telescope topology):
For R_n = wedge of 3*2^n circles, let the pointed cellular map
f_n : R_n -> R_(n+1) wrap each old circle along the commutator
of the two new sector-preserving child circles. It commutes with
C3 cyclic permutation of sector indices. The genuine topological
mapping telescope T of the f_n has
  pi1(T) = colim_n F_(3*2^n) = G_A * G_A * G_A
as an ABSTRACT group. Its finite truncations deformation retract
onto R_n, so H_k(T)=0 for k>=2 and H_1(T)=colim H_1(R_n)=0
because every f_n is ZERO on abelianization. Yet pi1(T) != 1
because original Hatcher transition homomorphisms are injective.
Thus T is an acyclic noncontractible 2-dimensional countable
CW model with nontrivial abstract flat SU3 LOCAL SYSTEMS
whenever original source group representations are provided.

This is not a 3D embedded wild sphere, not a smooth manifold,
not a bounded Euclidean gauge connection and not an actual
source-model identification of π1(E). The true telescope CW
construction and Hatcher group isomorphism are EXTERNAL source
theorems, not kernel-proved in this file.

Below: exact finite rank counts and the ALL-DEPTH receiver
comparison are source-conditional scalar/group consumers,
without inventing a native CW realization theorem.
-/

namespace DASHIHornC3AcyclicTelescopeCut

/-- The three sectors remain distinct in the free R_n rose. -/
def generatorCount (n : ℕ) : ℕ := 3 * 2 ^ n

/-- There are 3(2^n-1) mapping-cylinder 2-cells
once we have passed through levels 0, ..., n-1. -/
def relationCount (n : ℕ) : ℕ := 3 * (2 ^ n - 1)

/-- Count all circles in levels 0,...,n. -/
def totalOneCells (n : ℕ) : ℕ := 3 * (2 ^ (n+1) - 1)

theorem finiteCellCount (n : ℕ) :
    totalOneCells n = relationCount n + generatorCount n := by
  dsimp [totalOneCells, relationCount, generatorCount]
  have hpow : 2 ^ (n+1) = 2^n * 2 := by
    rw [pow_succ]
  omega

/-- The actual finite telescope retracts to its last rose; this
formal scalar count is NOT itself a topological deformation retract
proof. It makes the rank of the cellular d2 matrix falsifiable. -/
theorem finiteThreeSectorStageCount (n : ℕ) :
    generatorCount n = 3 * 2^n := rfl

variable {Source Receiver : Type*}
  [Group Source] [Group Receiver]

/-- The exact CW mapping telescope group must be inhabited by
the ORIGINAL Hatcher direct-limit source equivalence, which is
NOT constructed in this Lean module. The group equivalence is
an explicit parameter and cannot be conjured from a finite
rose or the connectedness of a cover. -/
variable {Telescope : Type*} [Group Telescope]

/-- Any chosen all-depth source representation transports through
the genuine group isomorphism to the telescope. This does NOT
transport Euclidean metric, smooth gauge regularity or curvature. -/
def telescopeReceiver
    (sourceToTelescope : Source ≃* Telescope)
    (sourceHolonomy : Source →* Receiver) :
    Telescope →* Receiver :=
  sourceHolonomy.comp sourceToTelescope.symm.toMonoidHom

theorem telescopeMatchesEverySourceWord
    (sourceToTelescope : Source ≃* Telescope)
    (sourceHolonomy : Source →* Receiver)
    (word : Source) :
    telescopeReceiver sourceToTelescope sourceHolonomy
      (sourceToTelescope word) =
    sourceHolonomy word := by
  change sourceHolonomy
    (sourceToTelescope.symm (sourceToTelescope word)) =
    sourceHolonomy word
  simp

theorem telescopeMatchesEverySourceObservable
    {Observed : Type*}
    (sourceToTelescope : Source ≃* Telescope)
    (sourceHolonomy : Source →* Receiver)
    (observable : Receiver → Observed)
    (word : Source) :
    observable
      (telescopeReceiver sourceToTelescope sourceHolonomy
        (sourceToTelescope word)) =
    observable (sourceHolonomy word) := by
  rw [telescopeMatchesEverySourceWord]

/-- The source C3 automorphism can be observed on the other
model's receiver as a group homomorphism, without thereby
producing a C3 spatial rotation in ambient Euclidean R3. -/
theorem telescopeMatchesRotatedWords
    {Observed : Type*}
    (sourceToTelescope : Source ≃* Telescope)
    (sourceHolonomy : Source →* Receiver)
    (observable : Receiver → Observed)
    (rotate : Source ≃* Source)
    (word : Source) :
    observable
      (telescopeReceiver sourceToTelescope sourceHolonomy
        (sourceToTelescope (rotate word))) =
    observable (sourceHolonomy (rotate word)) := by
  rw [telescopeMatchesEverySourceWord]

end DASHIHornC3AcyclicTelescopeCut
