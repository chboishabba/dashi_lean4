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

/-- An actual source-to-telescope group isomorphism is mandatory.
The original #1244 real wild-satellite exterior identification
remains a SEPARATE unproved geometry input. -/
structure SourceTelescopeGroupCertificate
    (Source : Type*) [Group Source] where
  TelescopeGroup : Type
  instGroup : Group TelescopeGroup
  groupEquivalence : Source ≃* TelescopeGroup

attribute [instance] SourceTelescopeGroupCertificate.instGroup

/-- Every abstract source holonomy admits an all-depth telescope
receiver with EXACTLY the same class functions and even the
same raw matrix after transporting the source word.
This is a GROUP result, not metric/curvature equivalence. -/
def telescopeReceiver
    (cert : SourceTelescopeGroupCertificate Source)
    (sourceHolonomy : Source →* Receiver) :
    cert.TelescopeGroup →* Receiver :=
  sourceHolonomy.comp cert.groupEquivalence.symm.toMonoidHom

theorem telescopeMatchesEverySourceWord
    (cert : SourceTelescopeGroupCertificate Source)
    (sourceHolonomy : Source →* Receiver)
    (word : Source) :
    telescopeReceiver cert sourceHolonomy
      (cert.groupEquivalence word) =
    sourceHolonomy word := by
  change sourceHolonomy
    (cert.groupEquivalence.symm (cert.groupEquivalence word)) =
    sourceHolonomy word
  simp

theorem telescopeMatchesEverySourceObservable
    {Observed : Type*}
    (cert : SourceTelescopeGroupCertificate Source)
    (sourceHolonomy : Source →* Receiver)
    (observable : Receiver → Observed)
    (word : Source) :
    observable
      (telescopeReceiver cert sourceHolonomy
        (cert.groupEquivalence word)) =
    observable (sourceHolonomy word) := by
  rw [telescopeMatchesEverySourceWord]

/-- A C3 rotation of the entire group and its conjugate/renamed
telescope representation may share observables. No spatial
Euclidean isometry is constructed on the CW telescope. -/
theorem telescopeMatchesRotatedWords
    {Observed : Type*}
    (cert : SourceTelescopeGroupCertificate Source)
    (sourceHolonomy : Source →* Receiver)
    (observable : Receiver → Observed)
    (rotate : Source ≃* Source)
    (word : Source) :
    observable
      (telescopeReceiver cert sourceHolonomy
        (cert.groupEquivalence (rotate word))) =
    observable (sourceHolonomy (rotate word)) := by
  rw [telescopeMatchesEverySourceWord]

end DASHIHornC3AcyclicTelescopeCut
