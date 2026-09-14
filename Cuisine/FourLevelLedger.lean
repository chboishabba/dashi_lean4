import Cuisine.ToeBridge
import Cuisine.CodecTransport
import Cuisine.SupervoxelClopen
import Cuisine.LoomBridge

/-!
# The four-level bridge ledger

The question this file answers is *how strong* the link between the cuisine lane
and each other lane of the corpus actually is.  Four levels are distinguished,
and never conflated:

1. `vocabulary` — the two lanes share words only.  No import path, no shared
   type, no map.
2. `recordDependency` — a cuisine record really does store a value of a type
   defined in the other lane (or reaches it through the Agda import graph), but
   the stored value carries no information beyond its presence.
3. `sharedType` — the two lanes are instances of one implementation-level type
   or interface defined in this repository, so statements can be compared, but
   no structure-preserving map between them is proved.
4. `provedTransport` — there is a checked map (or equivalence) between cuisine
   data and the other lane's carrier which preserves the structure at issue.

`bridgeLevel` is the assignment.  It is a *judgement*, and the point of
`LedgerWitnesses` is that the judgement cannot inflate silently: every lane
recorded at `provedTransport` has a field in that structure holding the actual
theorem, and every lane recorded lower has a field holding the actual proved
obstruction or audit fact that keeps it there.  `fourLevelLedger` inhabits it.

Nothing in this file introduces new mathematics; it is a typed index of what the
other modules prove.
-/

namespace Cuisine.FourLevelLedger

open AgdaMirror.DASHIAlgebra (Trit Stage6)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.UmamiTransport

/-- The four strengths of link. -/
inductive BridgeLevel
  | vocabulary | recordDependency | sharedType | provedTransport
  deriving DecidableEq, Repr, Fintype

/-- The lanes whose link to cuisine is at issue. -/
inductive TargetLane
  | monsterPrimeBase | moonshineNumerals | mdlTwoPartCode | base369Tone
  | tritAlgebra | dialecticStage | codecKernel | supervoxelRefinement
  | loomRelationAlgebra | klueverSpiral | hyperfabricBodyMemoryBridge
  | sweetgrassMotifFabric | cubicalLibrary
  deriving DecidableEq, Repr, Fintype

open BridgeLevel TargetLane

/-- **The ledger.**  See `CUISINE_FOUR_LEVEL_MAP.md` for the evidence behind each
entry; the witnesses are collected in `LedgerWitnesses` below. -/
def bridgeLevel : TargetLane → BridgeLevel
  | monsterPrimeBase => provedTransport
  | moonshineNumerals => provedTransport
  | mdlTwoPartCode => provedTransport
  | base369Tone => provedTransport
  | tritAlgebra => provedTransport
  | dialecticStage => provedTransport
  | codecKernel => provedTransport
  | supervoxelRefinement => provedTransport
  | loomRelationAlgebra => sharedType
  | klueverSpiral => sharedType
  | hyperfabricBodyMemoryBridge => recordDependency
  | sweetgrassMotifFabric => recordDependency
  | cubicalLibrary => vocabulary

/-- All thirteen lanes, in the order used throughout the map. -/
def allLanes : List TargetLane :=
  [monsterPrimeBase, moonshineNumerals, mdlTwoPartCode, base369Tone, tritAlgebra,
    dialecticStage, codecKernel, supervoxelRefinement, loomRelationAlgebra,
    klueverSpiral, hyperfabricBodyMemoryBridge, sweetgrassMotifFabric, cubicalLibrary]

theorem allLanes_complete (t : TargetLane) : t ∈ allLanes := by
  cases t <;> decide

theorem allLanes_nodup : allLanes.Nodup := by decide

/-- The lanes at each level. -/
def lanesAt (l : BridgeLevel) : List TargetLane :=
  allLanes.filter (fun t => bridgeLevel t == l)

theorem lanesAt_provedTransport :
    lanesAt provedTransport =
      [monsterPrimeBase, moonshineNumerals, mdlTwoPartCode, base369Tone,
        tritAlgebra, dialecticStage, codecKernel, supervoxelRefinement] := by
  decide

theorem lanesAt_sharedType : lanesAt sharedType = [loomRelationAlgebra, klueverSpiral] := by
  decide

theorem lanesAt_recordDependency :
    lanesAt recordDependency = [hyperfabricBodyMemoryBridge, sweetgrassMotifFabric] := by
  decide

theorem lanesAt_vocabulary : lanesAt vocabulary = [cubicalLibrary] := by
  decide

/-- **The witnesses.**  A level-4 entry must be backed by a transport theorem; a
level-3 entry by a shared type together with a proved obstruction to promoting
it; a level-2 entry by the audit showing the stored value carries nothing; the
level-1 entry only by the record that nothing in this repository connects the
two. -/
structure LedgerWitnesses : Prop where
  /-- Monster prime base: the cuisine monoid maps onto ternary sections over the
  fifteen supersingular primes, and the mask lattice embeds back. -/
  monster :
    Function.Surjective umamiFabric ∧
      ∀ m : MaskSSP, supportMask (umamiFabric (maskIntensity m)) = m
  /-- Moonshine: the supplied numerals are the cuisine intensity of the
  trivector mask, shifted.  A numeral identity, and nothing about the Monster
  group or the `j`-invariant. -/
  moonshine :
    maskIntensity Synthesis.MoonshineBase.trivectorMask + 1 = AgdaMirror.Moonshine.repDim ∧
      maskIntensity Synthesis.MoonshineBase.trivectorMask = 196882
  /-- MDL: for a transported cuisine intensity, the code-optimal subset of
  supersingular primes is exactly its mask, uniquely. -/
  mdl : ∀ m m' : MaskSSP,
    Cuisine.MdlPrimeModel.modelTotalLength (Cuisine.MdlPrimeModel.primeSubsetModel m')
        (umamiFabric (maskIntensity m))
      = Cuisine.MdlPrimeModel.suppCost (umamiFabric (maskIntensity m)) ↔ m' = m
  /-- `369`: the hexadic residual carrier maps onto cuisine safety verdicts,
  rotation-equivariantly. -/
  base369 :
    Function.Surjective Cuisine.SeveritySeam.hexToSafety ∧
      ∀ h, Cuisine.SeveritySeam.hexToSafety (AgdaMirror.Base369.rotateHex h) =
        Cuisine.ToneSeparation.safetyRotate (Cuisine.SeveritySeam.hexToSafety h)
  /-- Trit algebra: the knot/weave/braid carrier *is* the balanced-ternary
  digit, and knot-weave fields over the Monster base are hyperfabric sections. -/
  trit :
    Function.Bijective Cuisine.KnotWeave.knotWeaveEquivTrit ∧
      Function.Bijective Cuisine.KnotWeave.knotWeaveFabric
  /-- Dialectic: each stage of the sixfold dialectic acts on a transported
  cuisine blend as seasoning with the radical intensity. -/
  dialectic : ∀ (s : Stage6) (u : ℕ),
    fabricAct s (umamiFabric u) =
      umamiFabric (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) (stageIndex s))
  /-- Codec: combining blends is the affine codec operation, and the
  self-seasoning quotient has the supplied codec orbit count. -/
  codec :
    (∀ a b : ℕ, Cuisine.CodecTransport.umamiCodec (umamiCompose a b) =
        Cuisine.CodecTransport.umamiCodec a + Cuisine.CodecTransport.umamiCodec b + 1) ∧
      Cuisine.CodecTransport.blendDoubleOrbits = 7174454
  /-- Supervoxel: the cuisine transport is the depth-15 clopen-ball projection,
  and the refinement order on cuisine constraints is the Monster mask order. -/
  supervoxel :
    (∀ a b : ℕ, umamiFabric a = umamiFabric b ↔
        Cuisine.SupervoxelClopen.Cyl 15 (Cuisine.SupervoxelClopen.intensityStream a)
          (Cuisine.SupervoxelClopen.intensityStream b)) ∧
      ∀ m m' : MaskSSP,
        Cuisine.SupervoxelClopen.FineExtendsCoarse
            Cuisine.SupervoxelClopen.cuisineNeutrality m m' ↔ ∀ p, m p = true → m' p = true
  /-- Loom: a shared refinement interface — but the nine relation types do not
  carry the nonary rotation, so the shared numeral is not a map. -/
  loom :
    (∀ t, Cuisine.LoomBridge.rootOfBucket (AgdaMirror.Loom.bucketFor t) =
        AgdaMirror.Loom.relationRootFor t) ∧
      ∀ σ : AgdaMirror.Loom.LoomRelationType → AgdaMirror.Loom.LoomRelationType,
        (∀ t, σ t ≠ t) → (∀ t, σ (σ (σ t)) = t) →
          (∀ t, AgdaMirror.Loom.relationRootFor (σ t) =
            AgdaMirror.Loom.relationRootFor t) → False
  /-- Klüver spiral: a finite referent exists for the guard's `spiral` surface,
  but four form constants do not inject into the ternary digit. -/
  spiral : ¬ ∃ f : Cuisine.SpiralCarrier.KlueverForm → AgdaMirror.Base369.TriTruth,
    Function.Injective f
  /-- Hyperfabric body-memory bridge: the cuisine record stores it, and the part
  it stores is a singleton — a constant, not information. -/
  hyperfabricRecord : ∀ x y : Cuisine.HyperfabricGuard.HyperfabricFacet, x = y
  /-- Sweetgrass: reached only through a `String` attribution, and the motif the
  record names is realised by no type in this repository. -/
  sweetgrass :
    Cuisine.SweetgrassSpine.realise
      Cuisine.SweetgrassSpine.CarrierMotif.motifSweetgrassBraidFabric
      = Cuisine.SweetgrassSpine.SpineCarrier.unrealised
  /-- Cubical: recorded at the vocabulary level.  The only claim made is the
  ledger entry itself; the evidence is the Agda import closure, which contains
  no cubical module, and there is no Lean cubical material. -/
  cubical : bridgeLevel cubicalLibrary = vocabulary

/-- The ledger is inhabited by the theorems the other modules prove. -/
theorem fourLevelLedger : LedgerWitnesses where
  monster := ⟨umamiFabric_surjective, supportMask_umamiFabric_maskIntensity⟩
  moonshine := ⟨repDim_eq_maskIntensity_succ, maskIntensity_trivector⟩
  mdl := Cuisine.MdlPrimeModel.mdl_optimal_of_maskIntensity
  base369 := ⟨Cuisine.SeveritySeam.hexToSafety_surjective, Cuisine.SeveritySeam.hexToSafety_rotate⟩
  trit := ⟨Cuisine.KnotWeave.knotWeaveEquivTrit.bijective,
    Cuisine.KnotWeave.knotWeaveFabric.bijective⟩
  dialectic := dialectic_stage_is_seasoning
  codec := ⟨Cuisine.CodecTransport.umamiCodec_compose,
    Cuisine.CodecTransport.blendDoubleOrbits_value⟩
  supervoxel := ⟨Cuisine.SupervoxelClopen.umamiFabric_eq_iff_ball,
    Cuisine.SupervoxelClopen.neutrality_refines_iff⟩
  loom := ⟨Cuisine.LoomBridge.rootOfBucket_bucketFor,
    fun σ hfree h3 hroot => Cuisine.LoomBridge.no_free_order3_root_preserving σ hfree h3 hroot⟩
  spiral := Cuisine.SpiralCarrier.no_injective_klueverForm_to_trit
  hyperfabricRecord := fun x y => Subsingleton.elim x y
  sweetgrass := Cuisine.SweetgrassSpine.sweetgrass_itself_unrealised
  cubical := rfl

end Cuisine.FourLevelLedger
