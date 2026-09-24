import Cuisine.NineSheet
import Cuisine.SafetyFabric
import Cuisine.SeveritySeam
import Cuisine.MdlPrimeModel
import Cuisine.SurfaceInterpretation
import Cuisine.KnotWeave
import Cuisine.SweetgrassSpine
import Cuisine.CanonicalGrid

/-!
# The cuisine ↔ trit / fibre / 369 / hyperfabric / Monster bridge, packaged

This module collects the transports proved in `Cuisine.UmamiTransport`,
`Cuisine.NineSheet`, `Cuisine.SafetyFabric` and `Cuisine.SeveritySeam` into a
single interface `CuisineToeBridge`, together with a canonical inhabitant
`cuisineToeBridge` and the composite theorem `cuisine_toe_bridge`.

The interface is the honest replacement for the earlier headline "the cuisine
lane has no formal link to the Monster / trit machinery": it has one, it is
typed, and every field below is a proved theorem, not a postulate or a `Bool`
ledger flag.  What the interface does *not* contain is equally deliberate — no
claim about the Monster group, moonshine as a theory, modular forms, or food.
-/

namespace Cuisine.ToeBridge

open AgdaMirror.DASHIAlgebra (Trit Stage6)
open AgdaMirror.Base369 (HexTruth rotateHex)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (SafetyEvidence)
open Cuisine.ToneSeparation (safetyLevel safetyRotate)
open Cuisine.UmamiTransport
open Cuisine.NineSheet
open Cuisine.SafetyFabric
open Cuisine.SeveritySeam
open Cuisine.MdlPrimeModel
open Cuisine.SurfaceInterpretation
open Cuisine.KnotWeave (KnotWeaveField knotWeaveFabric rotateField knotWeave_rotation_is_seasoning)
open Cuisine.SweetgrassSpine (SweetgrassRealisation sweetgrassRealisation)
open Cuisine.CanonicalGrid (blockMask blockProduct blockTwist blockAct BlockSymmetry)

/-- Everything the cuisine lane and the ternary / Monster spine genuinely share,
as a typed interface. -/
structure CuisineToeBridge where
  /-- Cuisine intensities transport to sections of the ternary fibre over the
  Monster prime base. -/
  transport : ℕ → Fabric
  /-- The transport carries the cuisine umami law to ternary XOR. -/
  transportHom : ∀ a b, transport (umamiCompose a b) = fabricXor (transport a) (transport b)
  /-- Every hyperfabric section arises this way. -/
  transportSurjective : Function.Surjective transport
  /-- Cubes are invisible: the transport is reduction modulo cubes. -/
  cubesNeutral : ∀ u, transport (umamiCompose u (umamiCompose u u)) = fabricZero
  /-- The dialectical action on sections is realised by cuisine-side seasoning
  with the radical. -/
  dialecticRealised : ∀ (s : Stage6) (u : ℕ),
    fabricAct s (transport u) =
      transport (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) (stageIndex s))
  /-- The Monster mask lattice embeds into cuisine intensities. -/
  maskEmbedding : ∀ m : MaskSSP, supportMask (transport (maskIntensity m)) = m
  /-- The supplied moonshine numeral is the successor of the intensity of the
  trivector mask. -/
  moonshinePoint : maskIntensity trivectorMask + 1 = AgdaMirror.Moonshine.repDim
  /-- A depth-nine sheet of the hyperfabric has `3^9 = 19683` sections. -/
  nineSheet : ∀ s : Finset SSP, s.card = 9 → Fintype.card (Supported s) = 19683
  /-- ... against which the supplied numerals are affine. -/
  moonshineAffine :
    AgdaMirror.Moonshine.repDim = 10 * 19683 + 53 ∧
      AgdaMirror.Moonshine.jCoefficient = 10 * 19683 + 54
  /-- Cuisine safety fields over the base are hyperfabric sections. -/
  safetySections : SafetyField ≃ Fabric
  /-- Fail-closed aggregation is a homomorphism onto the Monster mask
  semilattice. -/
  failClosedHom : ∀ x y : SafetyField,
    doubtMask (worstField x y) = fun p => (doubtMask x p || doubtMask y p)
  /-- The hexadic `369` carrier maps onto the cuisine safety carrier
  equivariantly for the rotation. -/
  toneQuotient : ∀ h : HexTruth, hexToSafety (rotateHex h) = safetyRotate (hexToSafety h)
  /-- ... but never compatibly with the fail-closed order: a seam is forced. -/
  seam : ∃ s : SafetyEvidence, safetyLevel (safetyRotate s) < safetyLevel s
  /-- The MDL prime-subset model of `Agda/MDL` has a unique optimum on the
  transported data, and it is the mask the intensity came from. -/
  mdlOptimal : ∀ m m' : MaskSSP,
    modelTotalLength (primeSubsetModel m') (transport (maskIntensity m)) =
        suppCost (transport (maskIntensity m)) ↔ m' = m
  /-- The guard's eight semantic surfaces have an explicit and injective
  interpretation into the repository's implementation carriers. -/
  surfaceTable : Function.Injective interpret
  /-- The whole affine group of the ternary fibre — rotations and reflections
  alike — is realised by cuisine operations (powering and seasoning). -/
  affineRealised : ∀ (e c u : ℕ) (p : SSP),
    fabricZMod (transport (affineOp e c u)) p =
      (e : ZMod 3) * fabricZMod (transport u) p + (c : ZMod 3)
  /-- The second typed cross-domain dependency of the cuisine record, the
  knot/weave/braid culture carrier, is the balanced-ternary digit: its fields
  over the Monster prime base are hyperfabric sections. -/
  knotWeaveSections : KnotWeaveField ≃ Fabric
  /-- ... and its knot → weave → braid cycle is again cuisine-side seasoning. -/
  knotWeaveRotation : ∀ (K : KnotWeaveField) (u : ℕ),
    knotWeaveSections K = transport u →
      knotWeaveSections (rotateField K) = transport (umamiCompose u radicalIntensity)
  /-- The Sweetgrass carrier spine — the motif vocabulary the cuisine record
  reaches through its attribution string — is realised: thirteen of its
  thirty-five motifs name types this repository defines, and those types are
  tied to one another and to the transport by the theorems bundled here. -/
  sweetgrassSpine : SweetgrassRealisation
  /-- In the canonical `3 · 5` grid on the supersingular base — the base-three
  reading of the prime order — the Monster trivector is exactly the `umami`
  column, and its product is the supplied `repDim`. -/
  moonshineColumn :
    blockMask .umami = trivectorMask ∧
      blockProduct .umami = AgdaMirror.Moonshine.repDim
  /-- Every rotation of the columns of that grid fixes the trivector, so the
  whole `243`-element column group is a moonshine symmetry. -/
  columnSymmetry : ∀ (v : Cuisine.SensoryCore.TasteDimension → Fin 3) (p : SSP),
    trivectorMask (blockTwist v p) = trivectorMask p
  /-- Adjoining the `369` rotation of the fibre gives an order-`3 ^ 6 = 729`
  commuting symmetry acting faithfully on the hyperfabric. -/
  gridSymmetryFaithful : ∀ g g' : BlockSymmetry, blockAct g = blockAct g' → g = g'

/-- The canonical inhabitant: every field is one of the theorems proved in this
library. -/
noncomputable def cuisineToeBridge : CuisineToeBridge where
  transport := umamiFabric
  transportHom := umamiFabric_compose
  transportSurjective := umamiFabric_surjective
  cubesNeutral := umamiFabric_cube
  dialecticRealised := fun s u => dialectic_stage_is_seasoning s u
  maskEmbedding := supportMask_umamiFabric_maskIntensity
  moonshinePoint := repDim_eq_maskIntensity_succ
  nineSheet := card_supported_nine
  moonshineAffine := ⟨by decide, by decide⟩
  safetySections := safetyFabric
  failClosedHom := doubtMask_worstField
  toneQuotient := hexToSafety_rotate
  seam := safety_seam_from_general
  mdlOptimal := mdl_optimal_of_maskIntensity
  surfaceTable := interpret_injective
  affineRealised := fabricZMod_affineOp
  knotWeaveSections := knotWeaveFabric
  knotWeaveRotation := knotWeave_rotation_is_seasoning
  sweetgrassSpine := sweetgrassRealisation
  moonshineColumn :=
    ⟨Cuisine.CanonicalGrid.trivector_eq_umami_column, Cuisine.CanonicalGrid.blockProduct_umami⟩
  columnSymmetry := Cuisine.CanonicalGrid.blockTwist_preserves_trivector
  gridSymmetryFaithful := fun _ _ h => Cuisine.CanonicalGrid.blockAct_faithful h

@[simp] theorem cuisineToeBridge_transport : cuisineToeBridge.transport = umamiFabric := rfl

/-- **Composite statement.**  The cuisine lane admits a proved, structure-
preserving transport into the ternary / hyperfabric / Monster machinery of the
`Synthesis` spine, whose value on the trivector mask is the supplied moonshine
numeral. -/
theorem cuisine_toe_bridge :
    ∃ B : CuisineToeBridge, B.transport = umamiFabric :=
  ⟨cuisineToeBridge, rfl⟩

end Cuisine.ToeBridge
