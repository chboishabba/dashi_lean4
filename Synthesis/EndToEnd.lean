import Synthesis.Hyperfabric
import Synthesis.WalkGeometry
import Synthesis.MoonshineBase
import Synthesis.CodecBridge
import Synthesis.Vec15Fibre
import Synthesis.WalkArithmetic
import Synthesis.StatisticsFibre
import Synthesis.InferenceFibre
import Synthesis.PhysicsInterfaces
import Synthesis.SpinCoverBridge
import Synthesis.ExponentFibre
import Synthesis.MonsterOrder
import Synthesis.RelationSeam
import Synthesis.CircleCover

/-!
# Synthesis layer 4: the checkable end-to-end statement

This file assembles the three preceding layers into one structure,
`CrossDomainSpine`, whose fields are *propositions and equivalences* — never
Boolean flags, names, or unproved interfaces — and exhibits a canonical
inhabitant `crossDomainSpine`, every field of which is discharged by a theorem
proved in this repository.

It also proves one genuinely composite statement, `spine_end_to_end`, which
chains all four layers: the dialectical successor drives the ternary tone of a
Monster-indexed hyperfabric, the refined half-trit information is provably lost
by the collapse, and the resulting support mask lives in the supplied Monster
mask geometry where the constant projection strictly contracts distance.

## What this is *not*

The composite theorem is a statement about finite carriers: a 3-element tone
set, 4- and 6-element dialectical cycles, a 15-element index of supersingular
primes, and functions between them.  It is **not** a theory of everything, and
nothing here establishes any physical claim.  The honest content is: the pieces
of the supplied material that really do connect, connect in exactly the ways
stated below, and the ways in which they provably fail to connect are recorded
as negative theorems (`fourfoldObstruction`, `supportObstruction`,
`halfCollapseLossy`) rather than being glossed over.
-/

namespace Synthesis.EndToEnd

open AgdaMirror (Ultrametric)
open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Trit Stage6 next6)
open AgdaMirror.LogicTlurey (Stage next)
open AgdaMirror.TritBridge (toTriTruth tritXor rotTrit)
open AgdaMirror.HalfTritMod (HalfTrit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.DialecticTone
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.WalkGeometry
open Synthesis.MoonshineBase
open Synthesis.CodecBridge
open Synthesis.Vec15Fibre
open Synthesis.WalkArithmetic
open Synthesis.StatisticsFibre

/-! ## The spine interface -/

/-- The cross-domain spine: the interface that the supplied material genuinely
supports.  Every field is a proposition or an equivalence; the negative fields
record the connections that provably do *not* exist. -/
structure CrossDomainSpine where
  /-- Layer 0: the shared ternary tone primitive. -/
  toneEquiv : Trit ≃ TriTruth
  toneXor : ∀ a b, toneEquiv (tritXor a b) = triXor (toneEquiv a) (toneEquiv b)
  toneIsZMod3 : TriTruth ≃ ZMod 3
  /-- Layer 0': the half-trit fibre, its index, and the loss it incurs. -/
  halfIndex : HalfTrit ≃ Fin 5
  halfCollapseLossy : ¬ Function.Injective halfTone
  /-- Quantitative form of the loss: the refinements of a ternary section are
  counted by its non-zero fibres. -/
  collapseFibreCount : ∀ F : Fabric,
    Fintype.card {H : HalfFabric // collapse H = F} =
      2 ^ (Finset.univ.filter (fun p : SSP => F p ≠ Trit.zer)).card
  /-- Layer 1: the dialectical carriers. -/
  sixfoldTone : Stage6 → TriTruth
  sixfoldEquivariant : ∀ s, sixfoldTone (next6 s) = rotateTri (sixfoldTone s)
  fourfoldObstruction : ¬ ∃ f : Stage → TriTruth, ∀ s, f (next s) = rotateTri (f s)
  /-- The sixfold equivariant tone is essentially unique: the only ones are the
  three rotations of `stage6Tone`. -/
  sixfoldToneUnique : ∀ f : Stage6 → TriTruth,
    (∀ s, f (next6 s) = rotateTri (f s)) ↔
      ∃ k : Fin 3, f = fun s => rotateTri^[(k : Nat)] (stage6Tone s)
  /-- Layer 2: the Monster prime base and its mask fibre. -/
  base : SSP ≃ Fin 15
  basePrime : ∀ p : SSP, Nat.Prime (AgdaMirror.MonsterOntos.toNat p)
  maskCarrier : MaskSSP ≃ AgdaMirror.MonsterProjection15.Mask15
  geometry : Ultrametric MaskSSP
  geometrySeparates : ∀ x y, geometry.d x y = 0 ↔ x = y
  contraction : ∀ (target : MaskSSP) {x y : MaskSSP}, x ≠ y →
    geometry.d (projectSSP target x) (projectSSP target y) < geometry.d x y
  /-- The geometry remembers the ordering of the base: no non-trivial reindexing
  of the base is an isometry, so no dialectical cycle can act on the base itself
  compatibly with the geometry. -/
  baseRigidity : ∀ σ : SSP ≃ SSP,
    (∀ x y : MaskSSP, geometry.d (fun p => x (σ p)) (fun p => y (σ p)) = geometry.d x y) →
      σ = Equiv.refl SSP
  /-- Layer 3: hyperfabric sections and the dialectical action on them. -/
  sections3 : Fabric ≃ (SSP → ZMod 3)
  sectionsAdditive : ∀ x y, sections3 (fabricXor x y) = sections3 x + sections3 y
  act : Stage6 → Fabric → Fabric
  actEquivariant : ∀ s F, act (next6 s) F = fabricRot (act s F)
  supportObstruction : ¬ ∀ a b : Trit, support (tritXor a b) = (support a || support b)
  /-- Layer 2': the walk state geometry over the same mask carrier. -/
  walkClosenessComplement : ∀ {x y : List Bool}, x.length = 15 → x ≠ y →
    AgdaMirror.MonsterWalk.dMask x y + AgdaMirror.MonsterProjection15.dMask x y = 15
  walkNotUltrametric :
    ¬ (∀ x y z : AgdaMirror.MonsterWalk.Mask,
        AgdaMirror.MonsterWalk.dMask x z ≤
          max (AgdaMirror.MonsterWalk.dMask x y) (AgdaMirror.MonsterWalk.dMask y z))
  /-- Layer 2'': masks as arithmetic of the base, and the supplied moonshine
  numeral as one of its values.  This is a structural identity about a product
  of primes; it asserts nothing about Monster representations or modular forms. -/
  maskArithmetic : MaskSSP → Nat
  moonshineNumeralIsMaskProduct :
    maskArithmetic trivectorMask = AgdaMirror.Moonshine.repDim
  /-- Mask arithmetic *is* mask order: divisibility of mask products is the
  submask relation, because the base is fifteen distinct primes. -/
  arithmeticIsOrder : ∀ x y : MaskSSP,
    maskArithmetic x ∣ maskArithmetic y ↔ ∀ p, x p = true → y p = true
  /-- Consequently the walk driven by the arithmetic lens is non-expanding
  towards the collapse mask in the geometry above. -/
  arithmeticWalkNonExpanding : ∀ (cands : AgdaMirror.MonsterWalk.Candidates)
      (s : AgdaMirror.MonsterWalk.State),
    geometry.d (maskOfList (AgdaMirror.MonsterWalk.step arithLens cands s).mask) emptyMaskSSP ≤
      geometry.d (maskOfList s.mask) emptyMaskSSP
  /-- Layer 3': the hyperfabric is the depth-15 balanced-ternary codec kernel,
  with digit negation carried to kernel inversion — and the supplied ternary XOR
  carried only to an *affine* operation, which is the honest mismatch between the
  repository's two ternary operations. -/
  kernelIdentification : Fabric ≃ (Fin 15 → ZMod 3)
  kernelInversion : ∀ F, kernelIdentification (fabricInv F) = - kernelIdentification F
  kernelXorAffine : ∀ x y, kernelIdentification (fabricXor x y) =
    kernelIdentification x + kernelIdentification y + 1
  /-- Layer 2''': the repository's flat 15-slot record carriers are the same
  fibre over the prime base, so the 15-bit signature scanner lands in the mask
  geometry.  `Sig15` is a 15-bit record; no physical content is asserted. -/
  recordFibre : ∀ {A : Type}, AgdaMirror.GodelLattice.Vec15 A ≃ (SSP → A)
  signatureFibre : AgdaMirror.PhysicsSignature.Sig15 ≃ MaskSSP
  signatureScan : ∀ L s, signatureFibre (AgdaMirror.PhysicsSignature.scan L s) =
    fun p => L.Compat p s
  /-- Layer 2'''': the order/selection layer's threshold masks are Monster masks,
  its rank is the size of the mask's support, and the threshold family is a
  monotone chain towards the collapse mask. -/
  thresholdIsMask : ∀ (t : Nat) (v : AgdaMirror.Vec15Order.PrimeCarrier15),
    thresholdMask t v = fun p => decide (recordFibre v p ≤ t)
  rankIsSupportCount : ∀ (t : Nat) (v : AgdaMirror.Vec15Order.PrimeCarrier15),
    AgdaMirror.Vec15Order.rank15 t v =
      (Finset.univ.filter (fun p : SSP => thresholdMask t v p = true)).card
  thresholdChain : ∀ {t t' : Nat}, t ≤ t' → ∀ v : AgdaMirror.Vec15Order.PrimeCarrier15,
    geometry.d (thresholdMask t v) emptyMaskSSP ≤ geometry.d (thresholdMask t' v) emptyMaskSSP
  /-- Layer 2''''': the descriptive and inference layers on the same carrier.
  The non-zero count is the size of the support mask's support, support and rank
  partition the fifteen primes, and the decision surface is a mask detector: the
  baseline test fails to reject exactly on carriers that are Boolean masks over
  the base.  "Test" and "p-value" are the source material's naming; no
  statistical claim is made. -/
  supportCount : ∀ v : AgdaMirror.Vec15Order.PrimeCarrier15,
    AgdaMirror.Vec15Descriptive.countNonZero15 v =
      (Finset.univ.filter (fun p : SSP => Synthesis.InferenceFibre.supportMask v p = true)).card
  supportRankPartition : ∀ v : AgdaMirror.Vec15Order.PrimeCarrier15,
    AgdaMirror.Vec15Descriptive.countNonZero15 v + AgdaMirror.Vec15Order.rank15 0 v = 15
  decisionIsMaskDetector : ∀ v : AgdaMirror.Vec15Order.PrimeCarrier15,
    AgdaMirror.Vec15Inference.baselineDecision v =
        AgdaMirror.Vec15Inference.Decision.failToReject ↔
      v = Synthesis.InferenceFibre.maskCarrier (Synthesis.InferenceFibre.supportMask v)
  /-- Layer 2'''''': the physics-facing interface records, honestly delimited.
  The gauge "uniqueness claim" is satisfiable while picking a non-Standard-Model
  tag, and the spin bundle's cover field is a bare map, so neither record has
  the content its name suggests.  The one interface with transportable content is
  conformance: over the supplied one-point state carrier it is exactly distance
  zero between the scanned signatures in the mask geometry. -/
  gaugeContractPermitsNonSM : ∀ (St : Type) (s : St),
    ∃ C : AgdaMirror.GaugeGroupContract.UniquenessClaim St,
      C.E.pickGauge s = AgdaMirror.GaugeGroupContract.Gauge.Other
  spinInterfaceNoDoubleCover :
    ¬ ∀ A : AgdaMirror.SpinEmergence.SpinEmergenceAxioms.{0}, ∀ x : A.SO 3 1,
        ∃ a b : A.SpinGroup, a ≠ b ∧
          A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x
  conformanceIsMaskDistance : ∀ (L₁ L₂ : AgdaMirror.PhysicsSignature.Lens)
      {xs : List AgdaMirror.PhysicsSignature.State}, xs ≠ [] →
    (AgdaMirror.PhysicsConformance.ConformsOn (AgdaMirror.PhysicsSignature.scan L₁)
        (AgdaMirror.PhysicsSignature.scan L₂) xs ↔
      geometry.d (signatureFibre (AgdaMirror.PhysicsSignature.scan L₁
            AgdaMirror.PhysicsSignature.State.st))
        (signatureFibre (AgdaMirror.PhysicsSignature.scan L₂
            AgdaMirror.PhysicsSignature.State.st)) = 0)
  /-- The complementary positive fact: the spin interface *can* be instantiated so
  that its cover field really is two-to-one with exhaustive fibres, by the
  repository's finite quaternion cover.  The double-cover property is therefore a
  theorem about a chosen instance, never a consequence of the record.  The finite
  model is `Q8 → V4`; it is not `Spin(3,1) → SO⁺(3,1)`. -/
  spinInterfaceGenuineInstance :
    ∃ A : AgdaMirror.SpinEmergence.SpinEmergenceAxioms.{0}, ∀ x : A.SO 3 1,
      ∃ a b : A.SpinGroup, a ≠ b ∧
        A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x ∧
        ∀ c : A.SpinGroup, A.SpinIsDoubleCover c = x → c = a ∨ c = b
  /-- Layer 2'''''''': exponent vectors over the base.  The exponent order refines
  the mask order, and the supplied "observer" `+1` leaves residue `1` modulo every
  prime a mask keeps — a theorem about products of distinct primes, asserting
  nothing about the `j`-invariant. -/
  exponentCarrier : (Fin 15 → Nat) ≃ (SSP → Nat)
  supportDividesState : ∀ v : SSP → Nat,
    maskArithmetic (Synthesis.ExponentFibre.supportOf v) ∣
      Synthesis.ExponentFibre.exponentProduct v
  observerResidue : ∀ {m : MaskSSP} {p : SSP}, m p = true →
    (maskArithmetic m + 1) % AgdaMirror.MonsterOntos.toNat p = 1
  /-- Layer 2''''''''': the arithmetic half of the Monster-order obligation.  The
  order numeral recorded in the literature (provenance, not a theorem here) has
  exactly the fifteen base primes as prime factors, and its radical is the full
  mask product.  No group is constructed anywhere in this development. -/
  orderNumeralPrimeFactors :
    Synthesis.MonsterOrder.monsterOrderNumeral.primeFactors =
      Finset.univ.image AgdaMirror.MonsterOntos.toNat
  orderNumeralRadical :
    ∏ q ∈ Synthesis.MonsterOrder.monsterOrderNumeral.primeFactors, q =
      maskArithmetic fullMaskSSP

  /-- The cover content is not confined to finite models: the interface also
  admits an instance whose carriers are infinite topological spaces and whose
  cover field is a continuous, genuinely two-to-one map (the squaring map of the
  circle group).  This is a statement about the interface; the circle is not
  `Spin(3,1)` and squaring is not the Lorentz cover. -/
  spinInterfaceContinuousInstance :
    ∃ (A : AgdaMirror.SpinEmergence.SpinEmergenceAxioms.{0})
      (_ : TopologicalSpace A.SpinGroup) (_ : TopologicalSpace (A.SO 3 1)),
      Continuous A.SpinIsDoubleCover ∧ Infinite A.SpinGroup ∧ Infinite (A.SO 3 1) ∧
      ∀ x : A.SO 3 1, ∃ a b : A.SpinGroup, a ≠ b ∧
        A.SpinIsDoubleCover a = x ∧ A.SpinIsDoubleCover b = x ∧
        ∀ c : A.SpinGroup, A.SpinIsDoubleCover c = x → c = a ∨ c = b
  /-- Layer 1': relation classifiers and the seam of the fourfold tone.  One
  shared criterion governs both: a classifier factors through another exactly
  when the second separates at least as finely.  The Loom display bucket refines
  the coarse root strictly, and no function of the bucket determines the
  promotion state — the source material's Boolean honesty flag, proved.  On the
  dialectical side, every fourfold tone has a nonempty seam, the supplied
  `stageTone` attains the minimal seam of one stage, and the sixfold descent tone
  has no seam at all. -/
  classifierFactorisation : ∀ {A B C : Type} [Nonempty C] (f : A → C) (g : A → B),
    (∃ h : B → C, ∀ a, f a = h (g a)) ↔ ∀ a₁ a₂, g a₁ = g a₂ → f a₁ = f a₂
  bucketRefinesRoot : ∃ h : AgdaMirror.Loom.LoomBucket → AgdaMirror.Loom.LoomRelationRoot,
    ∀ t, AgdaMirror.Loom.relationRootFor t = h (AgdaMirror.Loom.bucketFor t)
  rootDoesNotDetermineBucket :
    ¬ ∃ h : AgdaMirror.Loom.LoomRelationRoot → AgdaMirror.Loom.LoomBucket,
      ∀ t, AgdaMirror.Loom.bucketFor t = h (AgdaMirror.Loom.relationRootFor t)
  promotionUnconstrained :
    ¬ ∃ h : AgdaMirror.Loom.LoomBucket → AgdaMirror.Loom.LoomPromotionState,
      ∀ R : AgdaMirror.Loom.LoomTypedRelation, R.promotionState = h R.bucket
  fourfoldSeamNonempty : ∀ f : Stage → TriTruth, (Synthesis.RelationSeam.seam f).Nonempty
  fourfoldSeamMinimal :
    (Synthesis.RelationSeam.seam AgdaMirror.LogicTlurey.stageTone).card = 1
  sixfoldSeamEmpty : Synthesis.RelationSeam.seam6 stage6Tone = ∅

/-- **The spine is inhabited**: every interface obligation is discharged by a
theorem of this repository. -/
def crossDomainSpine : CrossDomainSpine where
  toneEquiv := tritToneEquiv
  toneXor := tritToneEquiv_xor
  toneIsZMod3 := toneZMod
  halfIndex := halfTritEquivFin5
  halfCollapseLossy := halfTone_not_injective
  collapseFibreCount := card_collapse_fibre
  sixfoldTone := stage6Tone
  sixfoldEquivariant := stage6Tone_next
  fourfoldObstruction := no_equivariant_fourfold_tone
  sixfoldToneUnique := equivariant_sixfold_tone_iff
  base := sspEquivFin15
  basePrime := toNat_prime
  maskCarrier := maskFibreEquiv
  geometry := USSP
  geometrySeparates := dSSP_eq_zero_iff
  contraction := by
    intro target x y hxy
    exact projectSSP_contractive target hxy
  baseRigidity := isometric_reindex_eq_refl
  sections3 := fabricZMod
  sectionsAdditive := fabricZMod_add
  act := fabricAct
  actEquivariant := fabricAct_next6
  supportObstruction := support_not_hom
  walkClosenessComplement := fun hx hne => walk_distance_complement hx hne
  walkNotUltrametric := AgdaMirror.MonsterWalk.dMask_ultratriangle_false
  maskArithmetic := maskProduct
  moonshineNumeralIsMaskProduct := maskProduct_trivector
  arithmeticIsOrder := maskProduct_dvd_iff
  arithmeticWalkNonExpanding := step_arith_dSSP_empty_le
  kernelIdentification := fabricKernelEquiv
  kernelInversion := fabricKernelEquiv_neg
  kernelXorAffine := fabricKernelEquiv_xor_affine
  recordFibre := vec15Equiv
  signatureFibre := sig15Equiv
  signatureScan := sig15Equiv_scan
  thresholdIsMask := selectMask15_fibre
  rankIsSupportCount := rank15_eq_card
  thresholdChain := selectMask15_dSSP_empty_mono
  supportCount := Synthesis.InferenceFibre.countNonZero15_eq_card
  supportRankPartition := Synthesis.InferenceFibre.countNonZero15_add_rank15_zero
  decisionIsMaskDetector := Synthesis.InferenceFibre.baselineDecision_failToReject_iff
  gaugeContractPermitsNonSM := Synthesis.PhysicsInterfaces.gauge_contract_permits_non_SM
  spinInterfaceNoDoubleCover := Synthesis.PhysicsInterfaces.spin_interface_no_double_cover
  conformanceIsMaskDistance := fun L₁ L₂ {_xs} hxs =>
    Synthesis.PhysicsInterfaces.conformsOn_scan_iff_dSSP_zero L₁ L₂ hxs
  spinInterfaceGenuineInstance :=
    Synthesis.SpinCoverBridge.spin_interface_satisfiable_with_genuine_cover
  exponentCarrier := Synthesis.ExponentFibre.fractranStateEquiv
  supportDividesState := Synthesis.ExponentFibre.maskProduct_support_dvd_exponentProduct
  observerResidue := Synthesis.ExponentFibre.maskProduct_succ_mod
  orderNumeralPrimeFactors := Synthesis.MonsterOrder.monsterOrderNumeral_primeFactors
  orderNumeralRadical := Synthesis.MonsterOrder.radical_monsterOrderNumeral
  spinInterfaceContinuousInstance :=
    Synthesis.CircleCover.spin_interface_satisfiable_with_continuous_cover
  classifierFactorisation := fun f g => Synthesis.RelationSeam.factors_through_iff f g
  bucketRefinesRoot := Synthesis.RelationSeam.root_factors_through_bucket
  rootDoesNotDetermineBucket := Synthesis.RelationSeam.bucket_not_factor_through_root
  promotionUnconstrained := Synthesis.RelationSeam.promotion_not_determined_by_bucket
  fourfoldSeamNonempty := Synthesis.RelationSeam.seam_nonempty
  fourfoldSeamMinimal := Synthesis.RelationSeam.stageTone_seam_minimal.1
  sixfoldSeamEmpty := Synthesis.RelationSeam.stage6Tone_seam_empty

/-! ## The composite theorem -/

/-- The digit rotation is the tone rotation (layer 0 bridge, pointwise form). -/
theorem toTriTruth_rot (t : Trit) : toTriTruth (rotTrit t) = rotateTri (toTriTruth t) :=
  AgdaMirror.TritBridge.rotTrit_equivariant_to t

/-- **Iterated dialectic drives iterated tone rotation.**  After `n` dialectical
successor steps, every fibre of the hyperfabric has rotated exactly `n` times. -/
theorem fabricTone_act_iterate (n : Nat) (s : Stage6) (F : Fabric) :
    fabricTone (fabricAct (next6^[n] s) F) =
      fun p => (rotateTri^[n]) (fabricTone (fabricAct s F) p) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    funext p
    have h := congrFun (ih (next6 s)) p
    rw [Function.iterate_succ_apply, h, fabricAct_next6, Function.iterate_succ_apply]
    simp [fabricTone, fabricRot, toTriTruth_rot]

/-- **End-to-end synthesis.**  For every half-trit hyperfabric `H` over the
Monster prime base, every dialectical stage `s`, every step count `n`, and every
projection target, the four layers compose as follows.

1. *(dialectic ⇒ tone)* `n` dialectical successor steps rotate the tone of every
   fibre exactly `n` times;
2. *(period)* three steps already return the whole fabric, so the sixfold cycle
   covers the ternary tone twice;
3. *(algebra)* the section space is `(ℤ/3)^15` with pointwise ternary XOR as
   addition;
4. *(geometry)* the support mask of the fabric lies in the Monster mask fibre,
   where the constant projection strictly contracts the supplied ultrametric
   between distinct masks;
5. *(honest loss)* the half-trit refinement is not recoverable from the fabric,
   and no four-position dialectic admits a rotation-equivariant tone at all;
6. *(statistics ⇒ arithmetic)* for any 15-lane carrier `v` over the same base:
   its support and its rank at threshold `0` partition the fifteen primes; the
   inference layer's baseline test fails to reject exactly when `v` is the
   indicator of its own support; the support mask's product divides the number
   `v` denotes as an exponent vector; and that product plus one leaves residue
   `1` modulo every prime in the support. -/
theorem spine_end_to_end (H : HalfFabric) (s : Stage6) (n : Nat) (target : MaskSSP)
    (v : AgdaMirror.Vec15Order.PrimeCarrier15) :
    (fabricTone (fabricAct (next6^[n] s) (collapse H)) =
        fun p => (rotateTri^[n]) (fabricTone (fabricAct s (collapse H)) p)) ∧
    fabricAct (next6 (next6 (next6 s))) (collapse H) = fabricAct s (collapse H) ∧
    (∀ x y : Fabric, fabricZMod (fabricXor x y) = fabricZMod x + fabricZMod y) ∧
    (∀ G : Fabric, supportMask G ≠ supportMask (collapse H) →
        dSSP (projectSSP target (supportMask G)) (projectSSP target (supportMask (collapse H)))
          < dSSP (supportMask G) (supportMask (collapse H))) ∧
    ¬ Function.Injective collapse ∧
    ¬ (∃ f : Stage → TriTruth, ∀ t, f (next t) = rotateTri (f t)) ∧
    AgdaMirror.Vec15Descriptive.countNonZero15 v + AgdaMirror.Vec15Order.rank15 0 v = 15 ∧
    (AgdaMirror.Vec15Inference.baselineDecision v =
        AgdaMirror.Vec15Inference.Decision.failToReject ↔
      v = Synthesis.InferenceFibre.maskCarrier (Synthesis.InferenceFibre.supportMask v)) ∧
    maskProduct (Synthesis.InferenceFibre.supportMask v) ∣
      Synthesis.ExponentFibre.exponentProduct (vec15Equiv v) ∧
    (∀ p : SSP, Synthesis.InferenceFibre.supportMask v p = true →
      (maskProduct (Synthesis.InferenceFibre.supportMask v) + 1) %
        AgdaMirror.MonsterOntos.toNat p = 1) := by
  refine ⟨fabricTone_act_iterate n s (collapse H), fabricAct_period_three s (collapse H),
    fabricZMod_add, ?_, collapse_not_injective, no_equivariant_fourfold_tone,
    Synthesis.InferenceFibre.countNonZero15_add_rank15_zero v,
    Synthesis.InferenceFibre.baselineDecision_failToReject_iff v,
    Synthesis.ExponentFibre.maskProduct_support_dvd_exponentProduct (vec15Equiv v),
    fun _ hp => Synthesis.ExponentFibre.maskProduct_succ_mod hp⟩
  intro G hG
  exact projectSSP_contractive target hG

end Synthesis.EndToEnd
