import Integration.MonsterFifteen
import Integration.Base369Group
import Integration.ClopenBalls
import Integration.Refinement
import Integration.ReceiptSocket
import Integration.UltrametricCensus
import Integration.CognitionSupervoxel
import Integration.PhaseQuotient
import Integration.SSPWeave
import Integration.ObserverQuotient
import Integration.PolarResidual
import Integration.SymmetryReduction
import Integration.StructuredObserver
import Integration.ObserverTower
import Integration.PhysicsInstances
import Integration.GaugeSU2
import Integration.GaugeSSP
import Integration.DescentLevel

/-!
# The global TOE registry

This is the machine-checked half of the global map.  Every positive row is an
`Integration.Levels.Entry`, whose `Evidence` constructor *is* the four-level
classification: a row cannot be filed at level 3 without an `Equiv` and cannot be
filed at level 4 without a `Transport` or a preservation proof.  Every negative
row is a `Boundary`, which stores the refuted proposition together with its
refutation, so an absence cannot be asserted without a proof either.  Every
`Socket` records a place where the corpus supplies a record or `Bool` field that
constrains nothing, again with a proof.

The prose companion is `TOE_GLOBAL_MAP.md`, which adds the Agda import
statistics and the provenance of each Lean mirror.  The two are meant to be read
together: the file you are reading is what is actually checked.

Scope note: nothing in this registry mentions Yang–Mills or Navier–Stokes
material, and no row asserts a physical, empirical, Monster-group, moonshine,
vertex-algebra or Riemann-hypothesis statement.  The rows are statements about
finite types, finite groups and finite ultrametric spaces.
-/

namespace Integration.Registry

open Integration.Levels
open Integration.TernaryHub
open Integration.Address
open Integration.Base369Group
open Integration.ClopenBalls
open Integration.MonsterFifteen
open Synthesis.MonsterFibre (dSSP)
open Integration.UltrametricCensus
open Integration.CognitionSupervoxel
open Integration.PhaseQuotient
open Integration.SSPWeave
open Integration.ObserverQuotient
open Integration.PolarResidual
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.ObserverTower
open Integration.Physics369
open Integration.GaugeSU2
open Integration.GaugeSSP
open Integration.DescentLevel
open AgdaMirror.Base369 (TriTruth HexTruth NonaryTruth rotateHex rotateNonary hexXor triXor)
open AgdaMirror.DASHIAlgebra (Trit)

/-! ## Extra transports needed for the rows -/

/-- The loom's `projection2x3` as a level-4 transport: the hexadic beat splits as
parity × tone, compatibly with the beat rotation. -/
def hexSplitTransport :
    Transport HexTruth (ZMod 2 × ZMod 3) rotateHex (fun p => (p.1 + 1, p.2 + 1)) :=
  ⟨hexSplit, by decide⟩

/-- The nonary layer as a level-4 transport onto `ZMod 9` with `+1`. -/
def nonaryRotateTransport :
    Transport NonaryTruth (ZMod 9) rotateNonary (fun z => z + 1) :=
  ⟨nonEquiv, nonIdx_rotate⟩

/-- The codec-kernel/369-address bijection as a level-4 transport for the
pointwise polarity involution. -/
def kernelPolarityTransport (d : ℕ) :
    Transport (Kernel d) (Address369 d)
      (fun u i => Trit.inv (u i)) (fun a i => invert369 (a i)) :=
  ⟨kernelEquiv369 d, fun u => kernelIsometry_inv u⟩

/-! ## The positive rows -/

/-- The registry of cross-domain claims that this pass has established. -/
def registry : List Entry :=
  [ { source := "DASHI.Algebra.Trit"
      target := "ZMod 3 (balanced coordinate)"
      evidence := .provedTransport ternaryHub.trit
      note := "Polarity `Trit.inv` becomes negation; the coordinate is unique up \
               to sign (`bal_unique_up_to_sign`)." }
  , { source := "Base369.TriTruth (tone)"
      target := "ZMod 3"
      evidence := .provedTransport ternaryHub.tone
      note := "`triReflect` becomes negation.  Boundary: `triXor` is the affine \
               operation x+y+1 in this coordinate, not addition." }
  , { source := "DASHI.Geometry.SSP369Ultrametric.Digit369"
      target := "ZMod 3"
      evidence := .provedTransport ternaryHub.digit
      note := "`invert369` becomes negation; agrees with the supplied `trit→369`." }
  , { source := "DASHI.Foundations.SSPTritCarrier.SSPTrit"
      target := "ZMod 3"
      evidence := .provedTransport ternaryHub.ssp
      note := "The trit carrier of the foundations layer is the same digit." }
  , { source := "DASHI.Codec.TriadicMaskSign.TritCode"
      target := "ZMod 3"
      evidence := .provedTransport ternaryHub.code
      note := "Sign/active-sign codec words are the same digit; `invertCode` is \
               negation." }
  , { source := "ConstraintClopenRefinement.BTBranch"
      target := "ZMod 3"
      evidence := .sharedType ternaryHub.branch
      note := "Level 3 only: the source equips `BTBranch` with no involution, so \
               there is no operation to preserve." }
  , { source := "Base369 hexadic beat (HexTruth)"
      target := "ZMod 2 × ZMod 3"
      evidence := .provedTransport hexSplitTransport
      note := "The loom's declared `projection2x3`, realised: parity × tone, \
               additive for `hexXor` (`hexSplit_xor`)." }
  , { source := "Base369 nonary layer (NonaryTruth)"
      target := "ZMod 9"
      evidence := .provedTransport nonaryRotateTransport
      note := "Cyclic of order 9.  Boundary row below: it is *not* two ternary \
               layers." }
  , { source := "DASHI.Codec kernels (Kernel d)"
      target := "SSP369Ultrametric addresses (Address369 d)"
      evidence := .provedTransport (kernelPolarityTransport 15)
      note := "Polarity-equivariant, which is the one fact the Agda proves." }
  , { source := "DASHI.Codec kernels (Kernel 15)"
      target := "Address369 15, prefix distance"
      evidence := .provedPreservation (kernelTo369 (d := 15)) Addr.dist Addr.dist
        (fun u v => kernelIsometry u v)
      note := "Isometry: the codec lane and the 3/6/9 geometry lane are one \
               metric object.  The Agda proves only the reflexive case." }
  , { source := "Monster 15-prime mask fibre (MaskSSP, supplied ultrametric)"
      target := "depth-15 boolean prefix addresses"
      evidence := .provedPreservation maskAddr dSSP Addr.dist
        (fun x y => (dSSP_eq_dist x y).symm)
      note := "The two ultrametrics of the corpus — list longest-common-prefix \
               and indexed agreement depth — are the same construction." }
  , { source := "Hyperfabric sections (SSP → Trit)"
      target := "Address369 15"
      evidence := .sharedType fabricAddr369Equiv
      note := "Shared carrier.  The geometry transports (`fabric369_isometry`); \
               the descent to the mask layer is only an inequality, see the \
               boundary rows." }
  , { source := "Loom relation taxonomy (LoomBucket)"
      target := "Loom relation roots"
      evidence := .recordDependency Cuisine.LoomBridge.rootOfBucket
      note := "Level 2: a stored classification.  It does not invert \
               (`root_does_not_determine_bucket`) and the taxonomy is not a \
               product over its roots (`loom_root_not_product`), so it cannot be \
               promoted to level 3." }
  , { source := "MonsterOntos `SSP`"
      target := "the Monster sporadic simple group"
      evidence := .vocabulary "Monster"
      note := "Level 1 and no higher.  `SSP` is a 15-element enumeration of the \
               supersingular primes; no group, no vertex algebra and no \
               moonshine statement occurs anywhere in the Lean corpus." }
  , { source := "MonsterUltrametric15 `UMask15` (supplied record)"
      target := "depth-15 prefix geometry"
      evidence := .provedPreservation mask15Addr AgdaMirror.MonsterProjection15.d15
        Addr.dist (fun m m' => (d15_eq_prefix m m').symm)
      note := "The supplied length-15 mask ultrametric, on its own carrier." }
  , { source := "Cuisine safety fields (culture domain instance)"
      target := "depth-15 prefix geometry"
      evidence := .provedPreservation
        (fun x : Cuisine.SafetyFabric.SafetyField =>
          maskAddr (Cuisine.SafetyFabric.doubtMask x))
        Cuisine.SafetyFabric.dSafety Addr.dist
        (fun x y => (dSafety_eq_prefix x y).symm)
      note := "A domain instance: the culture layer's own ultrametric is the \
               prefix geometry pulled back along `doubtMask`.  It is a \
               pseudometric on safety fields (`dSafety_not_separating`)." }
  , { source := "Cognition `Phase3` (PhaseEnrichedTrit)"
      target := "ZMod 3 with rotation"
      evidence := .provedTransport phase3Transport
      note := "The cognition layer's cyclic phase is the hub's ternary carrier, \
               rotation to `+1`." }
  , { source := "Cognition observable `observeTrit`"
      target := "the hub's balanced digit with polarity"
      evidence := .provedEquivariance observeTrit flipPolarity Trit.inv observeTrit_flip
      note := "Level iv as a preservation theorem only: the map is surjective \
               but not injective (`observeTrit_not_injective`), so the zero \
               fibre is not a singleton and this is not an equivalence." }
  , { source := "Cognition psychological hidden state"
      target := "the hub's balanced digit"
      evidence := .recordDependency (balancedProjection (R := Unit))
      note := "Level ii: the cognition state record stores a phase-enriched \
               trit whose observable is the corpus's digit.  The layer also \
               instantiates the same `ConstraintSystem` interface as the \
               supervoxel, loom and publication lanes (`psychSystem`)." }
  , { source := "\"supervoxel\" / \"clopen\" in the cognition and culture layers"
      target := "the prefix-ball topology"
      evidence := .sharedType (Equiv.refl (PrefixBall 3 Digit369))
      note := "Level 3: the corpus's supervoxel talk denotes exactly the \
               prefix balls of `Integration.ClopenBalls`, which are proved open \
               and closed.  The corpus's own `authority` record is a socket." }
  , { source := "Ternary endomorphism codes (T³) modulo the output C₃"
      target := "the nine-state phase quotient `PhaseQuotient9 = T × T`"
      evidence := .provedEquivariance (fun c => (phaseEncode c).2) rotateOutputCode id
        phaseEncode_rotate_snd
      note := "Level iv: the quotient coordinate is invariant under the free \
               C₃ output phase and separates its orbits \
               (`quotient_eq_iff_orbit`), so the nine-state carrier is the \
               orbit space 27/C₃, not a coincidence of cardinality." }
  , { source := "`PhaseQuotient9`"
      target := "the `Base369` nonary labels (`NonaryTruth`)"
      evidence := .sharedType nonaryChart
      note := "Level iii: the two-sided row-major chart of the Agda separation \
               module.  Carrier only — the algebras differ, see the boundary \
               row below." }
  , { source := "the nonary labels with the transported phase-quotient law"
      target := "ℤ/3 × ℤ/3"
      evidence := .provedPreservation phaseZModEquiv
        (fun x y => phaseZModEquiv (nonaryPhaseAdd x y)) (fun u v => u + v)
        (fun x y => (phaseZModEquiv_add x y).symm)
      note := "Level iv, and the positive counterpart of the nonary boundary: \
               transporting the phase quotient's componentwise addition along \
               the chart gives a second, exponent-three algebra on the same \
               nine labels.  The corpus has the ingredients but never packages \
               the operation." }
  , { source := "SSP fibre orientations (`inverse`/`mediated`/`forward`)"
      target := "ℤ/2"
      evidence := .provedPreservation orientationSign
        (fun q p => orientationSign (composeOrientation q p)) (fun u v => u + v)
        (fun q p => (orientationSign_hom q p).symm)
      note := "Level iv: the orientation monoid's universal group quotient.  \
               The monoid itself is not a group (`not_a_group`)." }
  , { source := "SSP path composition"
      target := "composition of lane-state transports"
      evidence := .provedPreservation laneAction
        (fun q p => laneAction (composeOrientation q p))
        (fun f g => f ∘ g)
        (fun q p => by funext x; exact (laneAction_comp q p x).symm)
      note := "Level iv, and the algebra-preservation statement the SSP layer \
               actually supports: transport is functorial, T_{q∘p} = T_q ∘ T_p \
               (`transportSSP_comp`), indexed by the fifteen lanes." }
  , { source := "SSP lane states"
      target := "the ternary hub with its polarity"
      evidence := .provedTransport laneStateHub
      note := "Level iv: the lane-state carrier is the hub, and the `inverse` \
               orientation acts as exactly the hub's polarity involution." }
  , { source := "signed multiplicity defect orientation"
      target := "the ternary hub with its polarity"
      evidence := .provedTransport defectOrientationHub
      note := "Level iv: the sign of the integer defect δ(A,B) is the hub \
               digit, and swapping the two objects is the hub polarity \
               (`orientation_swap`)." }
  , { source := "signed multiplicity defect orientation"
      target := "the SSP `FibreOrientation` carrier"
      evidence := .provedEquivariance defectToFibreOrientation reverseOrientation fibreFlip
        defectToFibreOrientation_equiv
      note := "Level iv: the Agda's `toSSPFibreOrientation` bridge, upgraded to \
               a bijection that carries defect reversal to the forward/inverse \
               exchange.  So the relational signed layer and the SSP transport \
               layer share carrier and involution." }
  , { source := "the polarity-invariant Boolean observer"
      target := "the trivial action on masks"
      evidence := .provedEquivariance polarPresence Trit.inv id
        (fun t => by simpa [tritAction_inverse] using polarPresence_equivariant .inverse t)
      note := "Level iv: the symmetry action *does* descend to the Boolean \
               layer, uniquely (`laneAction_descends`), and the observer is \
               exactly the orbit map of the polarity involution \
               (`polarPresence_orbit`).  What fails at the Boolean layer is the \
               binary law, not the group action." }
  , { source := "the residual-bearing 9 → 6 polar projection"
      target := "polar cells ⊕ retained zero-branch phase"
      evidence := .provedTransport polarTransport
      note := "Level iv: the projection is a bijection 9 ≃ 6 + 3 whose inverse \
               is the source's `reopen`, and it is polarity-equivariant.  A \
               direct 9 → 6 retraction is impossible \
               (`no_retraction_to_polar`)." }
  , { source := "the closure lane's `KernelTrit`"
      target := "the ternary hub with its polarity"
      evidence := .provedTransport kernelTritHub
      note := "Level iv: a seventh independently declared ternary carrier, with \
               `negateTrit` the hub polarity." }
  , { source := "the free C₃ output-phase action on ternary endomorphism codes"
      target := "the nine-state orbit carrier"
      evidence := .provedEquivariance (fun c : LevelTwoCode => (phaseEquiv c).2)
        (rotateByPhase .p1) id (fun c => phaseQuotient_invariant .p1 c)
      note := "Level iv: the 27 → 9 symmetry reduction of \
               `TernaryEndomorphismPhaseQuotientExact.agda`, packaged as an \
               `EquivariantQuotient` (`phaseReduction`): the free C₃ action \
               descends, with trivial induced action, so the nine-state carrier \
               is the orbit space (`quotient_eq_iff_orbit`).  This reduction is \
               independent of which algebra the nine labels are given."   }
  , { source := "the SSP orientation action on a pair of lane states"
      target := "its action on a single lane state"
      evidence := .provedEquivariance (Prod.fst : Trit × Trit → Trit)
        (fun p => (tritAction .inverse p.1, tritAction .inverse p.2))
        (tritAction .inverse) (fun _ => rfl)
      note := "Level iv: an `EquivariantQuotient` with *nontrivial* induced \
               action (`laneReduction`, `laneReduction_action_nontrivial`), so \
               the symmetry-reduction structure is not inhabited only by orbit \
               maps." }
  , { source := "the SSP 369 nine-cell carrier with its orientation action"
      target := "visible lane polarity + retained depth-wheel phase"
      evidence := .provedEquivariance (Prod.fst : PolarResidual.FullPhaseCell → KernelTrit)
        (StructuredObserver.actFull .inverse) (StructuredObserver.actKernel .inverse)
        (fun c => StructuredObserver.kernelReduction.square .inverse c)
      note := "Level iv, and the first inhabitant of the welded record \
               `SymmetryResolvedObserver` (`ssp369Observer`): an equivariant \
               quotient with nontrivial induced action, an exactly reopenable \
               residual, and a strictly positive transverse Gram certificate \
               that is invariant under the action (`ssp369_theorem`)." }
  , { source := "the order-three depth-wheel rotation of the SSP 369 nine-cell carrier"
      target := "the invariant lane polarity, with the wheel phase as residual"
      evidence := .provedEquivariance (Prod.fst : PolarResidual.FullPhaseCell → KernelTrit)
        (StructuredObserver.actWheel Phase3.p1) id
        (fun c => StructuredObserver.wheelReduction.square Phase3.p1 c)
      note := "Level iv: the only registry row whose acting group is genuinely \
               of order three rather than an effective ℤ/2.  The rotation is \
               free (`actWheel_order_three`), the reduction is an orbit map, \
               and the retained phase reopens the cell exactly \
               (`wheelObserver`, `wheel_theorem`).  `phaseEmbed_rot` further \
               identifies the corpus depth wheel with the spine's regular \
               representation ℝ[C₃], so the spine's irreducible transverse \
               plane theorems apply verbatim (`wheel_no_invariant_line`)." }
  , { source := "the SSP kernel trit with its orientation action"
      target := "the polarity-invariant magnitude observer, with the sign as residual"
      evidence := .provedEquivariance ObserverTower.kernelMagnitude
        (StructuredObserver.actKernel .inverse) id
        (fun t => ObserverTower.magnitudeStep.square .inverse t)
      note := "Level iv: the second stage of the only *two-stage* tower in the \
               registry.  Composed with the SSP 369 row it gives \
               `9 → 3 → 2` with retained residual `sign × phase` of size six \
               (`sspTower`, `sspTower_theorem`).  The generic composition \
               theorem `towerOf` shows the welded record is closed under such \
               extensions, and `tower_nondegeneracy` shows the transverse \
               certificate is unchanged by the extra level." }
  , { source := "the SU(2) axis-lift double cover (finite chart layer)"
      target := "the base axis triple, with the lift polarity as residual"
      evidence := .provedEquivariance (Prod.fst : Physics369.AxisLift → Physics369.SU2Axis)
        (Physics369.liftAction .inverse) id
        (fun x => Physics369.axisReduction.square .inverse x)
      note := "Level iv: `3 × 2 = 6`, the central flip is free, the base is the \
               orbit space, and the cover is a `SymmetryResolvedObserver` \
               (`axisLiftObserver`, `axisLift_theorem`).  Only the finite chart \
               layer of the source module is used; no analytic or gauge-field \
               content is imported or claimed." }
  , { source := "the NS Stage-3 nine-state receipt coordinate (finite chart layer)"
      target := "signed analytic disposition + retained proof-maturity residual"
      evidence := .provedEquivariance (Prod.fst : Physics369.Stage3Nonary → Trit)
        (Physics369.dispositionAction .inverse) (Physics369.dispositionCoarse .inverse)
        (fun x => Physics369.stage3Reduction.square .inverse x)
      note := "Level iv: the ledger's `disposition × maturity ≃ 9` chart, with \
               the polarity involution as induced action, as a \
               `SymmetryResolvedObserver` (`nsStage3Observer`, \
               `nsStage3_theorem`).  This is a statement about a finite receipt \
               coordinate; nothing analytic is imported and no claim about the \
               Navier–Stokes equations is made." }
  , { source := "the axis-lift lane under the enlarged symmetry `C₂ × C₃`"
      target := "the axis triple, with the *surviving* `C₃` acting on it"
      evidence := .provedEquivariance (Prod.fst : Physics369.AxisLift → Physics369.SU2Axis)
        (GaugeSU2.actCover (GaugeSU2.Sheet.keep, PhaseQuotient.Phase3.p1))
        (GaugeSU2.rotAxis PhaseQuotient.Phase3.p1)
        (fun x => GaugeSU2.su2GaugeReduction.square (GaugeSU2.Sheet.keep, .p1) x)
      note := "Level iv, and the only registry row that is a *gauge* reduction \
               rather than an orbit quotient: the deck subgroup `C₂` is \
               quotiented away and is provably invisible downstairs, while the \
               rotation symmetry survives and moves the reduced carrier \
               (`su2_effective`, `su2_not_orbit_quotient`).  The invisible \
               symmetries are exactly the gauge subgroup \
               (`su2_redundant_iff_gauge`), and the lane still carries the \
               positive transverse certificate (`su2_gauge_theorem`).  This is \
               the finite shadow of the `SU(2)/{±1}` pattern only; no claim \
               that these carriers are Lie groups is made." }
  , { source := "the SSP nine-cell lane under the enlarged symmetry `C₃ × C₂`"
      target := "the visible lane polarity, with the *surviving* `C₂` acting on it"
      evidence := .provedEquivariance (Prod.fst : PolarResidual.FullPhaseCell → KernelTrit)
        (GaugeSSP.actCell (1, GaugeSU2.Sheet.flip)) (GaugeSSP.sheetOnTrit GaugeSU2.Sheet.flip)
        (fun c => GaugeSSP.sspGaugeReduction.square (1, GaugeSU2.Sheet.flip) c)
      note := "Level iv: the same projection `9 → 3` as the depth-wheel row, \
               but with the wheel demoted to the gauge subgroup of a larger \
               lane symmetry, so the induced action is now nontrivial \
               (`wheel_vs_gauge`).  The invisible symmetries are exactly the \
               wheel rotations (`ssp_redundant_iff_gauge`), the wheel phase is \
               the retained residual, and the transverse certificate is \
               positive and invariant (`ssp_gauge_theorem`)." }
  ]

/-- The level of every row, in order.  This is `rfl`: the classification is read
off the evidence constructors, not asserted separately. -/
theorem registry_levels :
    registry.map Entry.level =
      [.provedTransport, .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .sharedType, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport, .sharedType,
       .recordDependency, .vocabulary, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .recordDependency,
       .sharedType,
       .provedTransport, .sharedType, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport,
       .provedTransport] := rfl

/-! ## The negative rows -/

/-- Refuted cross-domain claims, each carrying its refutation. -/
def boundaries : List Boundary :=
  [ { source := "the two-state coarsening of the axis lane"
      target := "the lane's transverse nondegeneracy certificate"
      statement := "The certificate of `Integration.DescentLevel.highObserver` \
                    is an observable of the three-axis layer but not of the \
                    coarser two-state observation that merges the \
                    distinguished axis with another: it takes the values \
                    `107/9` and `104/9` on two states with the same merged \
                    label, so the coarsest sufficient observation for this \
                    invariant is exactly the axis layer \
                    (`axis_coarsest_sufficient`)."
      claim := DescentLevel.axisTower.FactorsAt DescentLevel.highObserver.nondegeneracy 2
      refutation := DescentLevel.cert_not_factorsAt_two }
  , { source := "Base369 nonary layer, with its *cyclic* law"
      target := "two independent ternary layers"
      statement := "No bijection carries `nonaryXor` to componentwise `triXor`: \
                    the nine-label address carrier does not determine the \
                    algebra.  This is a statement about the two operations, not \
                    about the carriers — the carrier bijection exists \
                    (`Integration.PhaseQuotient.nonaryChart`), and the same \
                    labels do carry an exponent-three law once the phase \
                    quotient's addition is transported along it \
                    (`nonaryPhaseAdd`, `phaseZModEquiv_add`)."
      claim := ∃ e : NonaryTruth ≃ (TriTruth × TriTruth),
        ∀ x y : NonaryTruth, e (AgdaMirror.Base369.nonaryXor x y) =
          (triXor (e x).1 (e y).1, triXor (e x).2 (e y).2)
      refutation := nonary_not_ternary_square }
  , { source := "Base369 tone XOR, read in the *balanced* chart"
      target := "the ZMod 3 group law of that chart"
      statement := "`triXor` is additive in its native index chart \
                    (`triIdx_xor`), whose origin is `tri-low`, and affine \
                    (`x + y + 1`) in the polarity-compatible balanced chart, \
                    whose origin is the polarity-fixed `tri-mid`.  The two \
                    charts differ by a translation, and the native one is not \
                    polarity-compatible \
                    (`Integration.PhaseQuotient.triXor_chart_dichotomy`).  The \
                    refuted claim is additivity *in the balanced chart*."
      claim := ∀ a b : TriTruth, balTone (triXor a b) = balTone a + balTone b
      refutation := by
        intro h
        obtain ⟨a, b, hab⟩ := balTone_triXor_ne_add
        exact hab (h a b) }
  , { source := "Loom relation taxonomy"
      target := "a bundle over its roots"
      statement := "Root classes have sizes 3, 2, 3, 1, so there is no fibre."
      claim := ∃ (F : Type) (e : AgdaMirror.Loom.LoomRelationType ≃
          AgdaMirror.Loom.LoomRelationRoot × F),
        ∀ t, (e t).1 = AgdaMirror.Loom.relationRootFor t
      refutation := Integration.Refinement.loom_root_not_product }
  , { source := "hyperfabric support map (observer-level)"
      target := "the Monster mask geometry"
      statement := "Support is non-expansive but not an isometry: the Boolean \
                    observer coarsens the ternary geometry.  This bounds the \
                    observer, not the SSP layer, whose own transport is \
                    functorial (`Integration.SSPWeave.transportSSP_comp`)."
      claim := ∀ F G : Synthesis.Hyperfabric.Fabric,
        dSSP (Synthesis.Hyperfabric.supportMask F)
          (Synthesis.Hyperfabric.supportMask G) = fabricDist F G
      refutation := support_not_isometry }
  , { source := "hyperfabric support map (observer-level)"
      target := "the Monster mask carrier"
      statement := "Support is not injective, so the fabric is not recoverable \
                    from the mask.  The information lost is the sign: the \
                    polarity-invariant observer is exactly the orbit map of the \
                    polarity involution \
                    (`Integration.ObserverQuotient.polarPresence_orbit`), and \
                    no section of it is equivariant (`no_equivariant_section`)."
      claim := Function.Injective Synthesis.Hyperfabric.supportMask
      refutation := support_not_injective }
  , { source := "hyperfabric ternary XOR (observer-level)"
      target := "any binary Boolean operation on the mask layer"
      statement := "No binary Boolean operation whatsoever makes the support \
                    observer a homomorphism for the ternary XOR — strictly \
                    stronger than the corpus's refutation of boolean OR, and \
                    equally true of the polarity-invariant observer \
                    (`polarPresence_no_descent`).  This is an observer-loss \
                    boundary: the *symmetry action* does descend along the \
                    polarity-invariant observer (`polarPresence_equivariant`), \
                    only the binary law does not."
      claim := ∃ f : Bool → Bool → Bool, ∀ a b : Trit,
        Synthesis.Hyperfabric.support (AgdaMirror.TritBridge.tritXor a b) =
          f (Synthesis.Hyperfabric.support a) (Synthesis.Hyperfabric.support b)
      refutation := support_no_descent }
  , { source := "hyperfabric support map"
      target := "a polarity-invariant observer"
      statement := "The corpus's support map is the indicator of ‘not the \
                    `tritXor` identity’, i.e. it is aligned with the native \
                    chart's origin, so it is not invariant under the polarity \
                    involution.  The polarity-invariant Boolean observer is the \
                    magnitude test instead."
      claim := ∀ t : Trit, Synthesis.Hyperfabric.support (Trit.inv t) =
        Synthesis.Hyperfabric.support t
      refutation := support_not_polarity_invariant }
  , { source := "the SSP orientation monoid"
      target := "a group"
      statement := "`forward` is a non-unit idempotent, so the three-element \
                    orientation monoid is not a group; its universal group \
                    quotient is ℤ/2, through which the lane action factors."
      claim := ∀ g : FibreOrientation, ∃ h, composeOrientation g h = .mediated
      refutation := not_a_group }
  , { source := "the residual-bearing 9 → 6 polar projection"
      target := "a direct 9 → 6 retraction"
      statement := "No injection of the nine full phase cells into the six \
                    polar cells exists, so the retained zero-branch residual is \
                    not removable bookkeeping."
      claim := ∃ f : PolarResidual.FullPhaseCell → PolarResidual.PolarPhaseCell,
        Function.Injective f
      refutation := no_retraction_to_polar }
  , { source := "Monster walk distance (`Monster/Ultrametric.agda`)"
      target := "the prefix geometry"
      statement := "No map presents the walk distance as a prefix distance; the \
                    Agda module postulates a strong triangle law that is false."
      claim := ∃ f : AgdaMirror.MonsterWalk.Mask → Addr 15 Bool,
        ∀ x y, AgdaMirror.MonsterWalk.dMask x y = Addr.dist (f x) (f y)
      refutation := walk_not_prefix }
  , { source := "Cognition \"public zero\" constraint"
      target := "an atomic supervoxel"
      statement := "Distinct hidden states share the observable zero, so the \
                    coarse constraint does not determine the fine state."
      claim := Cuisine.SupervoxelClopen.Atomic (psychSystem Unit) .publicZero
      refutation := publicZero_not_atomic }
  , { source := "hyperfabric support map (observer-level)"
      target := "a symmetry reduction of the polarity involution"
      statement := "There is *no* map on the Boolean layer making the support \
                    observer intertwine the polarity involution — the square \
                    fails already at the unary symmetry, before any binary law \
                    is considered.  So the correct scope of the `support` \
                    negatives is this observer's choice of origin, not the SSP \
                    layer: the same action does descend along the \
                    polarity-invariant observer (`polarReduction`)."
      claim := ∃ f : Bool → Bool, ∀ t : Trit,
        Synthesis.Hyperfabric.support (Trit.inv t) =
          f (Synthesis.Hyperfabric.support t)
      refutation := support_no_equivariant_action }
  , { source := "the 9 → 6 polar projection (coarse chart without the residual)"
      target := "an equivariant quotient for the polarity action"
      statement := "No map on the six polar cells makes the polarity square \
                    commute for the residual-free 9 → 6 chart: that chart parks \
                    the zero branch on the negative sheet, so its origin is not \
                    symmetric.  Retaining the residual in the *target* repairs \
                    equivariance — the 9 → 6 + 3 projection is an \
                    `EquivariantQuotient` with nontrivial induced action \
                    (`polarResultReduction`)."
      claim := ∃ f : PolarResidual.PolarPhaseCell → PolarResidual.PolarPhaseCell,
        ∀ c : PolarResidual.FullPhaseCell,
          Residual.polarCoarse (negateCell c) = f (Residual.polarCoarse c)
      refutation := StructuredObserver.polar6_no_equivariant_action }
  , { source := "the nine SU(2) operator slots"
      target := "the nine SSP full phase cells"
      statement := "Equal cardinality is not a map: the two nine-element \
                    carriers admit more than one bijection, so the shared \
                    numeral does not pick one out."
      claim := ∀ e f : Physics369.MatrixSlot ≃ PolarResidual.FullPhaseCell, e = f
      refutation := by
        obtain ⟨e, f, hef⟩ := Physics369.matrixSlot_no_canonical_phase_cell
        exact fun h => hef (h e f) }
  ]

/-! ## The sockets -/

/-- Places where the corpus supplies an unconstrained record, with a proof that
nothing is constrained. -/
def sockets : List Socket :=
  [ { site := "SSP369ClopenBallBridge.PrefixBallClopenAuthority"
      role := "certifying that a prefix ball is clopen"
      underdetermined := ∀ B : PrefixBall 3 Digit369,
        Nonempty (ClopenAuthority B ≃ ClopenWitness × ClopenWitness)
      witness := fun B => ⟨authorityContentless B⟩ }
  , { site := "SSPTritCarrier.SSPTritCarrierReceipt"
      role := "certifying a trit-carrier bridge"
      underdetermined := ∀ t : Trit, ∃ R : ReceiptSocket.Receipt,
        ∃ h : R.carrier = Trit, (h ▸ R.negativeValue) = t
      witness := ReceiptSocket.alignment_unconstrained }
  , { site := "ClopenPsychologicalSupervoxel.ClopenPsychologyBoundary"
      role := "recording that the public zero is non-atomic and that the \
               subvoxel mechanism is not clinically validated"
      underdetermined := Nonempty (PsychologyBoundary ≃ Unit)
      witness := ⟨boundaryContentless⟩ }
  ]

/-! ## What the registry does *not* contain

There is no row for `ConstraintClopenRefinement.RefinementSystem` as used by any
domain module, because the source never instantiates it; `Integration.Refinement`
supplies the two inhabitants (`loomRefinement`, `addressRefinement`) that make
the record non-vacuous.  There is no row connecting the 15-prime layer to the
Monster group, to moonshine or to a vertex algebra, because no such object is
defined anywhere in the corpus.  Every distance in *this file* is a natural
number on a finite carrier; the analytic (RH/zeta) lane is registered separately
in `Integration.RiemannDomain`, in the same `Entry` / `Boundary` / `Socket`
vocabulary but over `ℝ` and `ℂ`. -/

end Integration.Registry
