import RequestProject.Mereology

/-!
# TPS-grounded quantum mereology

This module keeps four layers distinct:

1. a bare quantum carrier/state/Hamiltonian;
2. a tensor-product structure (TPS), which supplies subsystem structure;
3. TPS-indexed entanglement/interaction relations;
4. an emergent-geometry consumer built only after a TPS and pair relation exist.

The classical benchmark is the repository's existing Wikidata.MKB executable
mereology. Its theorems are reused directly rather than reimplemented here.

Scientific source boundary:
* Carroll--Singh, Phys. Rev. A 103, 022213 (2021),
  DOI 10.1103/PhysRevA.103.022213.
* Cao--Carroll--Michalakis, Phys. Rev. D 95, 024031 (2017),
  DOI 10.1103/PhysRevD.95.024031.
* Pasqualini--Fortin, Entropy 28(6), 627 (2026),
  DOI 10.3390/e28060627.

Citations motivate interfaces only. They do not create local proof of a unique
preferred TPS, a canonical TPS meet, emergent geometry, or full GR.
-/

namespace QuantumMereology

structure BareQuantumWorld where
  State : Type
  Hamiltonian : Type
  evolve : Hamiltonian → State → State

structure TensorProductStructure (W : BareQuantumWorld) where
  Subsystem : Type
  FactorIndex : Type
  subsystemAt : FactorIndex → Subsystem
  partOfCarrier : Subsystem → Prop
  reconstructsCarrier : Prop
  reconstruction : reconstructsCarrier
  Entangled : W.State → Subsystem → Subsystem → Prop
  Interacts : W.Hamiltonian → Subsystem → Subsystem → Prop

structure EntanglementObservation
    (W : BareQuantumWorld) (T : TensorProductStructure W) where
  state : W.State
  left right : T.Subsystem
  entangled : T.Entangled state left right

structure QuasiclassicalCriterion
    (W : BareQuantumWorld) (T : TensorProductStructure W) where
  PointerState : Type
  pointerStateLivesIn : PointerState → W.State → Prop
  RobustAgainstEnvironment : PointerState → Prop
  EntanglementGrowthControlled : PointerState → Prop
  LocalizedAroundClassicalTrajectory : PointerState → Prop
  selectedPointer : PointerState
  robust : RobustAgainstEnvironment selectedPointer
  controlledGrowth : EntanglementGrowthControlled selectedPointer
  localized : LocalizedAroundClassicalTrajectory selectedPointer

structure PreferredTPSCandidate (W : BareQuantumWorld) where
  tps : TensorProductStructure W
  criterion : QuasiclassicalCriterion W tps

structure TPSRefinementSpace (W : BareQuantumWorld) where
  TPS : Type
  realizes : TPS → TensorProductStructure W
  Refines : TPS → TPS → Prop

structure CommonTPSRefinement
    {W : BareQuantumWorld}
    (R : TPSRefinementSpace W)
    (left right : R.TPS) where
  common : R.TPS
  refinesLeft : R.Refines common left
  refinesRight : R.Refines common right

structure CanonicalMeetAuthority
    {W : BareQuantumWorld}
    (R : TPSRefinementSpace W) where
  meet : R.TPS → R.TPS → R.TPS
  meetRefinesLeft : ∀ left right, R.Refines (meet left right) left
  meetRefinesRight : ∀ left right, R.Refines (meet left right) right

/-! ## Existing classical Wikidata mereology as benchmark -/

structure ClassicalBenchmark where
  mkb : Wikidata.MKB
  wellFormed : mkb.mWellFormed = true
  acyclic : mkb.mAcyclic = true
  noClassConfusion : mkb.noClassConfusion = true

theorem classical_overlap_comm (B : ClassicalBenchmark)
    (a b : Wikidata.Qid) :
    B.mkb.overlapsB a b = B.mkb.overlapsB b a :=
  Wikidata.MKB.overlapsB_comm B.mkb a b

theorem classical_proper_part_trans (B : ClassicalBenchmark)
    {a b c : Wikidata.Qid}
    (hab : B.mkb.isProperPartOfB a b = true)
    (hbc : B.mkb.isProperPartOfB b c = true) :
    B.mkb.isProperPartOfB a c = true :=
  Wikidata.MKB.properPartOf_trans B.wellFormed B.acyclic hab hbc

theorem classical_proper_whole_wf (B : ClassicalBenchmark) :
    WellFounded (fun b a : Wikidata.Qid =>
      B.mkb.isProperPartOfB a b = true) :=
  Wikidata.MKB.properWhole_wf B.wellFormed B.acyclic

theorem classical_overlap_mono (B : ClassicalBenchmark)
    {a b c : Wikidata.Qid}
    (hab : B.mkb.isPartOfB a b = true)
    (hca : B.mkb.overlapsB c a = true) :
    B.mkb.overlapsB c b = true :=
  Wikidata.MKB.overlapsB_mono B.wellFormed hab hca

theorem classical_part_not_subclass (B : ClassicalBenchmark)
    {a b : Wikidata.Qid} (hab : B.mkb.Part a b) :
    B.mkb.base.isSubclassOf a b = false :=
  Wikidata.MKB.part_not_subclass B.noClassConfusion hab

theorem classical_part_not_instance (B : ClassicalBenchmark)
    {a b : Wikidata.Qid} (hab : B.mkb.Part a b) :
    B.mkb.base.isInstanceOf a b = false :=
  Wikidata.MKB.part_not_instance B.noClassConfusion hab

theorem classical_part_complete_exhibits (B : ClassicalBenchmark)
    {a c c' d : Wikidata.Qid}
    (hcomp : B.mkb.partCompleteB a = true)
    (hac : B.mkb.base.isInstanceOf a c = true)
    (hcc' : B.mkb.base.isSubclassOf c c' = true)
    (hd : (c', d) ∈ B.mkb.partClasses) :
    ∃ p ∈ B.mkb.base.items,
      B.mkb.isProperPartOfB p a = true ∧
      B.mkb.base.isInstanceOf p d = true :=
  Wikidata.MKB.partComplete_exhibits
    (Wikidata.MKB.mwf_base B.wellFormed) hcomp hac hcc' hd

/-! ## Attribution roles

The repo keeps external source claims, local formal reconstruction,
cross-module inference, and new DASHI theorems distinct.
-/

inductive AttributionRole where
  | externalSourceClaim
  | localFormalReconstruction
  | crossModuleInference
  | newDASHITheorem
deriving Repr, DecidableEq

structure AttributionReceipt where
  role : AttributionRole
  owner : String
  claim : String
deriving Repr, DecidableEq

/-! ## Attributed scientific source receipts -/

structure SourceReceipt where
  authors : String
  title : String
  venue : String
  year : String
  identifier : String
  supports : String
deriving Repr, DecidableEq

def carrollSinghObjectiveClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
  claim := "The source proposes an in-principle preferred-factorisation search minimizing a combination of entanglement growth and internal spreading for quasiclassical subsystem behaviour."

def pasqualiniFortinNoCanonicalMeetClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Matías Pasqualini; Sebastian Fortin, Entropy 28(6), 627 (2026)"
  claim := "The source argues that TPS space lacks the canonical global meet/lattice structure of classical partition mereology."

def dashiSelectionReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Typed candidate/criterion/selection records reconstruct the source-described preferred-TPS search without importing existence, uniqueness, or physical correctness."

def dashiObserverCrossModuleReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI"
  claim := "Consumer-sufficiency/non-factorability logic is applied to TPS criterion observations only after the candidate family and downstream consumer are declared."

def dashiFiniteNoMeetTheoremReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "The finite two-tag refinement regression has no CanonicalMeetAuthority; this is not the Pasqualini--Fortin physical TPS theorem."

def carrollSingh2021 : SourceReceipt where
  authors := "Sean M. Carroll; Ashmeet Singh"
  title := "Quantum mereology: Factorizing Hilbert space into subsystems with quasiclassical dynamics"
  venue := "Physical Review A 103, 022213"
  year := "2021"
  identifier := "doi:10.1103/PhysRevA.103.022213"
  supports := "Preferred-TPS research program from Hilbert space plus Hamiltonian using pointer robustness and an in-principle objective combining entanglement growth with internal spreading/localization around approximately classical trajectories."

def caoCarrollMichalakis2017 : SourceReceipt where
  authors := "ChunJun Cao; Sean M. Carroll; Spyridon Michalakis"
  title := "Space from Hilbert space: Recovering geometry from bulk entanglement"
  venue := "Physical Review D 95, 024031"
  year := "2017"
  identifier := "doi:10.1103/PhysRevD.95.024031"
  supports := "Given a supplied TPS, entanglement/mutual-information relations can feed an emergent spatial-geometry construction under stated assumptions."

def pasqualiniFortin2026 : SourceReceipt where
  authors := "Matías Pasqualini; Sebastian Fortin"
  title := "Towards a Tensor Product Structure-Grounded Mereology"
  venue := "Entropy 28(6), 627"
  year := "2026"
  identifier := "doi:10.3390/e28060627"
  supports := "TPS-grounded quantum mereology and the sourced claim that the TPS refinement space lacks a canonical global meet analogous to a classical partition lattice."

/-! ## Entanglement relations are downstream of the TPS -/

structure FactorRelationGeometry
    (W : BareQuantumWorld) (T : TensorProductStructure W) where
  Weight : Type
  Distance : Type
  Geometry : Type
  pairWeight : W.State → T.Subsystem → T.Subsystem → Weight
  distanceFromWeight : Weight → Distance
  geometryFromDistances : (T.Subsystem → T.Subsystem → Distance) → Geometry

def emergentDistance
    {W : BareQuantumWorld} {T : TensorProductStructure W}
    (G : FactorRelationGeometry W T)
    (state : W.State) (left right : T.Subsystem) : G.Distance :=
  G.distanceFromWeight (G.pairWeight state left right)

def emergentGeometry
    {W : BareQuantumWorld} {T : TensorProductStructure W}
    (G : FactorRelationGeometry W T)
    (state : W.State) : G.Geometry :=
  G.geometryFromDistances (emergentDistance G state)

structure EntanglementCurvatureResponse
    {W : BareQuantumWorld} {T : TensorProductStructure W}
    (G : FactorRelationGeometry W T) where
  Perturbation : Type
  CurvatureResponse : Type
  perturbState : Perturbation → W.State → W.State
  curvatureResponse : Perturbation → W.State → CurvatureResponse
  SpatialEinsteinAnalogue : Prop
  spatialEinsteinAnalogue : SpatialEinsteinAnalogue

/-! ## Source/promotion firewalls -/

structure SourceBoundary where
  bareCarrierSelectsUniqueTPS : Bool := false
  hamiltonianAloneLocallyProvesUniqueTPS : Bool := false
  entanglementIsFactorisationIndependent : Bool := false
  tpsRefinementHasBuiltInGlobalMeet : Bool := false
  selectedTPSAlreadyIsEmergentGeometry : Bool := false
  spatialEinsteinAnalogueIsFullGR : Bool := false
  sourceNoCanonicalMeetIsKernelTheorem : Bool := false
deriving Repr, DecidableEq

def canonicalSourceBoundary : SourceBoundary := {}

theorem bare_carrier_does_not_select_unique_tps_by_definition :
    canonicalSourceBoundary.bareCarrierSelectsUniqueTPS = false := rfl

theorem entanglement_not_factorisation_independent_by_definition :
    canonicalSourceBoundary.entanglementIsFactorisationIndependent = false := rfl

theorem no_built_in_global_tps_meet :
    canonicalSourceBoundary.tpsRefinementHasBuiltInGlobalMeet = false := rfl

theorem sourced_no_meet_claim_not_kernel_theorem :
    canonicalSourceBoundary.sourceNoCanonicalMeetIsKernelTheorem = false := rfl

/-!
Pasqualini--Fortin's 2026 result is represented by the absence of a built-in
meet from TPSRefinementSpace and by a source boundary. The local kernel does
not claim the mathematical no-go theorem until an independent formalisation of
their TPS equivalence/refinement space is supplied.
-/


/-! ## Finite structural no-meet regression

This proves only that the abstract TPSRefinementSpace interface does not force
a meet. It is not the Pasqualini--Fortin theorem about the physical TPS space.
-/

inductive ToyTPSTag where
  | left
  | right
deriving Repr, DecidableEq

def toyWorld : BareQuantumWorld where
  State := Unit
  Hamiltonian := Unit
  evolve := fun _ _ => ()

def toyTPS : TensorProductStructure toyWorld where
  Subsystem := Unit
  FactorIndex := Unit
  subsystemAt := fun _ => ()
  partOfCarrier := fun _ => True
  reconstructsCarrier := True
  reconstruction := trivial
  Entangled := fun _ _ _ => True
  Interacts := fun _ _ _ => True

def toyRefinementSpace : TPSRefinementSpace toyWorld where
  TPS := ToyTPSTag
  realizes := fun _ => toyTPS
  Refines := fun a b => a = b

theorem toy_refinement_space_has_no_canonical_meet :
    ¬ Nonempty (CanonicalMeetAuthority toyRefinementSpace) := by
  rintro ⟨A⟩
  have hL := A.meetRefinesLeft ToyTPSTag.left ToyTPSTag.right
  have hR := A.meetRefinesRight ToyTPSTag.left ToyTPSTag.right
  have h : ToyTPSTag.left = ToyTPSTag.right := hL.symm.trans hR
  cases h

end QuantumMereology
