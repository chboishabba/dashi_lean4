import MillenniumExternal.TerminalCensus

namespace MillenniumExternal

inductive AdapterState where
  | greenExact
  | proofResolutionPending
  | sourceExactKernelPending
  | redType
  | redMath
  | upstreamIncomplete
  | upstreamSolvedUnformalized
  deriving DecidableEq, BEq, Repr

inductive FrontierClass where
  | proved
  | proofResolution
  | typeWeld
  | analytic
  | upstreamDefect
  | solvedUnformalized
  deriving DecidableEq, BEq, Repr

structure ExternalTargetReceipt where
  problem : Problem
  upstreamDeclaration : String
  state : AdapterState
  frontier : FrontierClass
  firstUnpaid : String
  note : String
  deriving DecidableEq, Repr

def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .proofResolutionPending
      frontier := .proofResolution
      firstUnpaid := "build literal generator microcode for the index-only ABI / finite local kernel tables, then provide a fresh-dispatch exact-T phase boundary (quiescent endpoint or clock/phase wrapper), concrete generator/suffix runs, and close their additive time inside the same Cook budget"
      note := "Live Agda #1129 is now past generic finite-machine plumbing. The own-Cook streamed evaluator has an index-only ABI; transition/acceptance kernels are same-object finite tables; mode sum, safe links and resident transition preservation are paid; CodedFiniteStandardLinkedStructuralSimulationExact gives the actual candidate submachine simulation; CodedFiniteStandardLinkedRunSimulationExact lifts the actual coded polynomial candidate execution edge-for-edge with identical step count and composes prefix ; candidate ; suffix exact runs. The exact linked candidate middle run is therefore paid. A determinism obstruction is also explicit: CodedFiniteStandardReturnLinkFreshnessExact proves a safe return link cannot share a fresh dispatch key with a resident candidate rule. Since StandardFiniteCandidateCode does not state that its declared T-step finish is quiescent, direct return is not automatic. The live compiler residual is therefore the literal generator fragment plus a true exact-T phase boundary (fresh/quiescent endpoint or clock/phase wrapper), surrounding runs, and final same Cook budget closure. Generic ConcreteTapeStandardClockExact remains the post-construction clock receipt." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .proofResolutionPending
      frontier := .proofResolution
      firstUnpaid := "locate and compose the existing global RH terminal donor into Mathlib.RiemannHypothesis"
      note := "LeanDojo already proves its exact Clay statement equivalent to Mathlib.RiemannHypothesis. Current Lean PR #50 still exposes genuine A1/A2/Route-B analytic producers rather than an unconditional root theorem; finite C3/Eisenstein/Ogg cross-pollinations do not discharge those analytic leaves." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanC|D"
      state := .sourceExactKernelPending
      frontier := .proved
      firstUnpaid := "exact-head kernel/axiom acceptance of DASHILiteralClayNS.dashiExactFeffermanC and dashiExactFeffermanD"
      note := "Force decay, momentum, divergence, energy, boundary and carrier transports are paid. LeanDojoExactTerminal contains literal exact C/D theorem terms. No mathematical or same-object theorem remains at this external boundary." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "a faithful external Clay Hodge target"
      note := "Pinned LeanDojo marks this statement incomplete. DASHI's stronger faithful algebraic-cycle/Hodge programme is not weakened to fit an incomplete external interface." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .proofResolutionPending
      frontier := .proofResolution
      firstUnpaid := "locate the existing same-curve analytic bridge and universal zero Selmer defect donors, compose BSDClayCoreObligation, then transport it into LeanDojo Rank.Existence"
      note := "Under UniversalSelmerDefectAnalyticBridge, BSDClayCoreObligation is equivalent to UniversalSelmerDefectZero. The selected-CM E[2]/Sha[2] and j=0/Eisenstein symmetry work remain useful local donors but do not supply the universal defect or analytic bridge." }
  , { problem := .yangMills
      upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "a faithful external Jaffe--Witten target"
      note := "Pinned LeanDojo marks this interface incomplete. DASHI's stronger OS/RP continuum-QFT, Hamiltonian and mass-gap physical-object programme remains authoritative; unrelated quantum/geometry benchmark closures do not create the actual YM cutoff/OS same-object inhabitants." }
  , { problem := .poincare
      upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
      state := .upstreamSolvedUnformalized
      frontier := .solvedUnformalized
      firstUnpaid := "upstream does not include Perelman's proof term"
      note := "Historically solved; retained only as an external-registry regression target." }
  ]

theorem externalTargetReceipts_length : externalTargetReceipts.length = 7 := by decide

def hasGreenExact (p : Problem) : Bool :=
  externalTargetReceipts.any fun r => r.problem == p && r.state == .greenExact

theorem faithful_active_lanes_not_red_math :
    (externalTargetReceipts.filter (fun r =>
      r.problem == .pVersusNP || r.problem == .riemann ||
      r.problem == .navierStokes || r.problem == .birchSwinnertonDyer)).all
        (fun r => r.state != .redMath) = true := by decide

theorem pnp_is_proof_resolution_pending :
    (externalTargetReceipts.find? (fun r => r.problem == .pVersusNP)).map
        (fun r => r.state) = some .proofResolutionPending := by decide

theorem riemann_is_proof_resolution_pending :
    (externalTargetReceipts.find? (fun r => r.problem == .riemann)).map
        (fun r => r.state) = some .proofResolutionPending := by decide

theorem navierStokes_frontier_is_proved :
    (externalTargetReceipts.find? (fun r => r.problem == .navierStokes)).map
        (fun r => r.frontier) = some .proved := by decide

theorem navierStokes_source_exact_kernel_pending :
    (externalTargetReceipts.find? (fun r => r.problem == .navierStokes)).map
        (fun r => r.state) = some .sourceExactKernelPending := by decide

theorem birchSwinnertonDyer_is_proof_resolution_pending :
    (externalTargetReceipts.find? (fun r => r.problem == .birchSwinnertonDyer)).map
        (fun r => r.state) = some .proofResolutionPending := by decide

theorem hodge_not_green_exact : hasGreenExact .hodge = false := by decide

theorem yangMills_not_green_exact : hasGreenExact .yangMills = false := by decide

theorem poincare_not_green_exact : hasGreenExact .poincare = false := by decide

end MillenniumExternal
