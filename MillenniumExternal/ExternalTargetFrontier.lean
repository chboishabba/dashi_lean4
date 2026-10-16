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
      firstUnpaid := "lower the existing behavioural Kleene self-specialization onto the actual CodedFiniteStandardTM candidate/generator model, then close one final same-object resource budget T* after static program-size feedback"
      note := "Live Agda #1129 now has exact costed streamed Cook access, finite local tables, exact candidate run transport, an exact-T quiescent phase compiler, exact phase-lift state/rule growth, a literal unary cursor, and a literal fixed Cook bitstream lookup TM with exact in-range query semantics. The full-table machine is a baseline, not the surviving self-fixed architecture: literal whole-own-formula materialisation is already closed for anchored candidates, strict raw-code growth blocks syntactic fixed points, and the new one-hot state-width theorem feeds machine size back into the actual Cook quotation. Existing Kleene machinery identifies behavioural/semantic fixed points as the correct self-reference notion, but the older finite-code Q2 primitive erases its quoted program and therefore does not yet instantiate that theorem on the current coded standard-TM generator. Recent XOR-grid work remains a bounded implementation donor only: XOR supplies recoverable local data updates for compact ripple-borrow control, while borrow is separate and IIT phi is not complexity hardness evidence. After the behavioural same-object compiler, the principal wall is the final self-description/runtime resource fixed point T*." }
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
