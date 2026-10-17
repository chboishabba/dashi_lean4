namespace DASHITOE

inductive TheoremRouteClass where
  | directSameObjectCandidate
  | lemmaDonor
  | structuralDonor
  | independentCrossCheck
  | backgroundOnly
  deriving Repr, DecidableEq

structure TheoremRoute where
  family : String
  upstreamModule : String
  upstreamDeclaration : String
  targetLeaf : String
  classification : TheoremRouteClass
  sameObjectTransportPaid : Bool
  deriving Repr

def openAITheoremRoutes : List TheoremRoute :=
  [ { family := "003"
      upstreamModule := "OAI.NumberTheory.DirichletL.Nonvanishing"
      upstreamDeclaration := "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
      targetLeaf := "RH analytic leaf; finite-order Hecke/Q(sqrt(-3)) donor for arithmetic-CM continuation"
      classification := .lemmaDonor
      sameObjectTransportPaid := false },
    { family := "102"
      upstreamModule := "OAI.Computability.MaxCut.Main"
      upstreamDeclaration := "OAI.OptimalMaxCut.main"
      targetLeaf := "complexity/P-vs-NP reduction infrastructure"
      classification := .structuralDonor
      sameObjectTransportPaid := false },
    { family := "362"
      upstreamModule := "OAI.Analysis.VlasovMaxwell.Main"
      upstreamDeclaration := "OAI.RVM.global_classical_solution"
      targetLeaf := "electromagnetic/gauge continuum effective dynamics"
      classification := .lemmaDonor
      sameObjectTransportPaid := false },
    { family := "376"
      upstreamModule := "OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult"
      upstreamDeclaration := "OAI.BalancedTransport.balanced_three_stack_realization"
      targetLeaf := "forced Navier-Stokes computation/effective dynamics"
      classification := .structuralDonor
      sameObjectTransportPaid := false } ]

inductive ExternalFormalAuthority where
  | importedFormalSource
  | localLeanPort
  | localKernelReceipt
  deriving Repr, DecidableEq

structure ExternalTheoremInhabitant where
  repository : String
  pinnedCommit : String
  family : String
  moduleName : String
  declarationName : String
  authority : ExternalFormalAuthority
  localLeanProofTerm : Bool
  sameObjectTOETransport : Bool
  deriving Repr


def theoremInhabitantFromRoute (r : TheoremRoute) : ExternalTheoremInhabitant :=
  { repository := "openai/math"
    pinnedCommit := "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
    family := r.family
    moduleName := r.upstreamModule
    declarationName := r.upstreamDeclaration
    authority := .importedFormalSource
    localLeanProofTerm := false
    sameObjectTOETransport := false }


def quasiRiemannFormalInhabitant : ExternalTheoremInhabitant :=
  theoremInhabitantFromRoute openAITheoremRoutes[0]!


def optimalMaxCutFormalInhabitant : ExternalTheoremInhabitant :=
  theoremInhabitantFromRoute openAITheoremRoutes[1]!


def vlasovMaxwellFormalInhabitant : ExternalTheoremInhabitant :=
  theoremInhabitantFromRoute openAITheoremRoutes[2]!


def forcedNavierStokesFormalInhabitant : ExternalTheoremInhabitant :=
  theoremInhabitantFromRoute openAITheoremRoutes[3]!


def canonicalOpenAITheoremInhabitants : List ExternalTheoremInhabitant :=
  [quasiRiemannFormalInhabitant, optimalMaxCutFormalInhabitant,
   vlasovMaxwellFormalInhabitant, forcedNavierStokesFormalInhabitant]

end DASHITOE
