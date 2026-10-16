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

end DASHITOE
