import Integration.OpenAIMath.PriorityAtlas

namespace Integration.OpenAIMath

/-- A concrete upstream result routed into DASHI.  This records provenance and scope only. -/
structure RoutedSource where
  familyId : String
  title : String
  authority : UpstreamAuthorityLevel
  solutionModule : String
  declaration : String
  comparator : String
  dashiProgramme : DASHIProgramme
  relevance : RelevanceClass
  provesFullRiemannHypothesis : Bool := false
  provesGeneralBSD : Bool := false
  provesGeneralHodgeConjecture : Bool := false
  provesPNotEqualsNP : Bool := false
  provesClayNavierStokes : Bool := false
  provesYangMillsMassGap : Bool := false
  sameObjectTransportPaid : Bool := false
  dashiPortPaid : Bool := false
  deriving Repr

/-- Family 003: exact upstream Lean theorem source for the zeta zero-free half-plane Re(s)>7/8. -/
def quasiRiemann : RoutedSource :=
  { familyId := "003"
    title := "The quasi-Riemann hypothesis"
    authority := .leanDeclaration
    solutionModule := "OAI.NumberTheory.DirichletL.Nonvanishing"
    declaration := "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
    comparator := "ComparatorChallenges.QuasiRiemannHypothesis"
    dashiProgramme := .riemannHypothesis
    relevance := .directFrontier }

/-- Family 102: formalized Unique Games / optimal Max-Cut hardness donor. -/
def uniqueGamesMaxCut : RoutedSource :=
  { familyId := "102"
    title := "The Unique Games Conjecture and optimal approximation thresholds"
    authority := .leanDeclaration
    solutionModule := "OAI.Computability.MaxCut.Main"
    declaration := "OAI.OptimalMaxCut.main"
    comparator := "ComparatorChallenges.OptimalMaxCut"
    dashiProgramme := .pVersusNP
    relevance := .lemmaDonor }

/-- Family 362: global smooth classical relativistic Vlasov-Maxwell source theorem. -/
def relativisticVlasovMaxwell : RoutedSource :=
  { familyId := "362"
    title := "Global smoothness for relativistic Vlasov-Maxwell"
    authority := .leanDeclaration
    solutionModule := "OAI.Analysis.VlasovMaxwell.Main"
    declaration := "OAI.RVM.global_classical_solution"
    comparator := "ComparatorChallenges.VlasovMaxwell"
    dashiProgramme := .quantumMathematics
    relevance := .lemmaDonor }

/-- Family 376: formalized computation inside smooth *forced* Navier-Stokes flows. -/
def forcedNavierStokesComputation : RoutedSource :=
  { familyId := "376"
    title := "Universal computation in forced Navier-Stokes flows"
    authority := .leanDeclaration
    solutionModule := "OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult"
    declaration := "OAI.BalancedTransport.balanced_three_stack_realization"
    comparator := "ComparatorChallenges.ForcedNavierStokesComputation"
    dashiProgramme := .navierStokes
    relevance := .lemmaDonor }

/-- Family 032 is scientifically relevant to DASHI Hodge work, but this receipt does not claim an upstream Lean theorem. -/
def hodgeCM : RoutedSource :=
  { familyId := "032"
    title := "The rational Hodge conjecture for CM abelian varieties"
    authority := .manuscript
    solutionModule := ""
    declaration := ""
    comparator := ""
    dashiProgramme := .hodge
    relevance := .directFrontier }

/-- Family 002 is scientifically relevant to DASHI BSD work, but this receipt does not claim an upstream Lean theorem. -/
def bsdLowSelmer : RoutedSource :=
  { familyId := "002"
    title := "The full BSD formula from low Selmer corank"
    authority := .manuscript
    solutionModule := ""
    declaration := ""
    comparator := ""
    dashiProgramme := .birchSwinnertonDyer
    relevance := .directFrontier }

/-- Comparator challenge files contain target statements with `sorry`; proof authority lives in the declared solution module. -/
def comparatorChallengeIsProofAuthority : Bool := false

/-- The routed atlas never manufactures a solution to a broader Millennium problem. -/
def sourceAtlasPromotesMillenniumClaims : Bool := false


/-- An upstream proof released after our immutable vendor pin. This metadata
does NOT cause the pinned submodule to contain the source theorem or make a
DASHI kernel acceptance claim. Source status and import status are different. -/
structure LaterUpstreamReceipt where
  familyId : String
  observedUpstreamCommit : String
  releaseDate : String
  solutionModule : String
  declaration : String
  comparator : String
  presentAtPinnedVendor : Bool := false
  dashiKernelVerified : Bool := false
  sameObjectTransportPaid : Bool := false
  deriving Repr

/-- Family 378: the October 26 addition, inspected directly in the public
upstream Lean solution and Comparator sources. Exact count, SAT, machine steps,
and all-prefix visited-tape bounds; *not* a proof of P = NP.
Previous DASHI SAT compiler results have independent ownership and do not
supply this runtime theorem. -/
def ethSubexponentialLater : LaterUpstreamReceipt :=
  { familyId := "378"
    observedUpstreamCommit := "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
    releaseDate := "2026-10-26"
    solutionModule := "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final"
    declaration := "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat"
    comparator := "ComparatorChallenges.SubexponentialSAT" }

/-- The current DASHI source pin predates the later family-378 source. -/
theorem laterEthNotPresentInVendor :
    ethSubexponentialLater.presentAtPinnedVendor = false := rfl

/-- A separately pinned, local same-object proof receipt remains unpaid. -/
theorem laterEthNotYetDashiVerified :
    ethSubexponentialLater.dashiKernelVerified = false := rfl

end Integration.OpenAIMath
