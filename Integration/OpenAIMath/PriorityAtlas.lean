import Integration.OpenAIMath.FormalizationStatus

namespace Integration.OpenAIMath

/-- Live DASHI programmes for which the OpenAI corpus is worth routing/searching. -/
inductive DASHIProgramme where
  | riemannHypothesis
  | birchSwinnertonDyer
  | hodge
  | yangMills
  | navierStokes
  | pVersusNP
  | ellipticCM
  | exceptionalRepresentation
  | quantumMathematics
  | fourierHarmonic
  | finiteCombinatorics
  deriving DecidableEq, Repr

/-- Routing significance only. This is not theorem authority. -/
inductive RelevanceClass where
  | directFrontier
  | lemmaDonor
  | independentCrossCheck
  | backgroundOnly
  deriving DecidableEq, Repr

structure PriorityEntry where
  programme : DASHIProgramme
  relevance : RelevanceClass
  routingNote : String
  sameObjectTransportPaid : Bool := false
  theoremPromotionPaid : Bool := false
  deriving Repr

/--
Initial max-cut routing. `directFrontier` means "search this corpus first when
working the named DASHI frontier"; it does not assert that the corpus contains
or proves the missing theorem.
-/
def priorityFor : DASHIProgramme → PriorityEntry
  | .riemannHypothesis => ⟨.riemannHypothesis, .directFrontier,
      "Search analytic number theory, zeta/L-function and explicit-estimate formalizations first."⟩
  | .birchSwinnertonDyer => ⟨.birchSwinnertonDyer, .directFrontier,
      "Search elliptic-curve, Selmer, L-function and arithmetic-geometry formalizations first."⟩
  | .hodge => ⟨.hodge, .directFrontier,
      "Search algebraic geometry, cohomology, cycles and Hodge-theoretic formalizations first."⟩
  | .yangMills => ⟨.yangMills, .independentCrossCheck,
      "Search gauge/analysis infrastructure, but do not infer a Clay-level continuum or mass-gap theorem."⟩
  | .navierStokes => ⟨.navierStokes, .directFrontier,
      "Search PDE, harmonic-analysis, regularity and inequality formalizations first."⟩
  | .pVersusNP => ⟨.pVersusNP, .independentCrossCheck,
      "Search complexity/combinatorics infrastructure; no topic match promotes a separation theorem."⟩
  | .ellipticCM => ⟨.ellipticCM, .directFrontier,
      "Search elliptic curves, modular forms, characters, local factors and CM arithmetic first."⟩
  | .exceptionalRepresentation => ⟨.exceptionalRepresentation, .lemmaDonor,
      "Search algebra, Lie/representation, finite-group and invariant-theory formalizations for reusable lemmas."⟩
  | .quantumMathematics => ⟨.quantumMathematics, .lemmaDonor,
      "Search operator, matrix, probability and geometry formalizations; physical identification remains separate."⟩
  | .fourierHarmonic => ⟨.fourierHarmonic, .lemmaDonor,
      "Search Fourier, spectral and harmonic-analysis formalizations for reusable analytic components."⟩
  | .finiteCombinatorics => ⟨.finiteCombinatorics, .lemmaDonor,
      "Search finite combinatorics, graph and counting formalizations for reusable exact lemmas."⟩

/-- The atlas is a routing index only. -/
def priorityAtlasPromotesTheorems : Bool := false

end Integration.OpenAIMath
