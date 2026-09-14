import Promoted.AgdaMirrorLean.MoonshineEarn
import Promoted.JMD.ArchitectureDynamics
import Promoted.JMD.FactorVecSheaf
import Promoted.MonsterLean.LogarithmicAnalysis
import Promoted.RequestProject.Archimedes369
import Promoted.RequestProject.CenterRetraction
import Promoted.RequestProject.Core
import Promoted.RequestProject.DeltaModular
import Promoted.RequestProject.Epistemic.Observer
import Promoted.RequestProject.Epistemic.Trit
import Promoted.RequestProject.Frobenius
import Promoted.RequestProject.GF27
import Promoted.RequestProject.GradedClock
import Promoted.RequestProject.Hecke23
import Promoted.RequestProject.Main
import Promoted.RequestProject.Matching
import Promoted.RequestProject.Meta.Provenance
import Promoted.RequestProject.OggPrimes
import Promoted.RequestProject.PaletteUniversality
import Promoted.RequestProject.PascalTower
import Promoted.RequestProject.PrimeFibers
import Promoted.RequestProject.Reachability
import Promoted.RequestProject.SporadicAtlas
import Promoted.RequestProject.Ternary.Balanced
import Promoted.RequestProject.Tesla369
import Promoted.RequestProject.UltrametricTaxonomy
import Promoted.RequestProject.Wikidata.Reachability
import Promoted.RequestProject.ZetaMoonshine
import Promoted.RiemannAnalytic.ChebyshevLower
import Promoted.RiemannAnalytic.CubicPhase
import Promoted.RiemannAnalytic.ExteriorCore
import Promoted.RiemannAnalytic.FrobeniusDecomposition
import Promoted.RiemannAnalytic.LiteralStatement
import Promoted.RiemannAnalytic.OggAffineGrid
import Promoted.RiemannAnalytic.PoissonExtension
import Promoted.RiemannAnalytic.RelativeContraction
import Promoted.RiemannAnalytic.ShortIntervalMeanValue
import Promoted.Tao.TaoFramework
import Promoted.Zeta23.Defs
import Promoted.Zeta23.Defs.LeafIntegrals
import Promoted.Zeta23.FromPNTPlus.Mathlib.Algebra.Notation.Support
import Promoted.Zeta23.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Promoted.Zeta23.LinAlg.PosIndex
import Promoted.Zeta23.MV.EigenIdentity
import Promoted.Zeta23.MV.Spacing
import Promoted.Zeta23.PairCeiling.Defs
import Promoted.Zeta23.PairCeiling.NumericCert
import Promoted.Zeta23.Prelude.InstancePriorities
import Promoted.Zeta23.Tail.Basic
import Promoted.Zeta23.ThmD.Functional
import Promoted.Zeta23.XiPrime.Coeff.Param
import Promoted.Zeta23.XiPrime.ZeroCount.ArgBound
import Promoted.Zeta23Bridge.CertifiedFiniteCarrierReindex
import Promoted.Zeta23Bridge.OddTaylorDeterminant
import Promoted.Zeta23Bridge.ResidualBudgetMarginCompiler
import Promoted.Zeta23Bridge.TwoZeroUniversalRHBoundary
import Promoted.Zeta23Comparator.ChallengeDeps
import Promoted.Zeta23Comparator.ChallengeDeps.XiPrime

/-!
# `Promoted` — imported material that has been made a first-class build target

Everything in this library arrived in an Aristotle handoff archive and was, until
now, inert source sitting under `Lean/Imported`.  A file is promoted here exactly
when it clears the mechanical bar recorded in `Lean/Imported/PROMOTION_STATUS.csv`:

* it imports nothing but `Mathlib`, so it needs no library root of its own;
* `lake env lean` elaborates it in *this* toolchain, with no error;
* it contains no `sorry`, no `axiom`, no `native_decide` and no
  `@[implemented_by]`.

Promotion to this library is therefore the rung `elaborates` → `wired` of
`Integration.CorpusPromotion.Stage`, and nothing further.  In particular it is
**not** the rung `audited` or `cited`: the statements here have not been reviewed
against a source, no correspondence receipt is claimed for them, and their names
are the names their authors gave them.  Being in a build target means the kernel
accepts the file, and means nothing else.

The archives these files came from have been deleted.  What is retained is the
source-of-claim provenance (which lane the module belongs to), not the transport
provenance (tar hashes, blob shards, archive member paths).
-/
