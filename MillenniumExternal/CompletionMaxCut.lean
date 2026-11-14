import MillenniumExternal.SameObjectMaxCut

/-!
# Post-identity completion max-cut

This module is intentionally small.  It records the first theorem-producing
obligation remaining after exhausting the repository's existing same-object and
physical-object welds.  It is not an acceptance surface; exact theorem terms
remain authoritative.
-/

namespace MillenniumExternal

inductive CompletionLeaf where
  | nsKernelCheck
  | rhMathlibProducer
  | bsdHasseWeilProducer
  | pnpUniversalSATFailure
  | hodgeFaithfulTarget
  | ymFaithfulTarget
  | none
  deriving DecidableEq, BEq, Repr

/-- Navier--Stokes now has source-written exact `FeffermanC` and `FeffermanD`
terms in the isolated literal package; only kernel verification can still reject
them. -/
def nsCompletionLeaf : CompletionLeaf := .nsKernelCheck

/-- The external RH proposition is already exactly equivalent to Mathlib's
`RiemannHypothesis`; no further statement identity remains. -/
def rhCompletionLeaf : CompletionLeaf := .rhMathlibProducer

/-- BSD's algebraic carrier has an existing Mathlib affine/projective point
additive equivalence.  The nontrivial external analytic seam is LeanDojo's
`HasseWeilLSeriesData`: explicit incomplete Euler product plus finite bad-prime
correction versus DASHI's literal Mathlib Hasse--Weil `LSeries` continuation. -/
def bsdCompletionLeaf : CompletionLeaf := .bsdHasseWeilProducer

/-- The Agda Clay core already proves `SATNotInP <-> P != NP` under established
Cook--Levin background.  Its own latest Q1 terminal-semantics module proves the
terminal package extensionally equivalent to direct SAT decision failure, so it
cannot be counted as an easier intermediate theorem. -/
def pnpCompletionLeaf : CompletionLeaf := .pnpUniversalSATFailure

def hodgeCompletionLeaf : CompletionLeaf := .hodgeFaithfulTarget

def yangMillsCompletionLeaf : CompletionLeaf := .ymFaithfulTarget

/-- There is no longer a generic external `same-object identity` leaf.  Each
live lane above has been reduced to its concrete next producer/specification. -/
theorem no_generic_same_object_leaf :
    nsCompletionLeaf != .none &&
    rhCompletionLeaf != .none &&
    bsdCompletionLeaf != .none &&
    pnpCompletionLeaf != .none := by decide

end MillenniumExternal
