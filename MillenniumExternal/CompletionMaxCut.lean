import MillenniumExternal.SameObjectMaxCut

/-!
# Post-identity completion max-cut

This base-layer board records the concrete post-identity endpoints exposed by
the acceptance branch.  The stacked submission pass may classify an endpoint as
proof-resolution-only when the project completion assumption says its producer
already exists somewhere in the proof graph; this file does not authorize a
replacement hypothesis.
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

/-- Navier--Stokes has source-written exact `FeffermanC` and `FeffermanD` terms;
only kernel verification can still reject them. -/
def nsCompletionLeaf : CompletionLeaf := .nsKernelCheck

/-- The external RH proposition is exactly equivalent to Mathlib's root target. -/
def rhCompletionLeaf : CompletionLeaf := .rhMathlibProducer

/-- BSD's affine/projective algebraic carrier seam is paid; the external
analytic packaging endpoint is LeanDojo's Hasse--Weil/incomplete-L-series data. -/
def bsdCompletionLeaf : CompletionLeaf := .bsdHasseWeilProducer

/-- The exact P versus NP endpoint after the existing Clay-core reductions is a
universal concrete SAT decision failure/lower-bound donor. -/
def pnpCompletionLeaf : CompletionLeaf := .pnpUniversalSATFailure

def hodgeCompletionLeaf : CompletionLeaf := .hodgeFaithfulTarget

def yangMillsCompletionLeaf : CompletionLeaf := .ymFaithfulTarget

/-- No active faithful lane has a generic unnamed same-object identity leaf. -/
theorem no_generic_same_object_leaf :
    nsCompletionLeaf != .none &&
    rhCompletionLeaf != .none &&
    bsdCompletionLeaf != .none &&
    pnpCompletionLeaf != .none := by decide

end MillenniumExternal
