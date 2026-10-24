import Synthesis.RiemannG21AtomicHyperbolicTP2
import Synthesis.RiemannImprovedZeroFreeG21UniformGap

/-!
# Improved-zero-free / G21 terminal max-cut

Branch-local status owner after the Liu/OpenAI donor recut and the new G21
hyperbolic proof candidates.

Paid/source-written on this branch:
* conservative exact rational target cap;
* conditional uniform G21 pole/off-line gap > 1/8;
* generic signed-hybrid fixed-point discrimination;
* `x*coth x` and `x*tanh x` positive-axis strict-monotonicity candidates;
* atomic strict sinh/cosh TP2 candidates.

Not paid by these constructions:
* exact import/re-proof of the external same-zeta theorem on this proof graph;
* actual taper-weighted continuum moment signs;
* direct six-term Taylor remainder < cubic determinant margin;
* finite-radius parity minors;
* nuisance-aware pole-quotient transversality;
* A1/A2/Route-B signed analytic producers;
* RH.

The booleans below are documentary; theorem authority comes only from imported
proof terms.  Since this exact head has not been kernel-checked in the current
authoring environment, all new theorem files remain SOURCE-WRITTEN / KERNEL-PENDING.
-/

namespace Synthesis

structure ImprovedZeroFreeG21TerminalMaxCut where
  externalZeroFreeSourcePinned : Bool
  exactExternalSameZetaTheoremImported : Bool
  safeRationalTargetCapPaid : Bool
  uniformPoleGapPaid : Bool
  uniformPoleGapExceedsOneEighth : Bool
  scaledCothMonotonicitySourceWritten : Bool
  scaledTanhMonotonicitySourceWritten : Bool
  atomicTP2SourceWritten : Bool
  exactHeadKernelChecked : Bool
  continuumMomentSignsPaid : Bool
  directRemainderBelowMarginPaid : Bool
  finiteRadiusParityMinorsPaid : Bool
  poleQuotientTransversalityPaid : Bool
  signedA1A2BProducerPaidByDonor : Bool
  riemannHypothesisDerived : Bool

def improvedZeroFreeG21TerminalMaxCut : ImprovedZeroFreeG21TerminalMaxCut where
  externalZeroFreeSourcePinned := true
  exactExternalSameZetaTheoremImported := false
  safeRationalTargetCapPaid := true
  uniformPoleGapPaid := true
  uniformPoleGapExceedsOneEighth := true
  scaledCothMonotonicitySourceWritten := true
  scaledTanhMonotonicitySourceWritten := true
  atomicTP2SourceWritten := true
  exactHeadKernelChecked := false
  continuumMomentSignsPaid := false
  directRemainderBelowMarginPaid := false
  finiteRadiusParityMinorsPaid := false
  poleQuotientTransversalityPaid := false
  signedA1A2BProducerPaidByDonor := false
  riemannHypothesisDerived := false

/-- The quantitative donor consequence that survives into the terminal recut. -/
theorem terminal_oneEighth_lt_uniformPoleGap :
    (1 : ℝ) / 8 < improvedZeroFreeUniformPoleGap :=
  oneEighth_lt_improvedZeroFreeUniformPoleGap

/-- Source-written pointwise odd TP2 theorem candidate exported by this branch. -/
theorem terminal_sinhTP2
    {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.sinh (p*v) * Real.sinh (a*u)
      > Real.sinh (p*u) * Real.sinh (a*v) :=
  sinhKernel_strictTP2 ha hap hu huv

/-- Source-written pointwise even TP2 theorem candidate exported by this branch. -/
theorem terminal_coshTP2
    {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.cosh (p*v) * Real.cosh (a*u)
      > Real.cosh (p*u) * Real.cosh (a*v) :=
  coshKernel_strictTP2 ha hap hu huv

end Synthesis
