import Mathlib
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

/-!
# p=2, N=4 non-squarefree Gamma_0 moduli boundary

External source:
K. Cesnavicius, "A modular description of X_0(n)", arXiv:1511.07475.

For nonsquarefree n, the naive compactified moduli stack of generalized
elliptic curves with an ample cyclic subgroup of order n does not agree at
the cusps with the Deligne--Rapoport Gamma_0(n) stack.  A refined moduli
problem is required.

Thus the finite-flat subgroup socket remains a valid interior interface, but
must not be promoted to the full compactified X_0(4) stack by naming.
-/

namespace Integration.OggSSPP2Gamma0FourRefinedModuliBoundary

open Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

inductive Gamma0FourModuliScope
  | interiorEllipticFiniteFlatSubgroup
  | naiveCompactifiedAmpleCyclicSubgroup
  | refinedDeligneRapoportCompactification
  deriving DecidableEq, Repr

structure RefinedGamma0FourCompactifiedSource where
  interiorDatum : Gamma0FourFiniteFlatDatum
  CompactifiedState : Type
  scope : Gamma0FourModuliScope
  scopeIsRefined :
    scope = .refinedDeligneRapoportCompactification
  cuspRefinementConstructed : Prop

inductive ClaimOrigin
  | externalSourceContext
  | repositoryNewExtension
  deriving DecidableEq, Repr

structure Boundary where
  levelFourRecognizedAsNonsquarefree : Bool
  interiorFiniteFlatSubgroupSocketRetained : Bool
  naiveCompactifiedCyclicSubgroupPromotedToFullX0Four : Bool
  refinedCompactificationRequiredAtCusps : Bool
  arithmeticInteriorSourceConstructed : Bool
  refinedCompactifiedSourceConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  levelFourRecognizedAsNonsquarefree := true
  interiorFiniteFlatSubgroupSocketRetained := true
  naiveCompactifiedCyclicSubgroupPromotedToFullX0Four := false
  refinedCompactificationRequiredAtCusps := true
  arithmeticInteriorSourceConstructed := false
  refinedCompactifiedSourceConstructed := false

end Integration.OggSSPP2Gamma0FourRefinedModuliBoundary
