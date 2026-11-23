import Integration.E6Mod3QuadraticBridge
import Integration.E6ProjectiveRootLineSRG
import Mathlib

/-!
# Literal E6 roots -> projective Q=2 root-line graph

`E6Mod3QuadraticBridge` already gives a concrete 72-root E6 carrier and a
same-object reduction to the 72-point Q=2 shell.  `E6ProjectiveRootLineSRG`
separately owns the 36 antipodal projective Q=2 lines and their
SRG(36,15,6,6) graph.

This owner closes the remaining same-object seam: projectivize the *literal
repo E6 roots themselves* using the same standard mod-3 coordinate and prove a
bijection to the 36 Q=2 root lines.  It also checks that the Cartan pairing
modulo 3 is exactly the standard five-dimensional dot pairing, so the literal
E6 root-line graph is the same graph, not merely a cardinality match.
-/

namespace DASHI.Integration.E6RootLineSameObject

open Integration.E6Mod3QuadraticBridge
open DASHI.Integration.E6ProjectiveRootLineSRG

/-- Standard five-dimensional mod-3 coordinate of a literal bounded E6 root. -/
def rootStandard (r : E6Root) : F3Five :=
  quotientToStandard (e6QuotientCoordinates r)

/-- Every literal E6 root lands on the norm-two shell in the standardized
five-dimensional quotient. -/
theorem rootStandard_qtwo :
    ∀ r : E6Root, standardQuadratic (rootStandard r) = 2 := by
  native_decide

/-- Canonical representative from each antipodal pair of literal E6 roots. -/
def E6RootLine :=
  {r : E6Root // canonicalLineRep (rootStandard r)}

instance : Fintype E6RootLine := Fintype.ofFinite _
instance : DecidableEq E6RootLine := inferInstance

theorem e6RootLine_card : Fintype.card E6RootLine = 36 := by
  native_decide

/-- Concrete projectivized same-object map. -/
def rootLineToQTwo (r : E6RootLine) : QTwoRootLine :=
  ⟨rootStandard r.1, rootStandard_qtwo r.1, r.2⟩

theorem rootLineToQTwo_injective : Function.Injective rootLineToQTwo := by
  native_decide

theorem rootLineToQTwo_surjective : Function.Surjective rootLineToQTwo := by
  native_decide

/-- Literal projective E6 roots are exactly the existing projective Q=2 carrier. -/
def e6RootLineEquivQTwo : E6RootLine ≃ QTwoRootLine :=
  Equiv.ofBijective rootLineToQTwo
    ⟨rootLineToQTwo_injective, rootLineToQTwo_surjective⟩

/-- Integral E6 Cartan pairing in the chosen simple-root coefficient basis. -/
def e6Pair (r s : E6Root) : Int :=
  let x := r.1
  let y := s.1
  2 * (c0 x*c0 y + c1 x*c1 y + c2 x*c2 y +
       c3 x*c3 y + c4 x*c4 y + c5 x*c5 y) -
      (c0 x*c2 y + c2 x*c0 y +
       c1 x*c3 y + c3 x*c1 y +
       c2 x*c3 y + c3 x*c2 y +
       c3 x*c4 y + c4 x*c3 y +
       c4 x*c5 y + c5 x*c4 y)

/-- The Cartan pairing, reduced modulo 3 and quotient-standardized, is exactly
the five-dimensional dot form used by the root-line graph. -/
theorem e6Pair_mod3_eq_dot5 :
    ∀ r s : E6Root,
      intMod3 (e6Pair r s) = dot5 (rootStandard r) (rootStandard s) := by
  native_decide

/-- Literal E6 root-line adjacency before transport. -/
def rootAdjacent (r s : E6RootLine) : Prop :=
  r ≠ s ∧ intMod3 (e6Pair r.1 s.1) = 0

/-- The literal Cartan graph and standardized Q=2 orthogonality graph agree. -/
theorem rootAdjacent_iff_qtwoAdjacent :
    ∀ r s : E6RootLine,
      rootAdjacent r s ↔
        (rootLineToQTwo s ∈ neighbors (rootLineToQTwo r)) := by
  native_decide

def rootNeighbors (r : E6RootLine) : Finset E6RootLine :=
  Finset.univ.filter (rootAdjacent r)

def rootCommonNeighbors (r s : E6RootLine) : Finset E6RootLine :=
  Finset.univ.filter fun t => rootAdjacent r t ∧ rootAdjacent s t

/-- Therefore the actual repo E6 projective root graph is SRG(36,15,6,6). -/
theorem e6RootLine_degree15 :
    ∀ r : E6RootLine, (rootNeighbors r).card = 15 := by
  native_decide

theorem e6RootLine_common6 :
    ∀ r s : E6RootLine, r ≠ s → (rootCommonNeighbors r s).card = 6 := by
  native_decide

structure SameObjectBoundary where
  literalE6RootProjectivizationTyped : Bool
  literalE6RootLineCount36Paid : Bool
  literalRootLineQTwoEquivalencePaid : Bool
  cartanDotIntertwiningPaid : Bool
  literalE6RootLineSRG361566Paid : Bool
  cardinalityAlonePromotesSameObject : Bool
  deriving Repr

def sameObjectBoundary : SameObjectBoundary where
  literalE6RootProjectivizationTyped := true
  literalE6RootLineCount36Paid := true
  literalRootLineQTwoEquivalencePaid := true
  cartanDotIntertwiningPaid := true
  literalE6RootLineSRG361566Paid := true
  cardinalityAlonePromotesSameObject := false

end DASHI.Integration.E6RootLineSameObject
