import Integration.E6Mod3QuadraticBridge
import Integration.E6PGSp4ExteriorSquare
import Integration.E6F3ProjectiveAssociation
import Mathlib

/-!
# Literal E6 projective root lines and the 36-state Q=2 association graph

The repository already owns a concrete 72-root E6 carrier and a bijection to
the Q=2 shell.  This file performs the antipodal projectivization explicitly:
choose the canonical first-nonzero-equals-1 representative after mod-3
standardization.  The resulting 36 root lines are equivalent to the existing
36 projective Q=2 points, and Cartan orthogonality matches the Q=2 graph.
-/

namespace Integration.E6ProjectiveRootAssociation

open Integration.E6Mod3QuadraticBridge
open Integration.E6PGSp4ExteriorSquare
open Integration.E6F3ExteriorSquare
open Integration.E6F3ProjectiveAssociation

/-- Standard five-dimensional mod-3 coordinate of a literal bounded E6 root. -/
def rootStandard (r : E6Root) : V5 :=
  fromE6Five (quotientToStandard (e6QuotientCoordinates r))

theorem root_standard_qtwo : ∀ r : E6Root, qStandard (rootStandard r) = 2 := by
  native_decide

/-- One representative from each antipodal E6 root pair. -/
def E6ProjectiveRoot :=
  {r : E6Root // canonicalProjective (rootStandard r) = true}

instance : Fintype E6ProjectiveRoot := inferInstance

theorem e6ProjectiveRoot_card : Fintype.card E6ProjectiveRoot = 36 := by
  native_decide

/-- Concrete map to the projective Q=2 carrier. -/
def projectiveRootToQ2Line (r : E6ProjectiveRoot) : Q2Line :=
  ⟨rootStandard r.1, root_standard_qtwo r.1, r.2⟩

theorem projective_root_to_q2_injective :
    Function.Injective projectiveRootToQ2Line := by
  native_decide

theorem projective_root_to_q2_surjective :
    Function.Surjective projectiveRootToQ2Line := by
  native_decide

def e6ProjectiveRootEquivQ2Line : E6ProjectiveRoot ≃ Q2Line :=
  Equiv.ofBijective projectiveRootToQ2Line
    ⟨projective_root_to_q2_injective, projective_root_to_q2_surjective⟩

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

/-- Root-line adjacency: distinct roots whose Cartan pairing vanishes modulo 3. -/
def rootLineAdjacent (r s : E6ProjectiveRoot) : Bool :=
  decide (r ≠ s ∧ intMod3 (e6Pair r.1 s.1) = 0)

/-- The root-system relation and the finite quadratic orthogonality graph agree. -/
theorem projective_root_adjacency_intertwining :
    ∀ r s : E6ProjectiveRoot,
      rootLineAdjacent r s =
        q2Adjacent (projectiveRootToQ2Line r) (projectiveRootToQ2Line s) := by
  native_decide

def rootLineDegree (r : E6ProjectiveRoot) : Nat :=
  (Finset.univ.filter fun s : E6ProjectiveRoot => rootLineAdjacent r s).card

def rootLineCommon (r s : E6ProjectiveRoot) : Nat :=
  (Finset.univ.filter fun t : E6ProjectiveRoot =>
    rootLineAdjacent r t && rootLineAdjacent s t).card

/-- Literal E6 projective root graph is SRG(36,15,6,6). -/
theorem root_line_degree_15 :
    ∀ r : E6ProjectiveRoot, rootLineDegree r = 15 := by
  native_decide

theorem root_line_adjacent_common_6 :
    ∀ r s : E6ProjectiveRoot,
      rootLineAdjacent r s = true → rootLineCommon r s = 6 := by
  native_decide

theorem root_line_nonadjacent_common_6 :
    ∀ r s : E6ProjectiveRoot,
      r ≠ s → rootLineAdjacent r s = false → rootLineCommon r s = 6 := by
  native_decide

structure Boundary where
  literalE6ProjectiveRootCount36Paid : Bool
  rootLineQ2EquivalencePaid : Bool
  cartanOrthogonalityIntertwiningPaid : Bool
  literalE6RootLineSRG361566Paid : Bool
  graphParametersAloneIdentifyUnrelatedRepresentation : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalE6ProjectiveRootCount36Paid := true
  rootLineQ2EquivalencePaid := true
  cartanOrthogonalityIntertwiningPaid := true
  literalE6RootLineSRG361566Paid := true
  graphParametersAloneIdentifyUnrelatedRepresentation := false

end Integration.E6ProjectiveRootAssociation
