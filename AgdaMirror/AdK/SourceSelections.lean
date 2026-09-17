import Mathlib
import AgdaMirror.AdK.AtomisticConfiguration

/-!
# Source-facing AdK CV selections

Li-Liu-Ji 2015 (DOI `10.1016/j.bpj.2015.06.059`) pays the residue/domain
roles mirrored here.  In particular, the theta1/theta2 construction explicitly
uses backbone centers of mass.

For `dLN`, the source pays the LID/NMP domain residue ranges but the exact atom
subset is underresolved in the available source text.  Therefore `dlnLid` and
`dlnNmp` require an explicit `AtomPolicy`; choosing `.backbone` or `.heavy` is a
DASHI evaluator convention and is never promoted into source authority.

`OXT` is included in the current DASHI backbone evaluator convention.  That
inclusion is not attributed to Li-Liu-Ji as an explicit atom-name statement.
-/

namespace AgdaMirror.AdK.SourceSelections

open AgdaMirror.AdK.AtomisticConfiguration

inductive AtomPolicy
  | backbone
  | heavy
  deriving DecidableEq, Repr

structure ResidueSpan where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

structure SelectionSpec where
  label : String
  spans : List ResidueSpan
  policy : AtomPolicy
  deriving DecidableEq, Repr

namespace ResidueSpan

def contains (span : ResidueSpan) (residue : Int) : Bool :=
  decide (span.lo ≤ residue ∧ residue ≤ span.hi)

end ResidueSpan

def backboneNames : List String := ["N", "CA", "C", "O", "OXT"]

def inAnySpan (spans : List ResidueSpan) (residue : Int) : Bool :=
  spans.any fun span => span.contains residue

def atomPolicyAccepts : AtomPolicy → Atom → Bool
  | .backbone, atom => backboneNames.contains atom.id.atomName
  | .heavy, atom => decide (atom.id.element ≠ "H")

def selectionAccepts (selection : SelectionSpec) (atom : Atom) : Bool :=
  inAnySpan selection.spans atom.id.residue && atomPolicyAccepts selection.policy atom

def selectedAtoms (configuration : Configuration) (selection : SelectionSpec) : List Atom :=
  configuration.filter (selectionAccepts selection)

/-- theta1 first point: LID backbone residues 123–155. -/
def theta1Lid : SelectionSpec :=
  { label := "theta1_lid_backbone"
    spans := [{ lo := 123, hi := 155 }]
    policy := .backbone }

/-- Shared hinge backbone residues 161–165. -/
def hinge : SelectionSpec :=
  { label := "theta_hinge_backbone"
    spans := [{ lo := 161, hi := 165 }]
    policy := .backbone }

/-- Shared CORE backbone spans 1–8, 79–85, 104–110, 190–198. -/
def core : SelectionSpec :=
  { label := "theta_core_backbone"
    spans :=
      [ { lo := 1, hi := 8 }
      , { lo := 79, hi := 85 }
      , { lo := 104, hi := 110 }
      , { lo := 190, hi := 198 } ]
    policy := .backbone }

/-- theta2 first point: NMP backbone residues 50–59. -/
def theta2Nmp : SelectionSpec :=
  { label := "theta2_nmp_backbone"
    spans := [{ lo := 50, hi := 59 }]
    policy := .backbone }

/-- dLN LID domain residues 122–159 with explicit evaluator atom policy. -/
def dlnLid (policy : AtomPolicy) : SelectionSpec :=
  { label := match policy with
      | .backbone => "dln_lid_backbone"
      | .heavy => "dln_lid_heavy"
    spans := [{ lo := 122, hi := 159 }]
    policy := policy }

/-- dLN NMP domain residues 30–59 with explicit evaluator atom policy. -/
def dlnNmp (policy : AtomPolicy) : SelectionSpec :=
  { label := match policy with
      | .backbone => "dln_nmp_backbone"
      | .heavy => "dln_nmp_heavy"
    spans := [{ lo := 30, hi := 59 }]
    policy := policy }

/-- Six unique selected-content objects feed the eight logical three-CV
positions because hinge/core are reused by both source angles. -/
def allThreeCVSelections (dlnPolicy : AtomPolicy) : List SelectionSpec :=
  [theta1Lid, hinge, core, theta2Nmp, dlnLid dlnPolicy, dlnNmp dlnPolicy]

/-- The source does not pay a unique dLN atom-policy choice in this mirror. -/
def dlnSourceAtomSubsetResolved : Bool := false

example : theta1Lid.spans = [{ lo := 123, hi := 155 }] := rfl
example : dlnSourceAtomSubsetResolved = false := rfl
example : dlnLid .backbone ≠ dlnLid .heavy := by decide

end AgdaMirror.AdK.SourceSelections
