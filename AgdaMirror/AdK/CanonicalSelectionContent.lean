import Mathlib
import AgdaMirror.AdK.SourceSelections

/-!
# Transparent canonical selected content

The proof-relevant selected-content carrier is a `Multiset CanonicalAtomRow`.
Lean's `Multiset` is the quotient of lists by permutation, so source-file/list
serialization order is removed while multiplicity is preserved.  This is more
faithful than hashing and avoids assuming cryptographic injectivity.

A canonical row contains exactly the atom identity, the adopted exact-rational
working mass, and exact-rational position used by the COM theorem.  Hashes and
PDB byte identity remain outside this equality.
-/

namespace AgdaMirror.AdK.CanonicalSelectionContent

open AgdaMirror.AdK.AtomisticConfiguration
open AgdaMirror.AdK.SourceSelections

structure CanonicalAtomRow where
  id : AtomId
  mass : ℚ
  position : Vec3Q
  deriving DecidableEq, Repr

abbrev CanonicalSelectionContent := Multiset CanonicalAtomRow

def canonicalRow (atom : Atom) : CanonicalAtomRow :=
  { id := atom.id, mass := atom.mass, position := atom.position }

/-- Order-insensitive, multiplicity-preserving selected content. -/
def canonicalContent
    (configuration : Configuration)
    (selection : SelectionSpec) : CanonicalSelectionContent :=
  Multiset.ofList ((selectedAtoms configuration selection).map canonicalRow)

/-- A permutation of the selected transparent rows creates exactly the same
canonical selected content.  This uses Lean's quotient equality, not a hash. -/
theorem canonicalContent_eq_of_selectedRows_perm
    {q₁ q₂ : Configuration}
    {selection : SelectionSpec}
    (h :
      ((selectedAtoms q₁ selection).map canonicalRow).Perm
        ((selectedAtoms q₂ selection).map canonicalRow)) :
    canonicalContent q₁ selection = canonicalContent q₂ selection := by
  simpa [canonicalContent] using (Multiset.coe_eq_coe.mpr h)

/-- Hash equality is deliberately absent from the proof carrier. -/
def hashEqualityCreatesCanonicalContentEquality : Bool := false

/-- PDB/deposition identity is deliberately absent from the proof carrier. -/
def pdbIdentityCreatesCanonicalContentEquality : Bool := false

example : hashEqualityCreatesCanonicalContentEquality = false := rfl
example : pdbIdentityCreatesCanonicalContentEquality = false := rfl

end AgdaMirror.AdK.CanonicalSelectionContent
