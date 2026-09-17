import Mathlib
import AgdaMirror.AdK.Attribution

/-!
# Exact atomistic carrier for the AdK Lean mirror

PDB-style decimal coordinates and the adopted rounded atomic masses are embedded
into `ℚ` exactly.  This is a DASHI reconstruction choice that gives the theorem
spine an exact carrier; it is **not** a claim that the experimental coordinates,
standard atomic weights, isotope masses, or force-field masses are intrinsically
exact rationals.
-/

namespace AgdaMirror.AdK.AtomisticConfiguration

structure Vec3Q where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

structure AtomId where
  model : Nat
  chain : String
  residue : Int
  residueName : String
  atomName : String
  altloc : String
  serial : Nat
  element : String
  deriving DecidableEq, Repr

structure Atom where
  id : AtomId
  mass : ℚ
  position : Vec3Q
  deriving DecidableEq, Repr

abbrev Configuration := List Atom

/-- Exact embedding of a decimal integer numerator over `1000`. -/
def milli (n : Int) : ℚ := n / 1000

/-- Adopted rounded working masses, attributed to the Prohaska et al. convention
coordinate retained in `Attribution`.  They are not isotope-exact masses. -/
def massH : ℚ := 1008 / 1000
def massC : ℚ := 12011 / 1000
def massN : ℚ := 14007 / 1000
def massO : ℚ := 15999 / 1000
def massP : ℚ := 30974 / 1000
def massS : ℚ := 32060 / 1000
def massMg : ℚ := 24305 / 1000

/-- Exact coordinate constructor for PDB decimal-thousandths. -/
def pdbMilliVec (x y z : Int) : Vec3Q :=
  { x := milli x, y := milli y, z := milli z }

example : milli 12345 = (12345 : ℚ) / 1000 := rfl
example : massC = (12011 : ℚ) / 1000 := rfl
example : pdbMilliVec 1000 0 (-1000) =
    { x := 1, y := 0, z := -1 } := by
  norm_num [pdbMilliVec, milli]

end AgdaMirror.AdK.AtomisticConfiguration
